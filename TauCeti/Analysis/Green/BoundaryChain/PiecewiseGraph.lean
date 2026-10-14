/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Analysis.Green.BoundaryChain.Graph
import TauCeti.Analysis.Calculus.Deriv.CountableLevels
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Piecewise

/-!
# Finite graph-piece boundary arcs

A geometric certificate permits finitely many coordinate graph pieces, joined as actual paths.
Continuous coordinate primitives prove gauge integrability and additivity even when the graph
speed is unbounded and the coordinate integrand is only conditionally integrable.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace TauCeti.Green.BoundaryChain

/-- A finite graph-piece presentation of an actual path, including ignored constant-coordinate
pieces. These certificates contain no integral identities or field assumptions. -/
inductive PiecewiseGraphArc (d : Coordinate) (U : Set ℂ) : Arc → Prop
  | constant {p q : ℂ} (γ : Path p q) (hγ : ∀ t, d.proj (γ t) = d.proj p) :
      PiecewiseGraphArc d U ⟨p, q, γ⟩
  | graph {g : ℝ → ℝ} {a b : ℝ} {γ : Arc} (hγ : GraphArc d g a b γ)
      (hU : d.graph g '' Icc a b ⊆ U) : PiecewiseGraphArc d U γ
  | trans {p q r : ℂ} {γ : Path p q} {δ : Path q r}
      (hγ : PiecewiseGraphArc d U ⟨p, q, γ⟩) (hδ : PiecewiseGraphArc d U ⟨q, r, δ⟩) :
      PiecewiseGraphArc d U ⟨p, r, γ.trans δ⟩
  | symm {p q : ℂ} {γ : Path p q} (hγ : PiecewiseGraphArc d U ⟨p, q, γ⟩) :
      PiecewiseGraphArc d U ⟨q, p, γ.symm⟩
  | reparam {p q : ℂ} {γ δ : Path p q} (hδ : PiecewiseGraphArc d U ⟨p, q, δ⟩)
      (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 1))
      (hdθ : ∃ s : Set ℝ, s.Countable ∧ ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ θ t)
      (hdδ : ∃ s : Set ℝ, s.Countable ∧
        ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ δ.extend t)
      (hfib : ∀ t : ℝ, (θ ⁻¹' {t}).Countable) (hmap : MapsTo θ (Icc 0 1) (Icc 0 1))
      (h0 : θ 0 = 0) (h1 : θ 1 = 1) (he : ∀ t : unitInterval, γ t = δ.extend (θ t)) :
      PiecewiseGraphArc d U ⟨p, q, γ⟩

private def CoordinatePrimitive (d : Coordinate) (P : ℂ → ℝ) (γ : Arc) (F : ℝ → ℝ) : Prop :=
  Continuous F ∧ F 0 = 0 ∧ ∃ s : Set ℝ, s.Countable ∧
    ∀ t ∈ Ioo 0 1 \ s, HasDerivAt F (P (γ.2.2.extend t) * d.proj (deriv γ.2.2.extend t)) t

private theorem GraphArc.coordinatePrimitive {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ}
    {γ : Arc} (h : GraphArc d g a b γ) {P : ℂ → ℝ}
    (hP : ContinuousOn P (d.graph g '' Icc a b)) : ∃ F, CoordinatePrimitive d P γ F := by
  let θ : ℝ → ℝ := fun t ↦ d.proj (γ.2.2.extend t)
  have hθ : Continuous θ := by fun_prop
  have hmap : MapsTo θ (Icc 0 1) (Icc a b) := fun t ht ↦ by
    simpa only [θ, Path.extend_apply _ ht] using h.coordinate_mem ⟨t, ht⟩
  have hab : a ≤ b := (hmap (left_mem_Icc.mpr zero_le_one)).1.trans
    (hmap (left_mem_Icc.mpr zero_le_one)).2
  let f : ℝ → ℝ := fun x ↦ P (d.graph g (projIcc a b hab x))
  have hf : Continuous f :=
    (hP.comp (d.continuousOn_graph h.continuous_graph) (mapsTo_image _ _)).domRestrict.comp
      continuous_projIcc
  let A : ℝ → ℝ := fun x ↦ ∫ y in a..x, f y
  have hA : Continuous A := (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hdA (x : ℝ) : HasDerivAt A (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a x)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  obtain ⟨s, hs, hdθ⟩ := h.differentiable_coordinate
  obtain ⟨S, hS, hdg⟩ := h.differentiable_graph
  let T := S ∪ {a, b}
  have hT : T.Countable := hS.union (toFinite _).countable
  refine ⟨fun t ↦ A (θ t) - A (θ 0), (hA.comp hθ).sub continuous_const,
    sub_self _, s ∪ {t | θ t ∈ T ∧ deriv θ t ≠ 0}, hs.union
      (TauCeti.countable_setOf_mem_and_deriv_ne_zero θ hT), ?_⟩
  intro t ht
  have hdt := hdθ t ⟨ht.1, fun hm ↦ ht.2 (Or.inl hm)⟩
  have hp : d.proj (deriv γ.2.2.extend t) = deriv θ t := by
    by_cases hd : DifferentiableAt ℝ γ.2.2.extend t
    · exact (d.proj.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv.symm
    · have hm : θ t ∈ T := by
        by_contra hm
        have hb := hmap (Ioo_subset_Icc_self ht.1)
        have he : γ.2.2.extend = d.graph g ∘ θ := funext h.extend_eq
        apply hd
        rw [he]
        have hi : θ t ∈ Ioo a b := by
          rw [← Icc_sdiff_both]
          exact ⟨hb, fun h ↦ hm (Or.inr h)⟩
        exact (d.differentiableAt_graph (hdg (θ t)
          ⟨hi, fun h ↦ hm (Or.inl h)⟩)).comp t hdt
      have hz : deriv θ t = 0 := by
        by_contra hz
        exact ht.2 (Or.inr ⟨hm, hz⟩)
      rw [deriv_zero_of_not_differentiableAt hd, map_zero, hz]
  have he : f (θ t) = P (γ.2.2.extend t) := by
    dsimp only [f]
    rw [projIcc_of_mem hab (hmap (Ioo_subset_Icc_self ht.1)), ← h.extend_eq]
  simpa only [he, hdt.hasDerivAt.deriv, hp, smul_eq_mul, mul_comm, Function.comp_apply] using
    ((hdA (θ t)).scomp t hdt.hasDerivAt).sub_const (A (θ 0))

private theorem CoordinatePrimitive.trans {d : Coordinate} {P : ℂ → ℝ}
    {p q r : ℂ} {γ : Path p q} {δ : Path q r} {F G : ℝ → ℝ}
    (hF : CoordinatePrimitive d P ⟨p, q, γ⟩ F)
    (hG : CoordinatePrimitive d P ⟨q, r, δ⟩ G) :
    CoordinatePrimitive d P ⟨p, r, γ.trans δ⟩
      (fun t ↦ if t ≤ 1 / 2 then F (2 * t) else F 1 + G (2 * t - 1)) := by
  obtain ⟨hcF, hF0, s, hs, hdF⟩ := hF
  obtain ⟨hcG, hG0, u, hu, hdG⟩ := hG
  refine ⟨Continuous.if ?_ (hcF.comp (by fun_prop))
    (continuous_const.add (hcG.comp (by fun_prop))), ?_,
    (fun t : ℝ ↦ t / 2) '' s ∪ (fun t : ℝ ↦ (t + 1) / 2) '' u ∪ {1 / 2},
    ((hs.image _).union (hu.image _)).union (countable_singleton _), ?_⟩
  · intro t ht
    have ht' : t = 1 / 2 := by simpa only [show {t : ℝ | t ≤ 1 / 2} = Iic (1 / 2) from rfl,
      frontier_Iic, mem_singleton_iff] using ht
    subst t
    norm_num [hG0]
  · norm_num [hF0]
  · intro t ht
    have hn : t ≠ 1 / 2 := fun he ↦ ht.2 (Or.inr (by simp [he]))
    by_cases hlt : t < 1 / 2
    · have hts : 2 * t ∉ s := fun hm ↦ ht.2 (Or.inl (Or.inl
        ⟨2 * t, hm, by ring⟩))
      have he : (γ.trans δ).extend =ᶠ[𝓝 t] fun x ↦ γ.extend (2 * x) := by
        filter_upwards [Iic_mem_nhds hlt] with x hx
        exact γ.extend_trans_of_le_half δ hx
      have hf : (fun x ↦ if x ≤ 1 / 2 then F (2 * x) else F 1 + G (2 * x - 1)) =ᶠ[𝓝 t]
          fun x ↦ F (2 * x) := by
        filter_upwards [Iic_mem_nhds hlt] with x hx using ite_eq_left hx
      have hd := ((hdF (2 * t) ⟨⟨by linarith [ht.1.1], by linarith⟩, hts⟩).comp t
        ((hasDerivAt_id t).const_mul 2)).congr_of_eventuallyEq hf
      rw [he.deriv_eq, deriv_comp_mul_left]
      simp only [he.self_of_nhds, map_smul, smul_eq_mul]
      convert hd using 1; simp only [mul_one]; ring
    · have hgt : 1 / 2 < t := lt_of_le_of_ne (le_of_not_gt hlt) hn.symm
      have htu : 2 * t - 1 ∉ u := fun hm ↦ ht.2 (Or.inl (Or.inr
        ⟨2 * t - 1, hm, by ring⟩))
      have he : (γ.trans δ).extend =ᶠ[𝓝 t] fun x ↦ δ.extend (2 * x - 1) := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx
        exact γ.extend_trans_of_half_le δ hx.le
      have hf : (fun x ↦ if x ≤ 1 / 2 then F (2 * x) else F 1 + G (2 * x - 1)) =ᶠ[𝓝 t]
          fun x ↦ F 1 + G (2 * x - 1) := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx using ite_eq_right (not_le.mpr hx)
      have hd := (((hdG (2 * t - 1) ⟨⟨by linarith, by linarith [ht.1.2]⟩, htu⟩).comp t
        (((hasDerivAt_id t).const_mul 2).sub_const 1)).const_add (F 1)).congr_of_eventuallyEq hf
      have hder : deriv (fun x ↦ δ.extend (2 * x - 1)) t =
          (2 : ℝ) • deriv δ.extend (2 * t - 1) := by
        have hh := deriv_comp_mul_left 2 (fun x ↦ δ.extend (x - 1)) t
        simpa only [deriv_comp_sub_const] using hh
      rw [he.deriv_eq, hder]
      simp only [he.self_of_nhds, map_smul, smul_eq_mul]
      convert hd using 1; simp only [mul_one]; ring

private theorem CoordinatePrimitive.symm {d : Coordinate} {P : ℂ → ℝ} {p q : ℂ}
    {γ : Path p q} {F : ℝ → ℝ} (hF : CoordinatePrimitive d P ⟨p, q, γ⟩ F) :
    CoordinatePrimitive d P ⟨q, p, γ.symm⟩ (fun t ↦ F (1 - t) - F 1) := by
  obtain ⟨hcF, hF0, s, hs, hdF⟩ := hF
  refine ⟨(hcF.comp (by fun_prop)).sub continuous_const, by simp,
    (fun t : ℝ ↦ 1 - t) '' s, hs.image _, ?_⟩
  intro t ht
  have hts : 1 - t ∉ s := fun hm ↦ ht.2 ⟨1 - t, hm, by ring⟩
  have hd := ((hdF (1 - t) ⟨⟨by linarith [ht.1.2], by linarith [ht.1.1]⟩, hts⟩).comp t
    ((hasDerivAt_id t).const_sub 1)).sub_const (F 1)
  have he : γ.symm.extend = fun x ↦ γ.extend (1 - x) := funext γ.extend_symm_apply
  rw [he, deriv_comp_const_sub]
  simpa only [map_neg, mul_neg, mul_neg_one, mul_one, Function.comp_apply] using hd

private theorem CoordinatePrimitive.reparam {d : Coordinate} {P : ℂ → ℝ}
    {p q : ℂ} {γ δ : Path p q} {F : ℝ → ℝ}
    (hF : CoordinatePrimitive d P ⟨p, q, δ⟩ F)
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc 0 1))
    (hdθ : ∃ s : Set ℝ, s.Countable ∧ ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ θ t)
    (hdδ : ∃ s : Set ℝ, s.Countable ∧
      ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ δ.extend t)
    (hfib : ∀ t : ℝ, (θ ⁻¹' {t}).Countable) (hmap : MapsTo θ (Icc 0 1) (Icc 0 1))
    (h0 : θ 0 = 0) (he : ∀ t : unitInterval, γ t = δ.extend (θ t)) :
    ∃ G, CoordinatePrimitive d P ⟨p, q, γ⟩ G ∧ G 1 = F (θ 1) := by
  obtain ⟨hcF, hF0, s, hs, hdF⟩ := hF
  obtain ⟨u, hu, hdu⟩ := hdθ
  obtain ⟨v, hv, hdv⟩ := hdδ
  let T := s ∪ v ∪ {0, 1}
  have hT : T.Countable := (hs.union hv).union (toFinite _).countable
  have hpre : (θ ⁻¹' T).Countable := by
    have hb := hT.biUnion (fun t _ ↦ hfib t)
    apply hb.mono
    intro t ht
    exact mem_iUnion₂.mpr ⟨θ t, ht, by simp⟩
  let Φ := IccExtend zero_le_one ((Icc 0 1).domRestrict θ)
  have hΦ : Continuous Φ := hθ.domRestrict.Icc_extend'
  have heΦ (t : ℝ) (ht : t ∈ Icc 0 1) : Φ t = θ t := IccExtend_of_mem _ _ ht
  refine ⟨F ∘ Φ, ?_, ?_⟩
  · refine ⟨?_, ?_, u ∪ θ ⁻¹' T, hu.union hpre, ?_⟩
    · exact hcF.comp hΦ
    · rw [Function.comp_apply, heΦ 0 ⟨le_rfl, zero_le_one⟩, h0, hF0]
    · intro t ht
      have hdt := hdu t ⟨ht.1, fun h ↦ ht.2 (Or.inl h)⟩
      have hav : θ t ∉ T := fun h ↦ ht.2 (Or.inr h)
      have hm := hmap (Ioo_subset_Icc_self ht.1)
      have hmt : θ t ∈ Ioo 0 1 := by
        rw [← Icc_sdiff_both]
        exact ⟨hm, fun h ↦ hav (Or.inr h)⟩
      have hdcur := hdv (θ t) ⟨hmt, fun h ↦ hav (Or.inl (Or.inr h))⟩
      have hdp := hdF (θ t) ⟨hmt, fun h ↦ hav (Or.inl (Or.inl h))⟩
      have heγ : γ.extend =ᶠ[𝓝 t] δ.extend ∘ θ := by
        filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with x hx
        rw [Path.extend_apply _ hx]
        exact he ⟨x, hx⟩
      have heF : F ∘ Φ =ᶠ[𝓝 t] F ∘ θ := by
        filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with x hx
        exact congrArg F (heΦ x hx)
      have hdγ := (hdcur.hasDerivAt.scomp t hdt.hasDerivAt).congr_of_eventuallyEq heγ
      have hp := (hdp.comp t hdt.hasDerivAt).congr_of_eventuallyEq heF
      rw [hdγ.deriv]
      simp only [map_smul, smul_eq_mul, Function.comp_apply, heγ.self_of_nhds]
      convert hp using 1; ring
  · rw [Function.comp_apply, heΦ 1 ⟨zero_le_one, le_rfl⟩]

private theorem CoordinatePrimitive.hasIntegral {d : Coordinate} {P : ℂ → ℝ}
    {γ : Arc} {F : ℝ → ℝ} (h : CoordinatePrimitive d P γ F) :
    BoxIntegral.HasIntegral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ P (γ.2.2.extend (t 0)) * d.proj (deriv γ.2.2.extend (t 0)))
      BoxIntegral.BoxAdditiveMap.volume (F 1) := by
  obtain ⟨hc, h0, s, hs, hd⟩ := h
  simpa only [h0, sub_zero] using
    TauCeti.BoxIntegral.hasIntegral_Henstock_of_hasDerivAt_off_countable
      zero_lt_one hs hc.continuousOn hd

private theorem PiecewiseGraphArc.coordinatePrimitive {d : Coordinate} {U : Set ℂ}
    {γ : Arc} (h : PiecewiseGraphArc d U γ) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    ∃ F, CoordinatePrimitive d P γ F := by
  induction h with
  | @constant p q γ hγ =>
    refine ⟨fun _ ↦ 0, continuous_const, rfl, ∅, countable_empty, ?_⟩
    intro t _
    have hz : d.proj (deriv γ.extend t) = 0 :=
      d.proj.deriv_eq_zero_of_forall_eq (γ.forall_extend (P := fun z ↦ d.proj z = d.proj p) hγ) t
    simpa only [hz, mul_zero] using hasDerivAt_const t (0 : ℝ)
  | graph hγ hU => exact hγ.coordinatePrimitive (hP.mono hU)
  | trans hγ hδ ihγ ihδ =>
    obtain ⟨F, hF⟩ := ihγ
    obtain ⟨G, hG⟩ := ihδ
    exact ⟨_, hF.trans hG⟩
  | symm hγ ih =>
    obtain ⟨F, hF⟩ := ih
    exact ⟨_, hF.symm⟩
  | reparam hδ θ hθ hdθ hdδ hfib hmap h0 h1 he ih =>
    obtain ⟨F, hF⟩ := ih
    obtain ⟨G, hG, _⟩ := hF.reparam hθ hdθ hdδ hfib hmap h0 he
    exact ⟨G, hG⟩

/-- Every finite graph-piece path is genuinely Henstock integrable in its selected coordinate,
with no Bochner integrability or absolute-continuity premise. -/
theorem PiecewiseGraphArc.integrable {d : Coordinate} {U : Set ℂ} {γ : Arc}
    (h : PiecewiseGraphArc d U γ) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    Integrable d.proj P (ofPath γ.2.2) := by
  obtain ⟨F, hF⟩ := h.coordinatePrimitive hP
  exact (integrable_ofPath_iff _ _ _).mpr hF.hasIntegral.integrable

/-- The actual joined path integral is the sum of its finite graph-piece integrals. This
is gauge additivity, including conditional integrability and arbitrary graph backtracking. -/
theorem PiecewiseGraphArc.arcIntegral_trans {d : Coordinate} {U : Set ℂ} {p q r : ℂ}
    {γ : Path p q} {δ : Path q r} (hγ : PiecewiseGraphArc d U ⟨p, q, γ⟩)
    (hδ : PiecewiseGraphArc d U ⟨q, r, δ⟩) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    arcIntegral d.proj P ⟨p, r, γ.trans δ⟩ =
      arcIntegral d.proj P ⟨p, q, γ⟩ + arcIntegral d.proj P ⟨q, r, δ⟩ := by
  obtain ⟨F, hF⟩ := hγ.coordinatePrimitive hP
  obtain ⟨G, hG⟩ := hδ.coordinatePrimitive hP
  have hj := (hF.trans hG).hasIntegral.integral_eq
  have hf := hF.hasIntegral.integral_eq
  have hg := hG.hasIntegral.integral_eq
  simp only [show ¬(1 : ℝ) ≤ 1 / 2 by norm_num, ite_false,
    show 2 * (1 : ℝ) - 1 = 1 by norm_num] at hj
  rw [arcIntegral_def, arcIntegral_def, arcIntegral_def]
  exact hj.trans (congrArg₂ (· + ·) hf.symm hg.symm)

/-- A countable-fiber regular change of parameter preserves the gauge integral of a finite
piecewise graph path. Endpoint preservation fixes its orientation. -/
theorem PiecewiseGraphArc.arcIntegral_reparam {d : Coordinate} {U : Set ℂ} {p q : ℂ}
    {γ δ : Path p q} (hδ : PiecewiseGraphArc d U ⟨p, q, δ⟩)
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc 0 1))
    (hdθ : ∃ s : Set ℝ, s.Countable ∧ ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ θ t)
    (hdδ : ∃ s : Set ℝ, s.Countable ∧
      ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ δ.extend t)
    (hfib : ∀ t : ℝ, (θ ⁻¹' {t}).Countable) (hmap : MapsTo θ (Icc 0 1) (Icc 0 1))
    (h0 : θ 0 = 0) (h1 : θ 1 = 1) (he : ∀ t : unitInterval, γ t = δ.extend (θ t))
    {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    arcIntegral d.proj P ⟨p, q, γ⟩ = arcIntegral d.proj P ⟨p, q, δ⟩ := by
  obtain ⟨F, hF⟩ := hδ.coordinatePrimitive hP
  obtain ⟨G, hG, hG1⟩ := hF.reparam hθ hdθ hdδ hfib hmap h0 he
  rw [arcIntegral_def, arcIntegral_def, hG.hasIntegral.integral_eq,
    hF.hasIntegral.integral_eq, hG1, h1]

/-- Reversing an actual finite graph-piece path negates its gauge integral. -/
theorem PiecewiseGraphArc.arcIntegral_symm {d : Coordinate} {U : Set ℂ} {p q : ℂ}
    {γ : Path p q} (hγ : PiecewiseGraphArc d U ⟨p, q, γ⟩)
    {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    arcIntegral d.proj P ⟨q, p, γ.symm⟩ = -arcIntegral d.proj P ⟨p, q, γ⟩ := by
  obtain ⟨F, hF⟩ := hγ.coordinatePrimitive hP
  have hj := hF.symm.hasIntegral.integral_eq
  simp only [sub_self, hF.2.1, zero_sub] at hj
  rw [arcIntegral_def, arcIntegral_def, hj, hF.hasIntegral.integral_eq]

end TauCeti.Green.BoundaryChain
