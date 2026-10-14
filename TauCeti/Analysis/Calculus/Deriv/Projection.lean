/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.CountableLevels
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Derivatives of real projections

A constant projection has zero projected derivative without regularity assumptions.
Prescribed projected derivatives also hold almost everywhere across exceptional levels.
-/

public section

open MeasureTheory Set
open scoped Topology

/-- A constant real projection has zero projected derivative, including where the curve
is not differentiable and its total derivative is defined to be zero. -/
theorem ContinuousLinearMap.deriv_eq_zero_of_forall_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) {γ : ℝ → E} {c : ℝ}
    (hγ : ∀ t, L (γ t) = c) (t : ℝ) : L (deriv γ t) = 0 := by
  by_cases h : DifferentiableAt ℝ γ t
  · have hp := L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt
    rw [show L ∘ γ = fun _ ↦ c from funext hγ] at hp
    exact hp.unique (hasDerivAt_const t c)
  · rw [deriv_zero_of_not_differentiableAt h, map_zero]

/-- A real projection of a curve has the prescribed derivative almost everywhere, even when
exceptional projection levels have uncountable preimages. -/
theorem ContinuousLinearMap.apply_deriv_ae_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {θ θ' : ℝ → ℝ} {γ : ℝ → E}
    (π : E →L[ℝ] ℝ) (hπ : π ∘ γ = θ) {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hdγ : ∀ t ∈ Ioo a b \ s, θ t ∉ S → DifferentiableAt ℝ γ t) :
    (fun t ↦ π (deriv γ t)) =ᵐ[volume.restrict (Ioc a b)] θ' := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae ((hs.union (Set.toFinite ({a, b} : Set ℝ)).countable).ae_notMem volume),
    hS.ae_deriv_eq_zero_on_preimage θ (volume.restrict (Ioc a b))]
    with t ht hts hlevel
  have htb : t ≠ b := fun h ↦ hts (Or.inr (by simp [h]))
  have ht' : t ∈ Ioo a b \ s :=
    ⟨⟨ht.1, lt_of_le_of_ne ht.2 htb⟩, fun h ↦ hts (Or.inl h)⟩
  by_cases hγ : DifferentiableAt ℝ γ t
  · have hproj := π.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
    rw [hπ] at hproj
    exact hproj.unique (hdθ t ht')
  · have hmem : θ t ∈ S := by
      by_contra h
      exact hγ (hdγ t ht' h)
    have hzero : deriv θ t = 0 := hlevel hmem
    rw [(hdθ t ht').deriv] at hzero
    rw [deriv_zero_of_not_differentiableAt hγ, map_zero, hzero]
