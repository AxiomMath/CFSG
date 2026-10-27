module


public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension

public section

namespace CFSG.LinearAlgebra.CoprimeActions.PrimeOrderBinaryLinearDimensionBound

theorem order_le_finrank (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : W ≃ₗ[ZMod 2] W) (hσ : σ ^ q = 1) (hne : σ ≠ 1) :
    orderOf (2 : ZMod q) ≤ Module.finrank (ZMod 2) W := by
  classical
  set s : Module.End (ZMod 2) W := σ.toLinearMap with hs
  have hpow : ∀ k : ℕ, ∀ w, (σ ^ k) w = (s ^ k) w := by
    intro k; induction k with
    | zero => intro w; rfl
    | succ k ih => intro w; rw [pow_succ, pow_succ]; simp [ih, hs]
  have hsq : s ^ q = 1 := by
    ext w; rw [← hpow, hσ]; rfl
  set W0 : Submodule (ZMod 2) W := LinearMap.range (s - 1) with hW0
  have hmap : W0.map s = W0 := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨s w, by simp [sub_eq_add_neg, hs]⟩
    · rintro _ ⟨u, rfl⟩
      refine ⟨(s - 1) (σ.symm u), ⟨_, rfl⟩, ?_⟩
      simp [hs, sub_eq_add_neg]
  let σ' : W0 ≃ₗ[ZMod 2] W0 := LinearEquiv.ofSubmodules σ W0 W0 hmap
  have hσ'pow : ∀ k : ℕ, ∀ v : W0, (((σ' ^ k) v : W0) : W) = (σ ^ k) (v : W) := by
    intro k; induction k with
    | zero => intro v; rfl
    | succ k ih => intro v; rw [pow_succ, pow_succ]; simp [ih, σ']
  have hσ'q : σ' ^ q = 1 := by
    ext v; rw [hσ'pow, hσ]; rfl
  have hfix : LinearMap.ker (σ'.toLinearMap - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h1 : σ (v : W) = v := by
      have := congrArg (fun x : W0 => (x : W)) hv
      simpa [σ', sub_eq_zero] using this
    obtain ⟨w, hw⟩ := v.2
    have hN : (∑ i ∈ Finset.range q, s ^ i) (v : W) = 0 := by
      rw [← hw]
      have := geom_sum_mul s q
      rw [hsq, sub_self] at this
      have := congrArg (fun f : Module.End (ZMod 2) W => f w) this
      simpa using this
    have hsv : s (v : W) = v := h1
    have hN2 : (∑ i ∈ Finset.range q, s ^ i) (v : W) = (q : ZMod 2) • (v : W) := by
      rw [LinearMap.sum_apply]
      have : ∀ i, (s ^ i) (v : W) = v := by
        intro i; induction i with
        | zero => rfl
        | succ i ih => rw [pow_succ, Module.End.mul_apply, hsv, ih]
      simp [this]
      exact (Nat.cast_smul_eq_nsmul _ _ _).symm
    have hodd : (q : ZMod 2) = 1 := by
      have : Odd q := hq.out.odd_of_ne_two hq2
      exact (ZMod.natCast_eq_one_iff_odd).2 this
    rw [hN2, hodd, one_smul] at hN
    exact_mod_cast Subtype.ext hN
  have hdvd := CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension.orderOf_two_dvd_finrank
    q hq2 σ' hσ'q hfix
  have hpos : 0 < Module.finrank (ZMod 2) W0 := by
    apply Module.finrank_pos_iff.2
    have : ∃ w, σ w ≠ w := by
      by_contra h
      push Not at h
      exact hne (LinearEquiv.ext h)
    obtain ⟨w, hw⟩ := this
    refine ⟨⟨⟨(s - 1) w, w, rfl⟩, 0, ?_⟩⟩
    intro h
    have := congrArg (fun x : W0 => (x : W)) h
    simp [hs, sub_eq_zero] at this
    exact hw this
  exact (Nat.le_of_dvd hpos hdvd).trans (Submodule.finrank_le W0)

end CFSG.LinearAlgebra.CoprimeActions.PrimeOrderBinaryLinearDimensionBound
