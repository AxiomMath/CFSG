module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem fixedFree_of_conj (ρ : A5 →* (V ≃ₗ[ZMod 2] V))
    (h : ∀ u : V, ρ a₀ u = u → u = 0) {y : A5} (hy : orderOf y = 5) :
    ∀ u : V, ρ y u = u → u = 0 := by
  obtain ⟨z, k, hk, rfl⟩ := exists_conj_of_orderOf_eq_five hy
  have hpow5 : (ρ a₀) ^ 5 = 1 := by
    rw [← map_pow, (show a₀ ^ 5 = 1 from by
      have := pow_orderOf_eq_one a₀
      rwa [orderOf_a₀] at this), map_one]
  intro u hu
  have hconj : ρ (z * a₀ ^ k * z⁻¹) = ρ z * (ρ a₀) ^ k * (ρ z)⁻¹ := by
    simp only [map_mul, map_pow, map_inv]
  have key : (ρ z * (ρ a₀) ^ k * (ρ z)⁻¹) u = u := by
    rw [← hconj]; exact hu
  have key2 : ρ z (((ρ a₀) ^ k) ((ρ z).symm u)) = u := by
    simpa using key
  have h2 : ((ρ a₀) ^ k) ((ρ z).symm u) = (ρ z).symm u := by
    have := congrArg (ρ z).symm key2
    simpa using this
  rcases hk with rfl | rfl
  ·
    have hfix : ρ a₀ ((ρ z).symm u) = (ρ z).symm u := by simpa using h2
    have hzero : (ρ z).symm u = 0 := h _ hfix
    simpa [hzero] using ((ρ z).apply_symm_apply u).symm
  ·
    have hiter : ∀ n : ℕ, (((ρ a₀) ^ 2) ^ n) ((ρ z).symm u) = (ρ z).symm u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, h2, ih]
    have hα_eq : ρ a₀ = (ρ a₀ ^ 2) ^ 3 := by
      have h6 : (ρ a₀) ^ 6 = ρ a₀ := by
        change (ρ a₀) ^ (5 + 1) = ρ a₀
        rw [pow_succ, hpow5, one_mul]
      nth_rewrite 1 [← h6]
      rw [← pow_mul]
    have hfix : ρ a₀ ((ρ z).symm u) = (ρ z).symm u := by
      rw [hα_eq]
      exact hiter 3
    have hzero : (ρ z).symm u = 0 := h _ hfix
    simpa [hzero] using ((ρ z).apply_symm_apply u).symm

theorem fixedFree_of_orderOf_eq_five (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (hα : ∀ u : V, σ (a₀, 1) u = u → u = 0) (hβ : ∀ u : V, σ (1, a₀) u = u → u = 0)
    {y : A5} (hy : orderOf y = 5) :
    (∀ u : V, σ (y, 1) u = u → u = 0) ∧ (∀ u : V, σ (1, y) u = u → u = 0) := by
  constructor
  · intro u hu
    exact fixedFree_of_conj (σ.comp (MonoidHom.inl A5 A5)) (by simpa using hα) hy u
      (by simpa using hu)
  · intro u hu
    exact fixedFree_of_conj (σ.comp (MonoidHom.inr A5 A5)) (by simpa using hβ) hy u
      (by simpa using hu)

end CFSG.EvenSporadicStandard.HNRecog.Fpf
