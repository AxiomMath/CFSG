module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem ka_fix_conjAut_proj {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (L : Subgroup (projectiveSL n F)) (N : Matrix (Fin n) (Fin n) F) (hN0 : N ≠ 0)
    (hN2 : N * N = 0)
    (hL : ∀ c : F, ∃ g : SL(n, F), (g : Matrix (Fin n) (Fin n) F) = 1 + c • N ∧
      proj n F g ∈ L)
    (e : MulAut (projectiveSL n F)) (hodd : Odd (orderOf e)) (hfix : ∀ r ∈ L, e r = r) :
    ∃ A : GL (Fin n) F, e = conjAut n F A := by
  have key : ∀ (B : GL (Fin n) F) (τ : F ≃+* F),
      (∀ r ∈ L, (conjAut n F B * fieldAut n F τ) r = r) → τ = 1 := fun B τ hBfix =>
    ka_proj_sigma_eq_one B τ N hN0 hN2 fun c => by
      obtain ⟨g, hg, hgL⟩ := hL c
      exact ⟨g, hg, hBfix _ hgL⟩
  obtain ⟨A, σ, ε, hε, he⟩ := (automorphism_generation hn).2 e
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at he
    subst he
    have hσ := key A σ hfix
    refine ⟨A, ?_⟩
    rw [hσ, map_one, mul_one]
  · rw [pow_one] at he
    have hsq : e * e = conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut n F (σ * σ) := by
      rw [← sq e, he]
      exact sq_conjAut_fieldAut_dualAut A σ
    have hfix2 : ∀ r ∈ L, (e * e) r = r := fun r hr => by
      rw [MulAut.mul_apply, hfix r hr, hfix r hr]
    rw [hsq] at hfix2
    have hσσ := key _ _ hfix2
    rw [hσσ, map_one, mul_one] at hsq
    obtain ⟨k, hk⟩ := hodd
    have h1 : e ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one e
    have h2 : e = (e * e) ^ (k + 1) := by
      calc e = e ^ (2 * k + 1) * e := by rw [h1, one_mul]
        _ = e ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
        _ = (e * e) ^ (k + 1) := by rw [pow_mul, sq]
    refine ⟨(A * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) ^ (k + 1), ?_⟩
    rw [map_pow, ← hsq]
    exact h2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
