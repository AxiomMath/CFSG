module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.OmegaRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def u1 : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem c3_ne_one : (c3 : SL(2, K)) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [c3] at this

theorem c3_not_commute_u1 : ¬ Commute (c3 : SL(2, K)) u1 := by
  intro h
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  simp [c3, u1, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem c3_sq_not_commute_u1 : ¬ Commute ((c3 : SL(2, K)) ^ 2) u1 := by
  intro h
  have h1 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  rw [coe_c3_sq] at h1
  simp [u1, Matrix.mul_apply, Fin.sum_univ_two] at h1

theorem c3_pow_commute_u1 {n : ℕ} (h : Commute ((c3 : SL(2, K)) ^ n) u1) :
    (c3 : SL(2, K)) ^ n = 1 := by
  have hn : (c3 : SL(2, K)) ^ n = c3 ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, c3_pow_three, one_pow, mul_one]
  rw [hn] at h ⊢
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : n % 3
  · rfl
  · rw [pow_one] at h
    exact absurd h c3_not_commute_u1
  · exact absurd h c3_sq_not_commute_u1

theorem two_le_pRank_three_of_commuting_sl2 {K' : Type} [Field K'] {X : Type} [Group X] [Finite X]
    (φ : SL(2, K) →* X) (ψ : SL(2, K') →* X) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (hc : ∀ A B, Commute (φ A) (ψ B)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens (x := φ c3) (y := ψ c3)
    ?_ ?_ (hc _ _) ?_ ?_
  · rw [← map_pow, c3_pow_three, map_one]
  · rw [← map_pow, c3_pow_three, map_one]
  · intro h
    exact c3_ne_one (hφ (h.trans (map_one φ).symm))
  · intro n hn
    have hcomm : Commute (φ c3 ^ n) (φ u1) := by
      rw [hn]
      exact (hc _ _).symm
    rw [← map_pow] at hcomm
    have h1 : Commute ((c3 : SL(2, K)) ^ n) u1 := by
      have := hcomm.eq
      rw [← map_mul, ← map_mul] at this
      exact hφ this
    have h2 := c3_pow_commute_u1 h1
    rw [← map_pow, h2, map_one] at hn
    exact c3_ne_one (hψ (hn.symm.trans (map_one ψ).symm))

end CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
