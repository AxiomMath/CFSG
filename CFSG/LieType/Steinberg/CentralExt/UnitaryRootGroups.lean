module

public import CFSG.LieType.Universal.Unitary.Extras.Basic

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras

theorem one_add_pow_char_sq_eq_one {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {N : R} (hN : N ^ 3 = 0) : (1 + N) ^ p ^ 2 = 1 := by
  rw [add_pow_char_pow_of_commute p 2 (Commute.one_left N), one_pow]
  have h3 : 3 ≤ p ^ 2 := by
    have := (Fact.out : p.Prime).two_le
    nlinarith
  rw [← Nat.add_sub_cancel' h3, pow_add, hN, zero_mul, add_zero]

variable {F : Type*} [Field F] {n : ℕ}

theorem hasWt_nsmul_mul {e : Fin (n / 2) → ℤ} {i j : ℕ} {N M : Matrix (Fin n) (Fin n) F}
    (hN : HasWt {w | ∃ k : ℕ, i ≤ k ∧ w = k • e} N)
    (hM : HasWt {w | ∃ k : ℕ, j ≤ k ∧ w = k • e} M) :
    HasWt {w | ∃ k : ℕ, i + j ≤ k ∧ w = k • e} (N * M) :=
  hN.mul hM fun a c b ⟨k, hk, h1⟩ ⟨l, hl, h2⟩ => ⟨k + l, by omega, by
    rw [add_nsmul, ← h1, ← h2]
    abel⟩

variable {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem pow_three_mat_sub_one_eq_zero {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n γ) : (mat σ n x - 1) ^ 3 = 0 := by
  set e := toStd n γ
  have h1 : HasWt {w | ∃ k : ℕ, 1 ≤ k ∧ w = k • e} (mat σ n x - 1) :=
    (hasWt_of_mem_rootGroup hσ hx).mono fun w hw => by
      rcases mem_wt2.1 hw with rfl | rfl
      · exact ⟨1, le_rfl, (one_nsmul _).symm⟩
      · exact ⟨2, by norm_num, rfl⟩
  have h3 := hasWt_nsmul_mul (hasWt_nsmul_mul h1 h1) h1
  rw [pow_three']
  ext a b
  refine h3.eq_zero_apply fun ⟨k, hk, hab⟩ => hγ ?_
  exact eq_zero_of_weight_sub_eq_nsmul hab hk

theorem isPGroup_rootGroup [Nonempty (Fin n)] {p : ℕ} [Fact p.Prime] [CharP F p]
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0) : IsPGroup p (rootGroup σ hσ n γ) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  apply mat_injective
  rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one,
    ← add_sub_cancel (1 : Matrix (Fin n) (Fin n) F) (mat σ n x)]
  exact one_add_pow_char_sq_eq_one (pow_three_mat_sub_one_eq_zero hσ hγ x.2)

end CFSG.LieType.Steinberg
