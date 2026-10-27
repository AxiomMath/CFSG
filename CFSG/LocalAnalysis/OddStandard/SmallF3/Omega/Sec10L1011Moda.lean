module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec1011_cube_bound :
    ∀ (σ : Equiv.Perm (Fin 5)), σ ^ 3 = 1 → ∀ w : Fin 5 → ZMod 2,
      IsEvenVec w → vecWeight (w + permVec σ w) ≤ 2 := by
  unfold IsEvenVec vecWeight permVec
  decide +kernel

theorem sec1011_cube_inv_bound :
    ∀ (σ : Equiv.Perm (Fin 5)), σ ^ 3 = 1 → ∀ w1 w2 : Fin 5 → ZMod 2,
      IsEvenVec w1 → IsEvenVec w2 →
        vecWeight ((w1 + permVec σ w1) + (w2 + permVec σ⁻¹ w2)) ≤ 2 := by
  unfold IsEvenVec vecWeight permVec
  decide +kernel

theorem sec1011_comm_cube_cases :
    ∀ σ1 σ2 : Equiv.Perm (Fin 5), σ1 ^ 3 = 1 → σ2 ^ 3 = 1 →
      σ1 * σ2 = σ2 * σ1 → σ1 = 1 ∨ σ2 = 1 ∨ σ2 = σ1 ∨ σ2 = σ1⁻¹ := by
  decide +kernel

theorem sec1011_perm5_two_pow_bounded :
    ∀ y : Equiv.Perm (Fin 5), (∃ k : ℕ, k ≤ 3 ∧ y ^ (2 ^ k) = 1) → y ^ 4 = 1 := by
  decide +kernel

theorem sec1011_perm5_conj_four :
    ∀ x : Equiv.Perm (Fin 5), x ≠ 1 → x ^ 4 = 1 →
      ∃ g : Equiv.Perm (Fin 5), (x * (g * x * g⁻¹)) ^ 4 ≠ 1 := by
  decide +kernel

theorem sec1011_card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm]
  norm_num

theorem sec1011_card_perm_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm]
  norm_num

end CFSG.OddStandard.SmallF3.Omega
