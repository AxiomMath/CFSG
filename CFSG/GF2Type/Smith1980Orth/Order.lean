module

public import CFSG.GF2Type.Smith1980Orth.Defs
public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.LargeExtraspecial.S7SevenMain
public import CFSG.LargeExtraspecial.S4CEOmegaModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open Module

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.polarBilin_nondegenerate (O : OrthData S) : O.q.polarBilin.Nondegenerate :=
  ⟨fun x hx => O.nondeg x fun y => by rw [← QuadraticMap.polarBilin_apply_apply]; exact hx y,
    fun y hy => O.nondeg y fun x => by
      rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]; exact hy x⟩

theorem OrthData.width_eq_two_mul (O : OrthData S) : S.width = 2 * (S.width / 2) := by
  obtain ⟨k, hk⟩ := O.even
  omega

theorem OrthData.finrank_eq (O : OrthData S) :
    finrank (ZMod 2) (Fin S.width → ZMod 2) = 2 * (S.width / 2) := by
  rw [Module.finrank_fin_fun]
  exact O.width_eq_two_mul

theorem OrthData.card_omega (O : OrthData S) :
    ∃ r : ℕ, Odd r ∧
      Nat.card (timmesfeldOmega O.q) = 2 ^ (S.width / 2 * (S.width / 2 - 1)) * r := by
  rw [S7.timmesfeldOmega_eq O.q O.polarBilin_nondegenerate]
  exact S4.card_omegaGroup_eq O.polarBilin_nondegenerate (by have := O.four_le; omega)
    O.finrank_eq

theorem OrthData.card_isometries (O : OrthData S) :
    Nat.card (timmesfeldIsometries O.q) = 2 * Nat.card (timmesfeldOmega O.q) := by
  have : Nontrivial (Fin S.width → ZMod 2) := by
    have h4 := O.four_le
    exact ⟨⟨0, fun _ => 1, fun h => by
      have := congrFun h ⟨0, by omega⟩
      simp at this⟩⟩
  rw [S7.timmesfeldIsometries_eq, S7.timmesfeldOmega_eq O.q O.polarBilin_nondegenerate]
  exact S12DW.card_orthogonalGroup_eq O.polarBilin_nondegenerate

theorem OrthData.card_M (O : OrthData S) :
    (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega O.q) →
      Nat.card S.M = 2 ^ (1 + 2 * S.width) * (6 * Nat.card (timmesfeldOmega O.q))) ∧
    (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries O.q) →
      Nat.card S.M = 2 ^ (1 + 2 * S.width) * (12 * Nat.card (timmesfeldOmega O.q))) := by
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · rw [S14.card_M_eq_card_Q_mul, S.card_Q_eq, Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_perm, Nat.card_fin]
    rfl
  · rw [S14.card_M_eq_card_Q_mul, S.card_Q_eq, Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_perm, Nat.card_fin, O.card_isometries]
    ring

theorem factorization_card_eq_M (S : Setting G) :
    (Nat.card G).factorization 2 = (Nat.card S.M).factorization 2 := by
  have h := S.M.card_mul_index
  have hodd : ¬ 2 ∣ S.M.index := S14.not_two_dvd_index_M S
  have hi : S.M.index ≠ 0 := fun h0 => hodd (by rw [h0]; exact dvd_zero 2)
  rw [← h, Nat.factorization_mul Nat.card_pos.ne' hi, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

theorem OrthData.factorization_card (O : OrthData S) :
    (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega O.q) →
      (Nat.card G).factorization 2 = (S.width / 2 + 1) * (S.width / 2 + 2)) ∧
    (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries O.q) →
      (Nat.card G).factorization 2 = (S.width / 2 + 1) * (S.width / 2 + 2) + 1) := by
  obtain ⟨r, hr, hΩ⟩ := O.card_omega
  have hw := O.width_eq_two_mul
  have h4 := O.four_le
  have hM := O.card_M
  generalize hm : S.width / 2 = m at hw hΩ ⊢
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk] at hΩ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [factorization_card_eq_M, hM.1 h, hΩ, hw]
    have : 2 ^ (1 + 2 * (2 * (k + 2))) * (6 * (2 ^ ((k + 2) * (k + 1)) * r)) =
        2 ^ ((k + 2 + 1) * (k + 2 + 2)) * (3 * r) := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      ring
    rw [this]
    exact S14.factorization_two_pow_mul_odd ((by decide : Odd 3).mul hr)
  · rw [factorization_card_eq_M, hM.2 h, hΩ, hw]
    have : 2 ^ (1 + 2 * (2 * (k + 2))) * (12 * (2 ^ ((k + 2) * (k + 1)) * r)) =
        2 ^ ((k + 2 + 1) * (k + 2 + 2) + 1) * (3 * r) := by
      rw [show (12 : ℕ) = 2 * 2 * 3 by norm_num]
      ring
    rw [this]
    exact S14.factorization_two_pow_mul_odd ((by decide : Odd 3).mul hr)

end CFSG.GF2Type.Smith1980Orth
