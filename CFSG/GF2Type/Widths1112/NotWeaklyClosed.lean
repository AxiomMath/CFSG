module

public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.LargeExtraspecial.FS77PSU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial

namespace CFSG.GF2Type.Widths1112

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_QG_of_card [IsSimpleGroup G] (S : Setting G)
    (hAS : S14.AschbacherSmith35Input) (hw : 5 ≤ S.width) (hw4 : S.width ≠ 4)
    (h2 : (Nat.card S.Mbar).factorization 2 + 1 + 2 * S.width <
      (S.width + 2) * (S.width + 1) / 2) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra hW
  push Not at hW
  rcases hAS G S (by omega) hW with he | ⟨h4, -⟩
  · obtain ⟨e⟩ := he
    have h := FS77.factorization_card_timmesfeldPSU (m := S.width + 2) (by omega)
    rw [← Nat.card_congr e.toEquiv, show S.width + 2 - 1 = S.width + 1 by omega] at h
    have hodd : ¬ 2 ∣ S.M.index := S14.not_two_dvd_index_M S
    have hi : S.M.index ≠ 0 := fun h0 => hodd (by rw [h0]; exact dvd_zero 2)
    have hfin : Finite S.Mbar := Bridge.finite_Mbar S
    have hMc : Nat.card S.M ≠ 0 := Nat.card_pos.ne'
    have hMb : Nat.card S.Mbar ≠ 0 := Nat.card_pos.ne'
    have hQ : (2 : ℕ) ^ (1 + 2 * S.width) ≠ 0 := by positivity
    have hG : (Nat.card G).factorization 2 = (Nat.card S.M).factorization 2 := by
      rw [← S.M.card_mul_index, Nat.factorization_mul hMc hi, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
    have hM : (Nat.card S.M).factorization 2 =
        1 + 2 * S.width + (Nat.card S.Mbar).factorization 2 := by
      rw [S14.card_M_eq_card_Q_mul, S.card_Q_eq, Nat.factorization_mul hQ hMb, Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    omega
  · omega

end CFSG.GF2Type.Widths1112
