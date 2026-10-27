module

public import CFSG.GF2Type.Smith1980Orth.Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.card_le_of_isPGroup_of_width_eq_four (O : OrthData S) (hw : S.width = 4)
    (P : Subgroup S.Mbar) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ 4 := by
  obtain ⟨r, hr, hcard⟩ := O.card_omega
  have he : 2 ^ (S.width / 2 * (S.width / 2 - 1)) = 4 := by rw [hw]; norm_num
  rw [he] at hcard
  have hM : Nat.card S.Mbar ∣ 2 ^ 4 * (3 * r) := by
    rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin, hcard]
      exact ⟨2, by ring⟩
    · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin,
        O.card_isometries, hcard]
      exact ⟨1, by ring⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hdvd : 2 ^ k ∣ 2 ^ 4 * (3 * r) := by
    rw [← hk]
    exact (Subgroup.card_subgroup_dvd_card P).trans hM
  have hodd : Odd (3 * r) := (by decide : Odd 3).mul hr
  have h4 : 2 ^ k ∣ 2 ^ 4 :=
    (Nat.Coprime.dvd_mul_right ((Nat.coprime_two_left.mpr hodd).pow_left k)).mp hdvd
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h4

theorem OrthData.factorization_ne_fifteen (O : OrthData S) (hw : S.width = 4) :
    (Nat.card G).factorization 2 ≠ 15 := by
  rcases O.factorization_card_cases with h | h <;> rw [h, hw] <;> norm_num

end CFSG.GF2Type.Smith1980Orth
