module

public import CFSG.GF2Type.Aschbacher1977.SectionalRankFour
import CFSG.GF2Type.Aschbacher1977.AlternatingExclusions
import CFSG.GF2Type.Aschbacher1977.ClassicalExclusions
import CFSG.GF2Type.Aschbacher1977.LieExclusions
import CFSG.GF2Type.Aschbacher1977.SmallExclusions
import CFSG.GF2Type.Aschbacher1977.SymplecticExclusions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint CFSG.LargeExtraspecial

theorem width_two_cases
    {G : Type} [Group G] [Finite G] (S : Setting G) (hw : S.width = 2)
    (hl : AS35W.GH74List G) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 ∨ LieModel G .PSU 4 3 1 ∨
      LieModel G .G2 0 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ NativeSporadic.IsSporadic G .M12 ∨
      NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .J3 := by
  rcases hl with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
    ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
    ⟨p, f, hp, hf, hq, h⟩ | h | ⟨n, h8, h11, ⟨e⟩⟩ | h
  ·
    by_cases h3 : p ^ f = 3
    · exact Or.inr (Or.inr (Or.inr (Or.inl (lieModel_G2_three_one hp h h3))))
    · exact (not_lieModel_G2_of_ne_three S hw hp hp2 hf h h3).elim
  ·
    exact (not_lieModel_trialityD4 S hw hp hp2 hf h).elim
  ·
    by_cases h3 : p ^ f = 3
    · exact Or.inl (lieModel_PSU_four_two_of_PSp_two_three (lieModel_PSp_two_three_one hp h h3))
    · exact (not_lieModel_PSp_two_of_ne_three S hw hp hp2 hf h h3).elim
  ·
    exact (not_lieModel_twistedG2 S hw h).elim
  ·
    by_cases h3 : p ^ f = 3
    · exact Or.inr (Or.inl (lieModel_PSL_four_three_one hp hf h3 h))
    · exact (not_lieModel_PSL_four_of_ne_three S hw hp hp2 hf h h3).elim
  ·
    by_cases h3 : p ^ f = 3
    · exact Or.inr (Or.inr (Or.inl (lieModel_PSU_four_three_one hp hf h3 h)))
    · exact (not_lieModel_PSU_four_of_ne_three S hw hp hp2 hf hq h h3).elim
  ·
    exact (not_lieModel_PSL_five S hw hp hf hq h).elim
  ·
    exact (not_lieModel_PSU_five S hw hp hf hq h).elim
  ·
    rcases h with h | h | h | h
    · exact (not_lieModel_PSL_2_2_3 S hw h).elim
    · exact (not_lieModel_PSL_2_2_4 S hw h).elim
    · exact (not_lieModel_PSL_3_2_2 S hw h).elim
    · exact (not_lieModel_twistedB2_0_2_3 S h).elim
  ·
    rcases (by omega : n = 8 ∨ n = 9 ∨ 10 ≤ n) with rfl | rfl | h10
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))
    · exact (not_alternating_of_ten_le_of_le_eleven S hw h10 h11 e).elim
  ·
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact (not_isSporadic_M22 S hw h).elim
    · exact (not_isSporadic_M23 S hw h).elim
    · exact (not_isSporadic_J1 S hw h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · exact (not_isSporadic_McL S hw h).elim
    · exact (not_isSporadic_Ly S hw h).elim

theorem width_two_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * 2)) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 ∨ LieModel G .PSU 4 3 1 ∨
      LieModel G .G2 0 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ NativeSporadic.IsSporadic G .M12 ∨
      NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .J3 := by
  obtain ⟨S, -, hw⟩ := exists_setting_of_extraspecial hz hext hcard
  exact width_two_cases S hw (gh74Models_of_width_two hnonab hz hext hcard)

end CFSG.GF2Type.Aschbacher1977
