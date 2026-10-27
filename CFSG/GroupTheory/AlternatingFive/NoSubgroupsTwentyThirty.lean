module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.GroupTheory.AlternatingFive

theorem alternating_five_no_subgroup_card_twenty_or_thirty
    (A : Subgroup (alternatingGroup (Fin 5))) :
    Nat.card A ≠ 20 ∧ Nat.card A ≠ 30 := by
  classical
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hGcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcard20 : Nat.card A ≠ 20 := by
    intro hcard
    have hindex : A.index = 3 := by
      have hmul := A.card_mul_index
      rw [hcard, hGcard] at hmul
      omega
    have hcore : A.normalCore = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top A.normalCore with hbot | htop
      · exact hbot
      · exfalso
        have hAtop : A = ⊤ := by
          have hle_top : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ A := by
            simpa only [htop] using A.normalCore_le
          exact top_le_iff.mp hle_top
        rw [hAtop, Subgroup.card_top, hGcard] at hcard
        omega
    have hcoreker : A.normalCore =
        (MulAction.toPermHom (alternatingGroup (Fin 5))
          (alternatingGroup (Fin 5) ⧸ A)).ker :=
      Subgroup.normalCore_eq_ker (G := alternatingGroup (Fin 5)) (H := A)
    have hker : (MulAction.toPermHom (alternatingGroup (Fin 5))
          (alternatingGroup (Fin 5) ⧸ A)).ker = ⊥ := by
      rw [← hcoreker, hcore]
    have hinj : Function.Injective (MulAction.toPermHom (alternatingGroup (Fin 5))
          (alternatingGroup (Fin 5) ⧸ A)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have hquotcard : Nat.card (alternatingGroup (Fin 5) ⧸ A) = 3 := by
      rw [← Subgroup.index_eq_card (G := alternatingGroup (Fin 5)) (H := A), hindex]
    have hpermcard : Nat.card
        (Equiv.Perm (alternatingGroup (Fin 5) ⧸ A)) = 6 := by
      rw [Nat.card_perm, hquotcard]
      decide
    have hcardle : Nat.card (alternatingGroup (Fin 5)) ≤
        Nat.card (Equiv.Perm (alternatingGroup (Fin 5) ⧸ A)) :=
      Nat.card_le_card_of_injective _ hinj
    have hle6 : Nat.card (alternatingGroup (Fin 5)) ≤ 6 := by
      calc
        Nat.card (alternatingGroup (Fin 5)) ≤
            Nat.card (Equiv.Perm (alternatingGroup (Fin 5) ⧸ A)) := hcardle
        _ = 6 := hpermcard
    rw [hGcard] at hle6
    omega
  have hcard30 : Nat.card A ≠ 30 := by
    intro hcard
    have hindex : A.index = 2 := by
      have hmul := A.card_mul_index
      rw [hcard, hGcard] at hmul
      omega
    have hAnormal : A.Normal := Subgroup.normal_of_index_eq_two hindex
    have : A.Normal := hAnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top A with hbot | htop
    · rw [hbot, Subgroup.card_bot] at hcard
      omega
    · rw [htop, Subgroup.card_top, hGcard] at hcard
      omega
  exact ⟨hcard20, hcard30⟩

end CFSG.GroupTheory.AlternatingFive

namespace CFSG.GroupTheory.SpecialLinear

open CFSG.GroupTheory.AlternatingFive

theorem sl2_four_no_subgroup_card_twenty_or_thirty
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) :
    Nat.card B ≠ 20 ∧ Nat.card B ≠ 30 := by
  classical
  obtain ⟨e₀⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  let e : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
      alternatingGroup (Fin 5) :=
    (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 2)).symm.trans e₀
  have h := alternating_five_no_subgroup_card_twenty_or_thirty (B.map e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective] at h
  exact h

end CFSG.GroupTheory.SpecialLinear
