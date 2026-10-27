module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lFixedComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporFix

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification


theorem a2l_isSimpleGroup_of_equiv {K C : Type} [Group K] [Group C] (e : K ≃* C)
    (hs : IsSimpleGroup C) : IsSimpleGroup K :=
  @MulEquiv.isSimpleGroup _ _ _ _ hs e

theorem closureSmallCases_holds : HypA2.ClosureSmallCases := by
  intro S _ _ hS σ P hP
  rcases hS with hL | hHe | hM12 | hJ2
  ·
    left
    have hcard : Nat.card S = 20160 := by
      rw [GH74.card_of_lieModel_PSL (G := S) (n := 3) (p := 2) (f := 2) (by norm_num) hL]
      decide
    have hlt := a2l_card_quot_lt hP.2.2.1
    omega
  ·
    obtain ⟨e⟩ := hHe
    haveI : IsSimpleGroup S := a2l_isSimpleGroup_of_equiv e Sporadic.He.isSimpleGroup_He
    obtain ⟨eZ⟩ := a2l_fusionZStar_equiv hP
    rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
        GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
        inferInstance (a2l_nonabelian hP) ⟨e⟩ σ hP.1 P hP.2.1
        (a2l_properFixedComponent hP).2.2.1 hP.2.2.1 with hL34 | hA7
    · exact Or.inr (LieModel.of_mulEquiv eZ hL34)
    · obtain ⟨eA⟩ := hA7
      left
      have h2520 : Nat.card (P ⧸ center P) = 2520 := by
        rw [← Nat.card_congr eZ.toEquiv, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
          Nat.card_fin]
        norm_num [Nat.factorial]
      omega
  ·
    obtain ⟨e⟩ := hM12
    haveI : IsSimpleGroup S :=
      a2l_isSimpleGroup_of_equiv e Sporadic.Mathieu.fam_m12_simplicity.2.2
    left
    have hle := a2l_card_quot_le_fixed hP.2.1
    rcases CatFC.card_fixedSubgroup_m12 e (a2l_orderOf_eq_two hP) with hc | hc | hc <;> omega
  ·
    obtain ⟨e⟩ := hJ2
    haveI : IsSimpleGroup S := a2l_isSimpleGroup_of_equiv e Sporadic.J2.isSimpleGroup_J2
    left
    have hle := a2l_card_quot_le_fixed hP.2.1
    rcases GS82PumpInputs.SporFix.card_fixedSubgroup_j2 e (a2l_orderOf_eq_two hP) with
      hc | hc | hc <;> omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
