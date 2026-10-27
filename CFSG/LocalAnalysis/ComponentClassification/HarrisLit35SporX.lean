module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporBase
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporX
public import CFSG.GH74.Generic.GKFSporadic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem sporCompData_M :
    SporCompData .M := by
  refine ⟨CatalogueU.sporadicOddCoreFree_M, fun G _ _ hGs _ ⟨eG⟩ t ht B hB hsB => ?_,
    fun G _ _ hs _ hG α _ hα => ?_⟩
  · obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput G hGs ⟨eG⟩ t ht B hB
    obtain ⟨eM⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple eG
    have hM : Nat.card (↥B ⧸ center ↥B) ∣ Open.monsterOrder := by
      rw [← YGroups.Y443.natCard_Gmat_eq_monsterOrder, ← Nat.card_congr eM.toEquiv]
      exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card B).trans
        (Subgroup.card_subgroup_dvd_card _))
    exact GSThmB.MonsterArith.not_smallCentralQuotient h41 hM hsB
  · exact (hα (CatLeafProof.monsterInnerInput G hs hG α)).elim

end CFSG.ComponentClassification.HarrisLit

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem rowFor_spor_Suz :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .Suz := by
  refine rowFor_spor_of_card CatalogueU.sporadicOddCoreFree_Suz {20160, 95040, 604800}
    (fun q N hN => ?_) (fun G _ _ ⟨e⟩ t ht B hB => ?_)
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)
  · rcases hN with rfl | rfl | rfl
    · exact N36.ne_of_bracket (a := 34) (by norm_num) (by norm_num)
    · exact N36.ne_of_bracket (a := 57) (by norm_num) (by norm_num)
    · exact N36.ne_of_bracket (a := 106) (by norm_num) (by norm_num)
  · exact Or.inl
      (Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB)
  · rcases SolMax.suzOuterComponentsInput_holds G hG α hα2 hα B hB with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

theorem rowFor_spor_J1 : RowFor fun Y _ => NativeSporadic.IsSporadic Y .J1 := by
  intro G _ _ p w v L K h hs
  exact (h.false_of_noTwoCover (GH74.Generic.noTwoCover_J1_of_walter _ hs)).elim

theorem rowFor_spor_J3 (hJ3 : N36.HSJ3TwoMultiplierFact) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .J3 := by
  intro G _ _ p w v L K h ⟨e⟩
  exact (h.false_of_noTwoCover fun Y _ _ hY h2 ⟨eY⟩ => hJ3.2 Y hY h2 ⟨eY.trans e⟩).elim

theorem rowFor_spor_He (hHe : TBLit.HeldTrivialMultiplier) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .He := by
  intro G _ _ p w v L K h ⟨e⟩
  exact (h.false_of_noTwoCover fun Y _ _ hY _ ⟨eY⟩ => hHe Y hY ⟨eY.trans e⟩).elim

theorem rowFor_spor_ONan (hSM : RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .ONan := by
  intro G _ _ p w v L K h ⟨e⟩
  exact (h.false_of_odd_hopfMultiplier (X := NativeSporadic.ON) e (by rw [hSM.2]; decide)).elim

end CFSG.ComponentClassification.HarrisLit.L35
