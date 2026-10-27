module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.RankThree.PartOne.CTP.StrongPSporadic
public import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenPair
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbedding CFSG.RankThree.PartOne.StrongP

section CertificateInstances


theorem sporadicRankTable_holds : SporadicRankTable := by
  refine sporadicRankTable_of_native ?_
  intro s p hp hp5 S _ _ ⟨e⟩ h3
  by_contra hne
  have hcard : Nat.card S = sporOrd s := (Nat.card_congr e.toEquiv).trans
    (card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card s)
  suffices h2 : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2 by omega
  have key : ¬ p ^ 4 ∣ sporOrd s → HasNoncommPair p S → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2 :=
    fun h4 h => pRank_le_two_of_hasNoncommPair hp (by rwa [hcard]) h
  have hmap : HasNoncommPair p (CFSG.Blueprint.NativeSporadic.Carrier s) → HasNoncommPair p S :=
    fun h => h.map e.symm.toMonoidHom e.symm.injective
  by_cases h3d : p ^ 3 ∣ sporOrd s
  swap
  · exact CFSG.SectionRank.QTK.CentreFact.small_pRank_top_le_two_of_not_dvd hp (by rwa [hcard])
  rcases offList_cases s p hp (by omega) h3d with hl | hoff
  · rcases hl with ⟨rfl, -⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · omega
    · exact absurd (by rcases hs with rfl | rfl | rfl | rfl | rfl <;>
        simp [SporadicRankThreePair]) hne
    · rcases hs with rfl | rfl
      · exact key (by norm_num [sporOrd])
          (hmap CFSG.RankThree.PartOne.CTP.hasNoncommPair_Fi24_seven)
      · exact absurd (by simp [SporadicRankThreePair]) hne
    · haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
        CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
      haveI : IsSimpleGroup S := e.isSimpleGroup
      obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
      exact key (by norm_num [sporOrd])
        (CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_of_mulEquiv_Gmat f)
  · rcases hoff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | omega
      | exact key (by norm_num [sporOrd]) (hmap (CFSG.RankThree.PartOne.CTP.hasNoncommPair_carrier
          (by simp [CFSG.RankThree.PartOne.CTP.SporadicPairNC])))

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
