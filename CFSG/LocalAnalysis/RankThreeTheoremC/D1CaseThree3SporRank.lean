module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (CaseThreeKFact SporCaseThreeKFacts)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne (SectionsForceEvenRankFour SimplePresentationMSectionsForceEvenRankFour)

variable {G : Type} [Group G] [Finite G]

namespace D1ComponentConfig3

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem pRank_sylow_le_three (h : D1ComponentConfig3 p P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (T : Sylow p K) :
    Open.pRank p (T : Subgroup K) ≤ 3 := by
  have hp : p.Prime := h.ext.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := (T.isPGroup'.map K.subtype).exists_le_sylow
  calc Open.pRank p (T : Subgroup K)
      ≤ Open.pRank p ((T : Subgroup K).map K.subtype) :=
        SectionRank.pRank_le_map hp.one_lt K.subtype K.subtype_injective _
    _ ≤ Open.pRank p (S : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
        SectionRank.pRank_mono hp.one_lt hS
    _ = Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
        sylow_pRank_eq p hp S Rbar
    _ = 3 := h.pRank_rbar_eq_three

end D1ComponentConfig3

@[expose] def SporCaseThreeKFactsRank3E3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ s : TauCeti.SporadicName,
    s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → IsPGroup p (Subgroup.center K) →
      IsCyclic (Subgroup.center K) → ¬ (s = .J3 ∧ p = 3 ∧ Subgroup.center K = ⊥) →
      (∀ T : Sylow p K, CFSG.Open.pRank p (T : Subgroup K) ≤ 3) →
      CaseThreeKFact p K

structure SporSectionFacts3 : Prop where
  bridge : ∀ s : TauCeti.SporadicName,
    Nonempty (Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)
  fi22 : SectionsForceEvenRankFour (Carrier .Fi22)
  fi23 : SectionsForceEvenRankFour (Carrier .Fi23)
  fi24Prime : SectionsForceEvenRankFour (Carrier .Fi24Prime)
  babyMonster : SectionsForceEvenRankFour (Carrier .B)
  monster : SimplePresentationMSectionsForceEvenRankFour

end CFSG.LocalAnalysis.RankThreeTheoremC
