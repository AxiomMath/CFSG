module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81ElevenElevenJZeroShape : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → IsCaseTwoGroup p ↥K → K.Normal →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    jZero H L ≤ d1PlusCore p H K → Open.pRank p (d1PlusCore p H K) = 1 →
    p ∣ Nat.card (jZero H L) →
      ¬ HasNormalPComplement p (↥(jZero H L) ⧸ CFSG.pCore 2 ↥(jZero H L)) ∧
      (CFSG.HallHigman.IsPSolvable p (↥(jZero H L) ⧸ CFSG.pCore 2 ↥(jZero H L)) →
        p = 3 ∧ ∃ I ∈ cZero (H ⊓ L), Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3)))

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
