module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Data
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtA9Data3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)),
    D1ComponentConfig3 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9)) →
    ∃ (X : Subgroup G) (σ z : G), D1A9DataCore P M H R X σ z

theorem stmtA9Data3_of (hL : KFactA9Local) : StmtA9Data3 G := by
  intro _ P M H R Rbar hcfg K hK huniq hcent hZ e
  exact exists_a9DataCore_of hL hcfg.glob.toU.toAGLGlobal hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hZ e

end CFSG.LocalAnalysis.RankThreeTheoremC
