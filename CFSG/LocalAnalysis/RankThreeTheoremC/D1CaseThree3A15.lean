module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Data
import CFSG.LocalAnalysis.AGLEmbedding.A15BlockOrbit
import CFSG.LocalAnalysis.AGLEmbedding.A15NoBlockOrbit
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

@[expose] def StmtA15Data3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ [Fact (Nat.Prime 5)] (P : Sylow 5 G)
    (M H R : Subgroup G) (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)),
    D1ComponentConfig3 5 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 5)),
      orderOf c = 5 → c ∈ (Subgroup.center K).map K.subtype) →
    Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 15)) →
    ∃ (c : Fin 3 → G) (σ τ : G), D1A15Data P M H R c σ τ

theorem stmtA15Data3_of (hL : KFactA15Local) : StmtA15Data3 G := by
  intro _ P M H R Rbar hcfg K hK huniq hcent hZ e
  exact exists_a15Data_of hL hcfg.glob.toU.toAGLGlobal
    (fun q hq _ => absurd (four_le_evenRank_of_mem_betaFour hq) (by rw [hcfg.glob.rank]; omega))
    hcfg.ext hcfg.rbar hcfg.red hK huniq (hcfg.centralizer_eq_bot hK huniq hcent hZ) hZ e

theorem d1CaseThreeA15At3_of (hData : StmtA15Data3 G) (hA : StmtA15BlockOrbit)
    (hB : StmtA15NoBlockOrbit) : D1CaseThreeA3pAt3 G (· = 5) := by
  intro p _ P M H R Rbar hcfg hp5 K hK huniq hnc hcent hKD hZ e
  subst hp5
  obtain ⟨c, σ, τ, hD⟩ := hData P M H R Rbar hcfg K hK huniq hcent hZ e
  refine hB hD fun L hL => ?_
  have hYn : H ⊓ M ≤ Subgroup.normalizer (((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L : Subgroup G) :
      Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases hD.surv.normal_dichotomy _ inf_le_left hYn with hle | hRle
  · exact hle
  · exact (hA hD L hL (hRle.trans inf_le_right)).elim

theorem d1CaseThreeA15At3_closed (hL : KFactA15Local) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hα : KFactThreeOrFiveDvd) (hS : CatalogOuterSolvable)
    (he : KFactBlockFiveNoncyclic) (hf : KFactBlockThreeFives) :
    D1CaseThreeA3pAt3 G (· = 5) :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  d1CaseThreeA15At3_of (stmtA15Data3_of hL)
    (stmtA15BlockOrbit_of hB3 stmtBlockInnerNormalizer_of h84 h85 h86 hD2 he hf)
    (stmtA15NoBlockOrbit_of hB3 stmtBlockInnerNormalizer_of h84 h86 hD2 hα hS)

end CFSG.LocalAnalysis.RankThreeTheoremC
