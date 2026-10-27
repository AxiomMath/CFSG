module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.AGLEmbedding.G28InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
import CFSG.LocalAnalysis.AGLEmbedding.G28Data
import CFSG.LocalAnalysis.AGLEmbedding.G28MSide
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtG28Data3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig3 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsGTwoEightIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) → ∃ z : G, D1G28Data P M H R z

theorem stmtG28Data3_of (hS' : KFactChevTwoSurvivorSchur) (hKF : KFactG28Local) :
    StmtG28Data3 G := by
  intro _ P M H R Rbar hcfg K hK huniq hcent d hd e
  obtain ⟨e₁⟩ := e
  have hZ : Subgroup.center K = ⊥ :=
    hS' K 3 d (Or.inr (Or.inr (Or.inl ⟨rfl, hd⟩))) hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK : K ≃* CatGroup d :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e₁
  exact exists_g28Data_of hKF hcfg.glob.toU.toAGLGlobal hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hd eK

theorem d1CaseThreeG28At3_of (hDat : StmtG28Data3 G) (hM : StmtG28MSide) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp3, hd'⟩ := hd
  subst hp3
  obtain ⟨z, hz⟩ := hDat P M H R Rbar hcfg K hK huniq hcent d hd' e
  exact hM hz

theorem d1CaseThreeG28At3_closed (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactG28Local)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hOut : KFactBlockThreeOut) (hSU : KFactBlockNoSU38) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  d1CaseThreeG28At3_of (stmtG28Data3_of hSchur hKF)
    (stmtG28MSide_of h84 h85 h86 h93 hD2 hB3 stmtBlockInnerNormalizer_of hOut hSU)

end CFSG.LocalAnalysis.RankThreeTheoremC
