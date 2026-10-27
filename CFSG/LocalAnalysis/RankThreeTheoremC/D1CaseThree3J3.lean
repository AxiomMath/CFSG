module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3JStar
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3
import CFSG.LocalAnalysis.AGLEmbedding.J3Data
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeJ3
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem D1ComponentConfig3.d1J3Config {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hcfg : D1ComponentConfig3 3 P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype)
    (hZ : Subgroup.center K = ⊥)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    D1J3Config P M H R := by
  obtain ⟨e⟩ := e
  exact ⟨hcfg.ext, hcfg.glob.toU.toAGLGlobal, K, normal_of_forall_isComponentOf_eq hK huniq,
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩,
    hcfg.centralizer_eq_bot hK huniq hcent hZ⟩

theorem d1CaseThreeJ33_of (hD : StmtJ3Data) (hM : StmtJ3MSide) (hOR : KFactJ3OuterRank)
    (hT : StmtJ3Target) (hTc : StmtJ3TargetCard) (hE : KFactJStarElimJ3)
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) : D1CaseThreeJ33 G := by
  intro P M H R Rbar hcfg K hK huniq _ hcent _ hZ e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact false_of_j3_of_competitors hD hM hOR hT h84 hCGT hD2 hcfg.glob.toU.toAGLGlobal hcfg.ext
    hcfg.rbar hK huniq (hcfg.centralizer_eq_bot hK huniq hcent hZ) hZ e
    (hcfg.d1J3Config hK huniq hcent hZ e) fun e₀ =>
      competitorsOn_socleConfig3 (hT _ ⟨e₀⟩) (hTc _ ⟨e₀⟩) (hE _ ⟨e₀⟩) hβ hP1L hP1A hP1S

theorem d1CaseThreeJ33_closed (hS : KFactJ3Sylow) (hO : KFactJ3OuterInvolution)
    (hOR : KFactJ3OuterRank) (hT : StmtJ3Target) (hTc : StmtJ3TargetCard)
    (hE : KFactJStarElimJ3) (hBlk : KFactBlockThreeSolvable) (hβ : KFactBetaRank2)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hCGT : AschbacherLocalCGTBlock) : D1CaseThreeJ33 G :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  d1CaseThreeJ33_of (stmtJ3Data_of hS hO hOR)
    (stmtJ3MSide_of h84 h85 h86 hD2 hB3 hBlk stmtBlockInnerNormalizer_of) hOR hT hTc hE hβ
    hP1L hP1A hP1S h84 hCGT hD2

end CFSG.LocalAnalysis.RankThreeTheoremC
