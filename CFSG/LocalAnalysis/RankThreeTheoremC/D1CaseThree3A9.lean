module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3JStar
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOne
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtA9MSide3 (G : Type) [Group G] [Finite G] : Prop :=
  evenRank G = 3 → 3 ∈ rankThreeSigmaA G →
    ∀ {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G}, IsTwoLocal M →
      D1A9DataCore P M H R X σ z → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem stmtA9MSide3_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hi : KFactBlockThreeOneOrbit) : StmtA9MSide3 G := by
  intro hrank h3 P M H R X σ z hM h hO
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  obtain ⟨L, hL, hσL⟩ := h.exists_not_mem_normalizer hB3 h84 h85 h86 hD2 hi hO
  exact false_of_not_mem_normalizer_of_pow_three3 hrank h3 hM hL.toIsTwoPrimeComponent
    (h.surv.ph3.le_M h.σ_mem) h.σ_pow hσL

theorem d1CaseThreeA9At3_of (hData : StmtA9Data3 G)
    (hSoc : @StmtA3pSocleData 3 ⟨Nat.prime_three⟩)
    (hT : @StmtA3pTarget 3 4 (3 ^ 4) ⟨Nat.prime_three⟩) (hE : KFactJStarElimA3p 3 (3 ^ 4))
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hM : StmtA9MSide3 G) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : D1CaseThreeA3pAt3 G (· = 3) := by
  intro p _ P M H R Rbar hcfg hp3 K hK huniq _ hcent _ hZ e
  subst hp3
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨X, σ, z, hA⟩ := hData P M H R Rbar hcfg K hK huniq hcent hZ e
  obtain ⟨e'⟩ := e
  have e₀ : K ≃* alternatingGroup (Fin (3 * 3)) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e'
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  obtain ⟨hTK, hTcK, hOutK⟩ := hT _ ⟨e₀⟩
  have hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤ K := by
    have : Finite (MulAut K) := MulEquiv.finite_left
    intro x hx
    rw [← hcfg.rbar] at hx
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem := mem_sup_centralizer_of_pow hp hOutK hxk
    rwa [hC, sup_bot_eq] at hmem
  have hS0 : D1SocleConfig (↥K) 3 P M H R R :=
    ⟨hcfg.ext, hcfg.glob.toU.toAGLGlobal, le_rfl, K, hKn, ⟨MulEquiv.refl _⟩, hC,
      (inf_eq_left.mpr hRK).symm⟩
  have hcompR : D1JCompetitorsOn (D1SocleConfig (↥K) 3 P M · R R) R R :=
    competitorsOn_socleConfig3 hTK hTcK (hE _ ⟨e₀⟩) hβ hP1L hP1A hP1S
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig (↥K) 3 P M H' R R)
    (fun H' h' => hSoc h' ⟨e₀⟩ hA.surv.le_R hA.elem hA.card_X)
    (hM hcfg.glob.rank hcfg.loc.sigma hcfg.loc.isCoreMaxLocal.1.1 hA)
    (competitorsOn_of_le hTK.simple hcompR hA.surv.le_R hA.surv.ne_bot) hS0

theorem d1CaseThreeA9At3_closed (hL : KFactA9Local) (hE : KFactJStarElimA3p 3 (3 ^ 4))
    (hi : KFactBlockThreeOneOrbit) (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hCGT : AschbacherLocalCGTBlock) :
    D1CaseThreeA3pAt3 G (· = 3) :=
  d1CaseThreeA9At3_of (stmtA9Data3_of hL) (stmtA3pSocleData_of (kFactA3pLocal_three_of hL))
    stmtA3pTarget_nine hE hβ hP1L hP1A hP1S
    (stmtA9MSide3_of h84 h85 h86 h93 hD2 hK2 hC3 hK5 hi) h84 hCGT hD2

end CFSG.LocalAnalysis.RankThreeTheoremC
