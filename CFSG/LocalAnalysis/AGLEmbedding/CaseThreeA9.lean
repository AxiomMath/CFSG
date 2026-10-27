module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeAThreeP
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOne
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideWreath
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Data
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target
import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem stmtA9MSideGen_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (ha : KFactBlockCyclicThree)
    (hi : KFactBlockThreeOneOrbit) :
    ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G},
      D1A9DataCore P M H R X σ z →
        CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ ∨ R = (P : Subgroup G) := by
  intro G _ _ P M H R X σ z h
  by_cases hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥
  · have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
    obtain ⟨L, hL, hσL⟩ := h.exists_not_mem_normalizer hB3 h84 h85 h86 hD2 hi hO
    exact Or.inr (h.eq_sylow_of_not_mem_normalizer hB3 h84 h85 hD2 ha hO hL hσL)
  · exact Or.inl hO

theorem stmtA9MSide_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (ha : KFactBlockCyclicThree)
    (hi : KFactBlockThreeOneOrbit) : StmtA9MSide := by
  intro G _ _ P M H R X σ z h
  rcases stmtA9MSideGen_of h84 h85 h86 h93 hD2 hK2 hC3 hK5 ha hi h.toD1A9DataCore with h1 | hRP
  · exact h1
  · exfalso
    have h4 := h.four_le
    rw [← hRP] at h4
    have h5 := (pRank_mono 3 Nat.prime_three h.surv.ph3.le_inf).trans h.pRank_le
    omega

theorem d1CaseThreeA9_of (hData : StmtA9Data) (hSoc : @StmtA3pSocleData 3 ⟨Nat.prime_three⟩)
    (hT : @StmtA3pTarget 3 4 (3 ^ 4) ⟨Nat.prime_three⟩) (hE : KFactJStarElimA3p 3 (3 ^ 4))
    (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hM : StmtA9MSide) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : D1CaseThreeA9 := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq _ hcent _ hZ e
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨X, σ, z, hA⟩ := hData G P M H R Rbar hcfg K hK huniq hcent hZ e
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
    ⟨hcfg.ext, hcfg.glob, le_rfl, K, hKn, ⟨MulEquiv.refl _⟩, hC, (inf_eq_left.mpr hRK).symm⟩
  have hcompR : D1JCompetitorsOn (D1SocleConfig (↥K) 3 P M · R R) R R :=
    competitorsOn_socleConfig hTK hTcK (hE _ ⟨e₀⟩) hβ hP1L hP1A hP1S
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig (↥K) 3 P M H' R R)
    (fun H' h' => hSoc h' ⟨e₀⟩ hA.surv.le_R hA.elem hA.card_X) (hM hA)
    (competitorsOn_of_le hTK.simple hcompR hA.surv.le_R hA.surv.ne_bot) hS0

theorem d1CaseThreeA9_closed (hL : KFactA9Local) (hE : KFactJStarElimA3p 3 (3 ^ 4))
    (ha : KFactBlockCyclicThree) (hi : KFactBlockThreeOneOrbit) (hβ : KFactBeta)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hCGT : AschbacherLocalCGTBlock) : D1CaseThreeA9 :=
  d1CaseThreeA9_of (stmtA9Data_of hL) (stmtA3pSocleData_of (kFactA3pLocal_three_of hL))
    stmtA3pTarget_nine hE hβ hP1L hP1A hP1S
    (stmtA9MSide_of h84 h85 h86 h93 hD2 hK2 hC3 hK5 ha hi) h84 hCGT hD2

end CFSG.AGLEmbedding
