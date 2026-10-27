module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.RankOneOut.PSLThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockCenterPSLThree
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


theorem hL3_of_blocks
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H)
    (hk1 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank 3 (CFSG.AGLEmbedding.barM M L) ≤ 1) :
    ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L) := by
  intro L hL
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have hBHS := CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have h85 := CFSG.AGLEmbedding.asc81bEightFive_of_factorization
    (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs hBHS)
  have hD2 := noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hA : CFSG.AGLEmbedding.Asc81bHyp M (pCoreOf 2 H) := hphase.asc81bHyp
  have hLw : CFSG.AGLEmbedding.IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hX := (hphase.nineThree_not_one hK h85 hD2 hLw).1
  have hS := hphase.not_isSylowTwoOf_inf hK h85 hD2 hLw
  have hno : ¬ CFSG.AGLEmbedding.BlockCyc.HasE9 ↥(CFSG.AGLEmbedding.barM M L) := by
    rintro ⟨E, hE, hcard⟩
    have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.AGLEmbedding.barM M L)) :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤) (E := E) le_top hE
        (k := 2) (by rw [hcard])
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (CFSG.AGLEmbedding.barM M L)] at h2
    have hk1L := hk1 L hL
    omega
  obtain ⟨f, hf, hm⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.exists_psl_three_of_not_hasE9
      hK hA hLw hX hS hno
  have hZ : Subgroup.center ↥(CFSG.AGLEmbedding.barM M L) = ⊥ :=
    center_barM_eq_bot_of_psl_three_odd hLw.toIsTwoPrimeComponent hf hm
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
    (↥(CFSG.AGLEmbedding.barM M L) ⧸
      Subgroup.center ↥(CFSG.AGLEmbedding.barM M L)) 3 2 f hm
  obtain ⟨eB⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hLw.le hLw.toIsTwoPrimeComponent.inf_twoCore
  let eZ : ↥(CFSG.AGLEmbedding.barM M L) ⧸
      Subgroup.center ↥(CFSG.AGLEmbedding.barM M L) ≃* ↥(CFSG.AGLEmbedding.barM M L) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨f, hf, ?_⟩
  unfold IsL3TwoPow
  exact ⟨eB.trans (eZ.symm.trans e₁)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
