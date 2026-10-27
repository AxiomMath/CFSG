module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIMemberQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIMemberLevi
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIMemberBar
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveLie
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeFive

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeUC.AGL81C CFSG.QuasithinUnique

private theorem not_hasE9_of_noElemNine {X : Type*} [Group X]
    (h : CFSG.Quasithin.F134.NoElemNine X) : ¬ CFSG.AGLEmbedding.BlockCyc.HasE9 X := by
  rintro ⟨E, hE, hcard⟩
  exact h E hcard hE.2

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


theorem nineThreeTwo_of_not_hasE9 {M S L : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hno : ¬ CFSG.AGLEmbedding.BlockCyc.HasE9 ↥(barM M L)) : NineThreeTwo M S L := by
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.asc81bNineThree_holds G M S L hK hA hL with
    h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact h2
  · rcases CFSG.AGLEmbedding.BlockCyc.lieFiveOrthogonal _ h3.2.1 with hE | hA5
    · exact absurd hE hno
    · exact absurd
        (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.kFactNineThreeThreeFive_proved
          G M S L hL h3 hA5) hX
  · exact absurd (CFSG.AGLEmbedding.BlockCyc.hasE9_of_nineThree_alt hL (Or.inl h4)) hno
  · exact absurd (CFSG.AGLEmbedding.BlockCyc.hasE9_of_nineThree_alt hL (Or.inr (Or.inl h5))) hno
  · exact absurd
      (CFSG.AGLEmbedding.BlockCyc.hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inl h6)))) hno
  · exact absurd
      (CFSG.AGLEmbedding.BlockCyc.hasE9_of_nineThree_alt hL
        (Or.inr (Or.inr (Or.inr (Or.inl h7))))) hno
  · exact absurd
      (CFSG.AGLEmbedding.BlockCyc.hasE9_of_nineThree_alt hL
        (Or.inr (Or.inr (Or.inr (Or.inr h8))))) hno

theorem exists_parabolic_of_isL3TwoPow
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) {n : ℕ}
    (hn : Odd n) (hL3 : IsL3TwoPow n (modTwoCore L)) :
    ∃ T J : Subgroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)),
      IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set _) ≤ J ∧
        J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤ ∧
        J = ((barM M (H ⊓ L)).subgroupOf (barM M L)).map
          (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have h85 : CFSG.AGLEmbedding.Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs
        CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved)
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hA : Asc81bHyp M (pCoreOf 2 H) := hphase.asc81bHyp
  have hLw : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hX : ¬ InClassXBlock L := (hphase.nineThree_not_one hK h85 hD2 hLw).1
  have hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
    hphase.not_isSylowTwoOf_inf hK h85 hD2 hLw
  have hno : ¬ CFSG.AGLEmbedding.BlockCyc.HasE9 ↥(barM M L) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
    obtain ⟨eB⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
      hLw.le hLw.toIsTwoPrimeComponent.inf_twoCore
    obtain ⟨e⟩ := hL3
    have hmodel : StatedClassicalModel ↥(barM M L) .PSL 3 2 n :=
      statedClassicalModel_psl_three_of_mulEquiv hn0 (eB.symm.trans e)
    exact not_hasE9_of_noElemNine (CFSG.Quasithin.F134.LieL3.noElemNine_of_odd hn hmodel)
  have h93 : NineThreeTwo M (pCoreOf 2 H) L :=
    nineThreeTwo_of_not_hasE9 hK hA hLw hX hno
  obtain ⟨-, T, J, hT, hle, hne, htop, hJ⟩ :=
    CFSG.AGLEmbedding.BlockCyc.nineThreeTwo_parabolic hA hLw hS h93
  refine ⟨T, J, hT, hle, hne, htop, ?_⟩
  rw [hphase.normalizer_twoCore_H] at hJ
  exact hJ

theorem twelveSixIMember_of_K
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) : TwelveSixIMember := by
  intro G _ _ M p Q H L n h hL hn hL3
  have hLw : IsWeakSBlock M (pCoreOf 2 H) L := hL
  obtain ⟨hZ, ⟨eY⟩⟩ := center_barM_eq_bot_and_psl hLw.toIsTwoPrimeComponent hL3
  obtain ⟨T, J, hT, hle, hne, htop, rfl⟩ :=
    exists_parabolic_of_isL3TwoPow h1 h2 h25 h hL hn hL3
  have hker : IsPGroup 2 (yHom (inf_le_right : H ⊓ L ≤ L) hLw.le).ker :=
    isPGroup_ker_yHom (inf_le_right : H ⊓ L ≤ L) hLw.le hZ
  have hcases : n = 1 ∨ 3 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    rcases k with - | k <;> omega
  rcases hcases with rfl | hn3
  · obtain ⟨e⟩ := quot_perm_three_of_parabolic eY hT hle hne htop
    refine cZero_eq_singleton_of_parabolic_one (yHom (inf_le_right : H ⊓ L ≤ L) hLw.le) hker ?_
    rw [range_yHom (inf_le_right : H ⊓ L ≤ L) hLw.le]
    exact e
  · obtain ⟨hTJ, hJ⟩ := perfectCore_isPSL_of_parabolic (by omega : 2 ≤ n) eY hT hle hne htop
    refine cZero_eq_singleton_of_parabolic (yHom (inf_le_right : H ⊓ L ≤ L) hLw.le)
      hker hT ?_ hn hn3 ?_
    · rwa [range_yHom (inf_le_right : H ⊓ L ≤ L) hLw.le]
    · rwa [range_yHom (inf_le_right : H ⊓ L ≤ L) hLw.le]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
