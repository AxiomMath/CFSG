module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIB
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCRee
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL28
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL34
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.SporadicM11

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)


theorem centralizerHasPElementOutside_three_of_nineFourListGroup {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hF : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup 3
      ↥(CFSG.generalizedFitting X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded 3 N) :
    CentralizerHasPElementOutside 3 N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  haveI : (CFSG.generalizedFitting X).Normal := hKn
  obtain ⟨-, i, hi, ⟨e⟩⟩ := hF
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ =>
    rcases hi with ⟨-, rfl⟩ | ⟨h5, -⟩
    ·
      have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
      have hcard : Fintype.card (GaloisField 3 2) = 9 := by
        rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
        norm_num
      obtain ⟨f⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism _ hcard
      exact (SEFive.good_psl2GF (p := 3) (n := 2) (by norm_num) (by norm_num) hO hN
        (e.trans f.symm)).2
    · omega
  | sporadic s =>
    rcases hi with ⟨-, rfl⟩ | ⟨h5, -⟩ | ⟨h11, -⟩
    ·
      exact (oc_of_gls3ConclusionPlus hO h2 hN fun P hP hΓ =>
        gls3ConclusionPlus_M11 hKn ⟨e⟩ hKC P hP hΓ).2
    · omega
    · omega
  | lie d =>
    rcases hi with ⟨q, hqp, hq2, hd⟩ | ⟨q, hqp, hd⟩ | ⟨-, m, hm⟩ |
      ⟨-, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩⟩ | ⟨h35, -⟩
    ·
      obtain ⟨f⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
        (p := 3) (n := q.exponent) (d := d) ⟨q, hd, hqp, rfl⟩
      exact (SEFive.good_psl2GF (p := 3) (n := q.exponent) (by norm_num) (by omega) hO hN
        (e.trans f)).2
    ·
      exact (SEFive.good_unitary (p := 3) (d := d) ⟨q, hqp, hd⟩ hO hN e).2
    ·
      obtain ⟨d1, hv⟩ := d
      change d1 = .reeG2 m at hm
      subst hm
      exact (good_of_isoLie_reeG2 hO hN ⟨hv, ⟨e⟩⟩).2
    ·
      exact (oc_of_gls3ConclusionPlus hO h2 hN fun P hP _ =>
        gls3ConclusionPlus_lie_L28 d q hq2 hq3 hd hKn ⟨e⟩ hKC P hP).2
    ·
      exact (oc_of_gls3ConclusionPlus hO h2 hN fun P _ hΓ =>
        gls3ConclusionPlus_lie_L34 d q hq2 hq3 hd hKn ⟨e⟩ hKC P hΓ).2
    · omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive
