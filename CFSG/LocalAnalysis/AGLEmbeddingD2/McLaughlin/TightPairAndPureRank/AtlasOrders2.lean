module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeRank
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
public import CFSG.GH74.KGroups.PSLN
public import CFSG.RankThree.PartTwo.Census.Classical.EvenLinear

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem card_of_isUThreeThree {X : Type} [Group X] (h : IsUThreeThree X) :
    Nat.card X = 6048 :=
  card_of_isSmallUnitary_three (isSmallUnitary_three_of_isUThreeThree h)

theorem card_of_isL5Two {X : Type} [Group X] (h : IsL5Two X) : Nat.card X = 9999360 := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq2, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .A 4 q := hd
  subst hd'
  have hp : q.p = 2 ∧ q.exponent = 1 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hq2, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
    have h2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
    have hpow : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]; exact hq2
    rw [h2] at hpow
    exact ⟨h2, (Nat.prime_two.pow_eq_iff.mp hpow).2⟩
  have hmod := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA 4 q hv e
  rw [hp.1, hp.2] at hmod
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (GaloisField 2 1) := inferInstance
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := GaloisField 2 1) 5 2 1
    (by norm_num) (by rw [GaloisField.card 2 1 one_ne_zero, pow_one]) hmod
  have e2 := CFSG.RankThree.PartTwo.Sec4.Census.pslEquivProjSL 5 (GaloisField 2 1)
  have e3 := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL (n := 5) (by norm_num)
  rw [Nat.card_congr (e1.trans (e2.trans e3.symm)).toEquiv,
    CFSG.RankThree.PartTwo.Census.card_SL_five_two]

end CFSG.AGLEmbeddingD2.McLaughlin
