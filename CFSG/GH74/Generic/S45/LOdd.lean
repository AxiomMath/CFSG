module

public import CFSG.GH74.Generic.S45.LQSmall
public import CFSG.GH74.Generic.S45.LExcOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieReeCover
public import CFSG.GH74.Generic.S45.LSporCommon

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.ExcSelector

theorem odd_exc_false
    {S : Type} [Group S] {t : StatedLieTag} {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : ChevalleyExceptionalModel S t r f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : False := by
  have hya2 : ya ^ 2 = 1 := by rw [pow_two]; exact hQ.sq
  exact noSmallQ8Component_of_model_odd hr2 hmodel ya hya2 hQ.ne Lb hQ.isComponentOf_fixed
    hQ.smallQ8

theorem odd_twistedG2_false
    {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K} (hyp : Hyp1310 K y L) {f : ℕ}
    (hmodel : ReeTitsModel (K ⧸ center K) .twistedG2 3 f) : False := by
  have hKq : CFSG.Open.IsQuasisimple K := ⟨hyp.1.1.1.commutator_eq_top, hyp.1.1.2.1⟩
  have hz2 : IsPGroup 2 ↥(Subgroup.center K) := by
    have := hyp.data
    exact this.2.1
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.smallReeTwoMultiplierTrivial K hKq hz2 ⟨f, hmodel⟩
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact hyp.2.2.2.2.2.2.1 ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e
    (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [reeTitsTags], hmodel⟩)))⟩

end CFSG.GH74.Generic.S45
