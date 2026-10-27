module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenOrthMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClFam
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClSp
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcSmall
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcTwisted
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29DataSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFull

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem crossAtOn_of_forall_crossAtPrime {d : TauCeti.ValidLieTypeIndex} {S : ℕ → Prop}
    (h : ∀ p, S p → CrossAtPrime d p) : CrossAtOn d S :=
  ⟨fun p hp hp5 hS hdp L _ _ hs he hl h2 => (h p hS hp hp5 hdp).1 L hs he hl h2,
    fun p hp hp5 hS hdp L _ _ hs he hl h3 y hy => (h p hS hp hp5 hdp).2 L hs he hl h3 y hy⟩

section KD29Cross

theorem kd29Cross_of_e7_e8 (h7 : CrossE7SevenSplit) (h8 : CrossE8FiveFour) : KD29Cross := by
  refine kd29Cross_reduced_of_bcd_even crossFamUnitaryLarge ?_ ?_ ?_ ?_
    crossFamBSpLarge crossFamBOrthEvenLarge crossFamCLarge crossFamDEvenLarge crossFamTwistedDEvenLarge
    (crossFamE6_of_five crossFamE6Five_holds)
    (crossFamTwistedE6_of_five crossFamTwistedE6Five_holds)
    (crossFamE7_of_small (crossFamE7Small_of_split h7))
    (crossFamE8_of_small (crossFamE8Small_of_four h8)) crossSylowAbelianF4_holds
    crossSylowAbelianG2_holds crossSylowAbelianTrialityD4_holds crossSylowAbelianReeG2_holds
    crossSylowAbelianReeF4_holds
  · intro r q hv
    refine crossAtOn_of_forall_crossAtPrime fun p hrp => ?_
    have hr2 : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      exact crossAtPrime_B2 hv
    · by_cases hq : q.p = 2
      · exact crossAtPrime_B_even_of_lt hv hq hr3 hrp
      · exact crossAtPrime_B_odd_of_lt hv hq hr3 hrp
  · exact fun r q hv => crossAtOn_of_forall_crossAtPrime fun p hrp => crossAtPrime_C_of_lt hv hrp
  · exact fun r q hv => crossAtOn_of_forall_crossAtPrime fun p hrp => crossAtPrime_D_of_lt hv hrp
  · exact fun r q hv =>
      crossAtOn_of_forall_crossAtPrime fun p hrp => crossAtPrime_twistedD_of_lt hv hrp

end KD29Cross

section YS02

theorem invariantTwoSylowOfD1Rank4_of_e7_e8 (h7 : CrossE7SevenSplit) (h8 : CrossE8FiveFour) :
    InvariantTwoSylowOfD1Rank4 := invariantTwoSylowOfD1Rank4_of_cross (kd29Cross_of_e7_e8 h7 h8) fun _ hq hq5 =>
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrained_odd hq (by omega)

end YS02

end CFSG.LocalAnalysis.RankFourTheoremC
