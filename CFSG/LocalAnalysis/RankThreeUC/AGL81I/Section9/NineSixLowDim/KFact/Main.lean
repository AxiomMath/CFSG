module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Main
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.AltSeven

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

@[expose] def PSpFourPPrimeGen : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ q →
    PPrimeGenAt p (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q)))

theorem kFactLowDimPPrimeGen_of (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    (hA6 : CFSG.RankThree.PartOne.N1322.KF1322ThreeA6Norm) (hSp : PSpFourPPrimeGen) :
    KFactLowDimPPrimeGen := by
  intro q _ p hp hq2 hp2 hqp S _ _ _ _ hS E hE hcard hS6
  have hpq : p ≠ q := Ne.symm hqp
  suffices h : PPrimeGenAt p S from h E hE hcard
  unfold IsLowDimSimpleSection at hS
  rcases hS with e | e | e | e | e | e | e | e
  · exact .of_mulEquiv e.some (.of_noElemSq (noElemSq_psl_two q hq2 hp hp2 hpq))
  · exact .of_mulEquiv e.some (pPrimeGenAt_psl_three hB hA6 q hq2 hp hp2 hpq)
  · exact .of_mulEquiv e.some (hSp q hq2 p hp hp2 hpq)
  · exact .of_mulEquiv e.some (.of_noElemSq (noElemSq_psl_two_sq q hq2 hp hp2 hpq))
  · exact .of_mulEquiv e.some (.of_noElemSq (noElemSq_alt_five hp hp2))
  · exact .of_mulEquiv e.some (.of_noElemSq (noElemSq_alt_six hp hp2 fun h3 => hS6 ⟨h3, e⟩))
  · by_cases hp3 : p = 3
    · subst hp3
      exact .of_mulEquiv e.some pPrimeGenAt_three_alt_seven
    · have h5 : 5 ≤ p := by
        have := hp.two_le
        by_contra h
        push Not at h
        interval_cases p <;> first | omega | norm_num at hp
      exact .of_mulEquiv e.some (.of_noElemSq (noElemSq_alt_seven hp h5))
  · exact .of_mulEquiv e.some (.of_noElemSq (noElemSq_gl_three_two hp hp2))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
