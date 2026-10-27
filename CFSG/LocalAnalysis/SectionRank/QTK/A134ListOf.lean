module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListAlt
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListOdd
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListEven
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSmall
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListU38
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListG2
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListD4
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListF4
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListTits
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListMat
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSporB
import CFSG.Quasithin.Background.A3FactsA134

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem a134Types_or_oddLocalWitness {S : Type} [Group S] [Finite S]
    (hlist : CFSG.Milestones.SQTKSimpleList S) :
    CFSG.Quasithin.A134Types S ∨ OddLocalWitness S := by
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ | (⟨f, hf⟩ | htits) |
    ⟨n, hn, hmodel⟩ | ⟨s, hs, ⟨e⟩⟩
  · rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 by omega) with rfl | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨5, 1, Nat.prime_five, by norm_num, le_rfl,
        by norm_num, CFSG.Quasithin.A3Facts.statedPSL_two_five_of_alt_five e⟩)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_alternating h))
  · exact a134Types_or_oddLocalWitness_odd hp hp2 hodd
  · rcases hf with ⟨hf2, hmodel⟩ | ⟨hf1, hmodel⟩ | ⟨hf2, hmodel⟩ | ⟨hf2, hmodel⟩ | ⟨hf2, hmodel⟩ |
      ⟨hf1, hmodel⟩ | ⟨-, -, hmodel⟩ | ⟨-, -, hmodel⟩
    · exact Or.inl (Or.inl ⟨f, hmodel⟩)
    · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨7, 1, by norm_num, by norm_num, le_rfl,
          by norm_num, CFSG.Quasithin.A3Facts.statedPSL_two_seven_of_three_two hmodel⟩)))
      · exact Or.inr (oddLocalWitness_psl_three_even hf2 hmodel)
    · by_cases hf3 : f = 3
      · subst hf3
        exact Or.inr (oddLocalWitness_psu_three_eight hmodel)
      · exact Or.inr (oddLocalWitness_psu_three_even hf2 hf3 hmodel)
    · exact Or.inr (oddLocalWitness_psp_two_even hf2 hmodel)
    · exact Or.inr (oddLocalWitness_G2 hf2 hmodel)
    · exact Or.inr (oddLocalWitness_trialityD4 hf1 hmodel)
    · exact Or.inr (oddLocalWitness_twistedF4 hmodel)
    · exact Or.inl (Or.inr (Or.inl ⟨f, hmodel⟩))
  · exact Or.inr (oddLocalWitness_tits htits)
  · exact Or.inr (oddLocalWitness_psl_four_five hn hmodel)
  · have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv S e.toEquiv
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_mathieu (Or.inl rfl)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_mathieu (by simp)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_mathieu (by simp)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_mathieu (by simp)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_mathieu (by simp)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_matrixSporadic (Or.inl rfl)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_matrixSporadic (by simp)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_matrixSporadic (by simp)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_matrixSporadic (by simp)))
    · exact Or.inr (OddLocalWitness.of_mulEquiv e (oddLocalWitness_matrixSporadic (by simp)))

theorem qtA134List : QTA134List := by
  intro S _ _ _ _ hlist hbound
  rcases a134Types_or_oddLocalWitness hlist with h | h
  · exact h
  · exact absurd hbound (not_bound_of_oddLocalWitness h)

end CFSG.SectionRank.QTK
