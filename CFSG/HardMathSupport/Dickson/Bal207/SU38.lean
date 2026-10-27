module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Frame
public import CFSG.HardMathSupport.Dickson.Bal207.SU38G2
public import CFSG.HardMathSupport.Dickson.Bal207.SU38Exc

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

section Main

set_option linter.unusedSectionVars false


theorem bal207PlusSmallSU38_of_frames {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    (hF : SU38ClassicalFrame G) : Bal207PlusSmallSU38 G := by
  obtain ⟨hSp, hUni, hOrth, hD4⟩ := hF
  intro X _ _ hX K B A ctx hIH a haA ha1 J hJ hSU hBJ
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  obtain ⟨d, ⟨e⟩, hd⟩ := ctx.hyp
  rcases hd with ⟨hdi, hcond⟩ | ⟨-, hD, hno⟩
  · by_cases hs : IsSpIdx d.1
    · exact isStronglyLocallyOneBalanced_of_rankThree_or_toral a hperf hSU
        (hSp X hX K B A ctx ⟨d, ⟨hdi, hs⟩, ⟨e⟩⟩ hIH a haA ha1 J hJ hSU hBJ)
    by_cases hu : IsUniIdx d.1
    · exact isStronglyLocallyOneBalanced_of_rankThree_or_toral a hperf hSU
        (hUni X hX K B A ctx ⟨d, ⟨hdi, hu⟩, ⟨e⟩⟩ hIH a haA ha1 J hJ hSU hBJ)
    by_cases ho : IsOrthIdx d.1
    · exact isStronglyLocallyOneBalanced_of_rankThree_or_toral a hperf hSU
        (hOrth X hX K B A ctx ⟨d, ⟨hdi, ho⟩, ⟨e⟩⟩ hIH a haA ha1 J hJ hSU hBJ)
    rcases exc_cases_of_bal207Index hdi hs hu ho with hG2 | h | h | h | h
    · exact isStronglyLocallyOneBalanced_of_g28 ctx ⟨d, hG2, ⟨e⟩⟩ (hcond hG2) hJ hBJ
    · exact (false_of_isSU38Comp_of_exc hJK hSU (Or.inl h) ⟨e⟩).elim
    · exact (false_of_isSU38Comp_of_exc hJK hSU (Or.inr (Or.inl h)) ⟨e⟩).elim
    · exact (false_of_isSU38Comp_of_exc hJK hSU (Or.inr (Or.inr (Or.inl h))) ⟨e⟩).elim
    · exact (false_of_isSU38Comp_of_exc hJK hSU (Or.inr (Or.inr (Or.inr h))) ⟨e⟩).elim
  · exact isStronglyLocallyOneBalanced_of_rankThree_or_toral a hperf hSU
      (hD4 X hX K B A ctx ⟨d, hD, ⟨e⟩⟩ hno hIH a haA ha1 J hJ hSU hBJ)

end Main

end CFSG.HardMathSupport.Dickson.Bal207

end
