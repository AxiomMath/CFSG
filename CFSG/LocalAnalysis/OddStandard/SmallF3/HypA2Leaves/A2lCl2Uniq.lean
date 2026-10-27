module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqCross
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDigit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqFinal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqG2

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.CatLeaf

theorem cl24_lt_false (hO : LieOrderFormulasInput) {Q : Type} [Group Q] {τ τ' : StatedLieTag}
    {n n' j d : ℕ} (h : LieModel Q τ n 3 j) (h' : LieModel Q τ' n' 3 d) (hjd : j < d) :
    False := by
  obtain ⟨hN, hC⟩ := cl24_cross hO h h'
  have hE := cl24_E_eq h.admissible h'.admissible hC
  by_cases hτ : τ = .twistedG2
  · subst hτ
    obtain rfl : n = 0 := h.admissible.2.2.1
    exact cl24_twistedG2_small h.admissible h'.admissible hjd hN hE hC
  by_cases hτ' : τ' = .twistedG2
  · subst hτ'
    obtain rfl : n' = 0 := h'.admissible.2.2.1
    exact cl24_twistedG2_large h.admissible h'.admissible hjd hN hE
  · exact cl24_final h.admissible h'.admissible hjd hτ hN hE
      (cl24_digit h.admissible h'.admissible hjd hτ hτ' hC)

theorem a2l_cl2_fieldUnique3 (hO : LieOrderFormulasInput) : Cl24FieldUnique3 := by
  intro Q _ τ τ' n n' j d h h'
  rcases lt_trichotomy j d with hlt | heq | hgt
  · exact (cl24_lt_false hO h h' hlt).elim
  · exact heq
  · exact (cl24_lt_false hO h' h hgt).elim

end CFSG.OddStandard.SmallF3.HypA2Leaves
