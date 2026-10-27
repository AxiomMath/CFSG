module

public import CFSG.ClassicalInvolution.Q3.Q3VRowFin
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3ZFrbFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution CFSG.Open

theorem chainPiece3Sp_two_of_c3ChainInput (h : Q3Z.C3ChainInput) : ChainPiece3Sp 2 := by
  intro G _ _ _ hnab K z hR hshape hO3
  obtain ⟨U, hU, hcomm, hA, hB⟩ := h G hnab K z hR hshape hO3
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    have hi : i = 0 := by ext; simp; have := j.isLt; omega
    have hj : j = 2 := by ext; simp; have := j.isLt; omega
    subst hi hj
    exact hcomm a ha b hb
  · intro i j hij hj
    have hi : i = 0 := by ext; simp; have := j.isLt; omega
    have hj' : j = 1 := by ext; simp; have := j.isLt; omega
    subst hi hj'
    exact hA
  · intro i j hi hj
    have hi' : i = 2 := by ext; simp; have := i.isLt; omega
    have hj' : j = 1 := by ext; simp; have := j.isLt; omega
    subst hi' hj'
    exact hB

theorem piece3Sp2_of_collapse (h3 : Q3W.OddThreeFreeInput) (hchain : Q3Z.C3ChainInput)
    (hC : Q3Z.V6Collapse) : Q3W.Piece3Sp2 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  have hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  exact Or.inl (oddLieType_of_spChain3 le_rfl (weakCT3SpHyp_of_collapse hC le_rfl) hnab hR hshape
    hO3 (chainPiece3Sp_two_of_c3ChainInput hchain G hnab K z hR hshape hO3))

end CFSG.ClassicalInvolution.Q3.Q3V
