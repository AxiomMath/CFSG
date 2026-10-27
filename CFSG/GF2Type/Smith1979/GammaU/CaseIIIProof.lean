module

public import CFSG.GF2Type.Smith1979.GammaU.Dict5
public import CFSG.GF2Type.Smith1979.GammaU.ThetaTwo
public import CFSG.GF2Type.Smith1979.CaseIIIHyp10
public import CFSG.GF2Type.Smith1979.SixCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10 CFSG.GF2Type.Smith1980Orth

theorem caseIIIStmt :
    CaseIIIStmt := by
  intro I G _ _ _ _ S hw hirr hnoAll g H C hI hII
  obtain ⟨t, X⟩ := exists_hyp10 I hw hirr hnoAll H C hI hII
  obtain ⟨Xb, Yb, D, -⟩ := exists_dec108_of_width_six I X hw
  obtain ⟨θ, hθ, hθ1, hθ3, -, hfix, -⟩ := exists_theta I D
  have hP := noPGL25_of_width_six I hw hirr hnoAll g
  exact false_of_thetaInputs hw hirr H C (thetaInputs_of_dec108 I hw hP D hθ hθ1
    fun s hs hinv => finrank_Vt_le_two_of_inverts I hw hirr hnoAll H C hI hII hθ1 hθ3 hfix hs hinv)

end CFSG.GF2Type.Smith1979.GammaU.Dict
