module

public import CFSG.GF2Type.Smith1979.W4AsLin
public import CFSG.GF2Type.Smith1979.W4AsMain
public import CFSG.GF2Type.Smith1979.W4AsOmega83

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open CFSG.Yardstones.M3aba7dc4b8a8

section BetaFalseAll

theorem betaFalse_of_linGen4All (hLin : LinGen4All) : BetaFalse := by
  intro G _ _ _ z hset S hSz hSQ hw hno hirr hnwc
  have I : Smith1980Orth.TimInputs := Smith1980Orth.timInputs_holds
  obtain ⟨g, haQ, hne⟩ :=
    CFSG.LargeExtraspecial.DW.W4Rank.exists_conj_of_not_weaklyClosed S hSz hSQ hnwc
  obtain ⟨H, C⟩ := W4O83.hyp4_cons311_of_w4 I.hTI hw hno hirr g haQ hne
  exact false_of_gen4 hset S hSz hSQ hw hno I.hTI hirr hnwc
    (gen4_of_beta_all I hLin hw hno H C hirr)

theorem betaFalse_of_layerSurvivors (hL : LayerSurvivorsW4) : BetaFalse :=
  betaFalse_of_linGen4All
    (linGen4_of_s11_1StmtW4 (s11_1Stmt_w4 hL) Smith1980Orth.timInputs_holds)

end BetaFalseAll

section WidthFourAll

theorem widthFourIrreducibleCase_of_layerSurvivors (hL : LayerSurvivorsW4) :
    CFSG.Yardstones.M3aba7dc4b8a8.WidthFourIrreducibleCase :=
  widthFourIrreducibleCase_of_betaFalse (betaFalse_of_layerSurvivors hL)

end WidthFourAll

end CFSG.GF2Type.Smith1979.W4As
