module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClVacuous
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClSmall

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddA6Shape_all
    (hPSL : OddA6Shape .PSL) (hPSU : OddA6Shape .PSU) (hPSp : OddA6Shape .PSp)
    (hOdd : OddA6Shape .POmegaOdd) (hPlus : OddA6Shape .POmegaPlus)
    (hMinus : OddA6Shape .POmegaMinus) (hG2 : OddA6Shape .G2) (hF4 : OddA6Shape .F4)
    (hE6 : OddA6Shape .E6) (hE7 : OddA6Shape .E7) (hE8 : OddA6Shape .E8)
    (htE6 : OddA6Shape .twistedE6) (htri : OddA6Shape .trialityD4)
    (htG2 : OddA6Shape .twistedG2) : ∀ t, OddA6Shape t := by
  intro t
  cases t <;> first
    | exact hPSL | exact hPSU | exact hPSp | exact hOdd | exact hPlus | exact hMinus
    | exact hG2 | exact hF4 | exact hE6 | exact hE7 | exact hE8 | exact htE6 | exact htri
    | exact htG2 | exact oddA6Shape_twistedB2 | exact oddA6Shape_twistedF4
    | exact oddA6Shape_Tits

theorem oddA6Small_all
    (hPSL : OddA6Small .PSL) (hPSU : OddA6Small .PSU) (hPSp : OddA6Small .PSp)
    (hOdd : OddA6Small .POmegaOdd) (hMinus : OddA6Small .POmegaMinus) : ∀ t, OddA6Small t := by
  intro t
  cases t <;> first
    | exact hPSL | exact hPSU | exact hPSp | exact hOdd | exact hMinus
    | exact oddA6Small_POmegaPlus | exact oddA6Small_G2 | exact oddA6Small_F4
    | exact oddA6Small_E6 | exact oddA6Small_E7 | exact oddA6Small_E8
    | exact oddA6Small_twistedE6 | exact oddA6Small_trialityD4 | exact oddA6Small_twistedG2
    | exact oddA6Small_twistedB2 | exact oddA6Small_twistedF4 | exact oddA6Small_Tits

end CFSG.ComponentClassification.CatFC
