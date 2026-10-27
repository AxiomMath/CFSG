module

public import CFSG.GH74.KGroups.L27Inputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.GH74.KGroups Equiv

@[expose] def l27OuterOK : Bool :=
  (elemsT L27.QA).all fun r => !(decide (r * r = 1)) || decide (r = 1) || L27.QP.sift r 0 ||
    (((elemsT L27.QP).any fun y => decide (y ^ 3 = 1) && !(decide (y = 1)) &&
        decide (y * r = r * y) && (elemsT L27.QP).all fun g => !(decide (g * r = r * g)) ||
          decide (g * y * g⁻¹ = y) || decide (g * y * g⁻¹ = y * y)) &&
      (elemsT L27.QA).all fun y => !(decide (y * r = r * y)) || !(decide (y ^ 16 = 1)) ||
        decide (y * y = 1))

@[expose] def a5OuterOK : Bool :=
  decide (∀ r : Perm (Fin 5), Perm.sign r = -1 → r * r = 1 →
    (∃ y : Perm (Fin 5), Perm.sign y = 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ y * r = r * y ∧
      ∀ g : Perm (Fin 5), Perm.sign g = 1 → g * r = r * g →
        g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y * y) ∧
    ∀ y : Perm (Fin 5), y * r = r * y → y ^ 16 = 1 → y * y = 1)

@[noinline, expose] def l2OuterOK : Bool := l27OuterOK && a5OuterOK

end CFSG.ComponentClassification.GrSLit.L34Facts
