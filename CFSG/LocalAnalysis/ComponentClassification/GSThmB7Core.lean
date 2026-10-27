module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

@[expose] def Lemma61Case2 (h : Hyp52 X) (y b : X) : Prop :=
  orderOf b = 2 ∧ h.x⁻¹ * b * h.x = h.a * b ∧ h.upperP 2 = closure {h.a, b} ∧
    b ∈ h.B ⊓ conjugate h.B y ∧ y * b = b * y ∧ ⁅h.B, zpowers y⁆ ≤ closure {h.a, b} ∧
    ((centralizer ({b} : Set X)).subgroupOf h.S).index = 2

end Seven

end CFSG.ComponentClassification.GSThmB
