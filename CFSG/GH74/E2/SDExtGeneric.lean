module

public import CFSG.GH74.E2.Ext2

public section

namespace CFSG.GH74.E2

namespace SDW

structure SDData (L : Type*) [Group L] where
  R : L
  S : L
  nf : L → ℕ × ℕ
  nf_spec : ∀ a : L, R ^ (nf a).1 * S ^ (nf a).2 = a
  hR8 : R ^ 8 = 1
  hR4 : R ^ 4 ≠ 1
  hSS : S * S = 1
  hS1 : S ≠ 1
  hSR : S * R * S⁻¹ = R ^ 3

namespace SDData

variable {L : Type*} [Group L] (D : SDData L)

@[expose] def ap (u v : L × L) (a : L) : L × L := u ^ (D.nf a).1 * v ^ (D.nf a).2

@[expose] def evA (h₁ h₂ h₃ h₄ w : L × L) : L × L := D.ap h₁ h₂ w.1 * D.ap h₃ h₄ w.2

@[expose] def gX1 : L × L := (D.R, 1)

@[expose] def gY1 : L × L := (D.S, 1)

@[expose] def gX2 : L × L := (1, D.R)

@[expose] def gY2 : L × L := (1, D.S)

end SDData

namespace SDData

variable {L : Type*} [Group L] (D : SDData L)

@[expose] def CFix (h₁ h₂ h₃ h₄ w : L × L) : Prop :=
  D.evA h₁ h₂ h₃ h₄ w = w ∧ D.evA h₁ h₂ h₃ h₄ h₁ = w * D.gX1 * w⁻¹ ∧
    D.evA h₁ h₂ h₃ h₄ h₂ = w * D.gY1 * w⁻¹ ∧ D.evA h₁ h₂ h₃ h₄ h₃ = w * D.gX2 * w⁻¹ ∧
      D.evA h₁ h₂ h₃ h₄ h₄ = w * D.gY2 * w⁻¹

end SDData

end SDW

end CFSG.GH74.E2
