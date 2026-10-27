module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

@[expose] def IsSmallAltOrL2 (Y : Type) [Group Y] : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel Y .PSL 2 p f

@[expose] def CFSmallInv : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSmallAltOrL2 Y →
    ∀ s t : Y, orderOf s = 2 → orderOf t = 2 → ∃ g : Y, g⁻¹ * s * g = t

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CFAutSmallCommutator : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), IsSmallAltOrL2 (OddBar h.J) →
    center (OddBar h.J) = ⊥ →
    ∃ d ∈ h.D, (∀ s ∈ h.S, s * d * s⁻¹ ∈ zpowers d) ∧ ⁅h.S, h.S⁆ ≤ zpowers d ⊔ h.P

@[expose] def CFAutSmallQuotient : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), IsSmallAltOrL2 (OddBar h.J) →
    center (OddBar h.J) = ⊥ →
    ∃ (m : ℕ) (f : ↥h.S →* Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m))),
      f.ker = (h.D ⊔ h.P).subgroupOf h.S

end CFSG.ComponentClassification.GSThmB
