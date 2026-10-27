module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueSetup

public section

namespace CFSG.Semidihedral.UnitaryDValue

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

@[expose] def GWStep : Prop :=
  ∀ w ∈ D.W, w ≠ 1 → (∃ k : ℕ, orderOf w = 3 ^ k) → D.t * w = w * D.t →
    Subgroup.centralizer {w} ≤ Subgroup.normalizer (D.T : Set G) ∨
      ∀ c ∈ D.C, (∃ k : ℕ, orderOf c = 3 ^ k) →
        D.t * (D.t * c * D.t⁻¹ * c⁻¹) = (D.t * c * D.t⁻¹ * c⁻¹) * D.t

end DValueData

end CFSG.Semidihedral.UnitaryDValue
