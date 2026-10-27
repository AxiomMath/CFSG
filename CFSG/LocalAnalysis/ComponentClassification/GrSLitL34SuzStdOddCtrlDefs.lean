module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

@[expose] def SuzTwoBFusionGeneration : Prop :=
  ∀ (S : Type) [Group S], Blueprint.NativeSporadic.IsSporadic S .Suz →
    ∀ x : S, x * x = 1 → Nat.card (centralizer ({x} : Set S)) = 161280 →
      ∀ L : Subgroup S, L ≤ centralizer ({x} : Set S) → ⁅L, L⁆ = L → Nat.card L = 20160 →
        ∀ h ∈ L, h * h = 1 → h ≠ 1 →
          ∃ a : S, a * x * a⁻¹ = x * h ∧ L ⊔ L.map (MulAut.conj a).toMonoidHom = ⊤

end CFSG.ComponentClassification.GrSLit.L34Sec5S
