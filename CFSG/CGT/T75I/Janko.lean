module

public import CFSG.CGT.Timmesfeld75.Sec5OutBar

public section

namespace CFSG.CGT.T75I

open CFSG.CGT.Timmesfeld75

@[expose] def JankoMathieuInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T : Subgroup G, IsWC T → Nat.card T = 16 →
      (∀ d ∈ T, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)) →
      Subgroup.centralizer (T : Set G) = T →
      (∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y) →
      (Nonempty (NQuot T ≃* alternatingGroup (Fin 6)) →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M22) ∧
      (Nonempty (NQuot T ≃* alternatingGroup (Fin 7)) →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M23)

end CFSG.CGT.T75I
