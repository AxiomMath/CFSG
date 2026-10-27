module

public import CFSG.Monster.B.Pinned.Primes.FiveWords

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Pinned

@[expose] def BabyFiveBPureFact : Prop :=
  ∀ F : Subgroup NativeSporadic.B, F ≤ PFive → zFive ∈ F → IsElemAbelian 5 F →
    Nat.card F = 5 ^ 2 →
    (∀ f ∈ F, f ≠ 1 → ∃ (c : ℕ) (g : NativeSporadic.B), g * zFive ^ c * g⁻¹ = f) →
    ∀ W : Subgroup NativeSporadic.B, IsElemAbelian 2 W → Nat.card W = 2 ^ 4 →
      F ≤ Subgroup.centralizer (W : Set NativeSporadic.B) → False

end CFSG.LocalAnalysis.GLTheoremA.H1017
