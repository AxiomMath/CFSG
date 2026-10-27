module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Assembly.Dichotomy
open scoped commutatorElement

@[expose] def SmallTypeCBaseS (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G → CFSG.ClassicalInvolution.DeltaConnected K →
      ¬ BootData p f (conjClass K) → ¬ A2Configuration z K →
      ∀ (Kd : Fin 3 → Subgroup G) (zd t : Fin 3 → G),
        (∀ i, Kd i ∈ conjClass K ∧ IsClassicalMember p f (Kd i) (zd i)) →
        (∀ i j, i ≠ j → Commutes (Kd i) (Kd j)) → zd 0 * zd 1 * zd 2 = 1 →
        (∀ i, t i ∈ Kd i ∧ t i * t i = zd i ∧ orderOf (t i) = 4) →
        ∀ A : Subgroup G, A = Subgroup.closure {zd 0, zd 1, t 0 * t 1 * t 2} →
          CFSG.Open.IsElemAbelian 2 A → Nat.card A = 8 →
          ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ∉ Subgroup.closure {zd 0, zd 1} →
            ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b

end CFSG.ClassicalInvolution.Generic.CoreAssembly
