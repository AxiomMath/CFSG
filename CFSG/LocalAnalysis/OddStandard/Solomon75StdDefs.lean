module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.GLS

@[expose] def Solomon2AnStdCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G),
    standardComponentIsStandard L → ∀ n : ℕ, 8 ≤ n →
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) → Nat.card (center L) = 2 →
      (∃ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G)))) →
      Nonempty (G ≃* NativeSporadic.McL) ∨ Nonempty (G ≃* NativeSporadic.Ly)

@[expose] def Solomon2AnStdW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) →
      Nat.card (center L) = 2 →
        AltOutcome G ∨ OddLieType G ∨ IsSporadic G .McL ∨ IsSporadic G .Ly

structure StdSetup (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (n : ℕ)
    (z : G) : Prop where
  nonab : ∃ a b : G, a * b ≠ b * a
  standard : standardComponentIsStandard L
  hn : 8 ≤ n
  cover : IsDoubleCoverOfAlt ↥L n
  hz : orderOf z = 2
  z_mem : z ∈ L
  z_cent : z ∈ centralizer (L : Set G)
  cent_eq : centralizer ({z} : Set G) = normalizer (L : Set G)
  exists_partner : ∃ g : G, g⁻¹ * z * g ≠ z ∧ (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g)
  cyclic : ∀ P : Subgroup G, P ≤ centralizer (L : Set G) → IsPGroup 2 ↥P → IsCyclic ↥P
  inv_unique : ∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = z

@[expose] def Solomon2AnStdCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (n : ℕ) (z : G),
    StdSetup G L n z →
      n ≤ 11 ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)),
        Nat.card (S : Subgroup (centralizer (L : Set G))) = 2) ∧
      ∀ (M : AhatModel G n L) (a : G) (ha : a ∈ normalizer (L : Set G)),
        a ∈ centralizer ({z} : Set G) → a ≠ z → (∃ g : G, g⁻¹ * z * g = a) →
          Equiv.Perm.sign (M.perm a ha) = 1

@[expose] def Solomon2AnStdCoreFull : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (n : ℕ) (z : G),
    StdSetup G L n z →
      n ≤ 11 ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)),
        Nat.card (S : Subgroup (centralizer (L : Set G))) = 2) ∧
      ∀ (M : AhatModel G n L) (a : G) (ha : a ∈ normalizer (L : Set G)),
        a ∈ centralizer ({z} : Set G) → a ≠ z → (∃ g : G, g⁻¹ * z * g = a) →
          a ∈ L ∧ transCount (M.perm a ha) = 4

end CFSG.OddStandard.Solomon75
