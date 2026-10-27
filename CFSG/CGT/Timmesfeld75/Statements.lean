module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def ThmAConclusion {G : Type} [Group G] (T : Subgroup G) : Prop :=
  ∃ (N : Subgroup (Subgroup.normalClosure (T : Set G))) (_ : N.Normal),
    IsElemAbelian 2 N ∧
      (ZStarCase (↥(Subgroup.normalClosure (T : Set G)) ⧸ N) ∨
        IsCoveringOfList (↥(Subgroup.normalClosure (T : Set G)) ⧸ N))

@[expose] def TheoremAStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsWC T → ThmAConclusion T

@[expose] def CorollaryBStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), CorBHyp T → ThmAConclusion T

@[expose] def NodeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ B : Subgroup G, IsElemAbelian 2 B → 4 ≤ Nat.card B →
      (∀ g : G, B ⊓ conjSubgroup g⁻¹ B = ⊥ ∨ B ⊓ conjSubgroup g⁻¹ B = B) →
      (∀ g : G, conjSubgroup g⁻¹ B ≤ Subgroup.normalizer (B : Set G) → conjSubgroup g⁻¹ B = B) →
      (∃ m s : ℕ, 2 ≤ m ∧ 1 ≤ s ∧ StatedClassicalModel G .PSL m 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s) ∨
      (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ k : ℕ, 6 ≤ k ∧ k ≤ 9 ∧ Nonempty (G ≃* alternatingGroup (Fin k))) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M24

end CFSG.CGT.Timmesfeld75
