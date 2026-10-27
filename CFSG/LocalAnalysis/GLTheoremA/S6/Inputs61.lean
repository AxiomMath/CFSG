module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

@[expose] def innerModSubgroup (p : ℕ) (L : Subgroup G) : Subgroup G where
  carrier := {g | InducesInnerMod p L g}
  one_mem' := S3.inducesInnerMod_one p L
  mul_mem' := fun ha hb => S3.inducesInnerMod_mul ha hb
  inv_mem' := fun ha => S3.inducesInnerMod_inv ha

theorem mem_innerModSubgroup {p : ℕ} {L : Subgroup G} {g : G} :
    g ∈ innerModSubgroup p L ↔ InducesInnerMod p L g := Iff.rfl

@[expose] def IsCoreFreeLocalType (p : ℕ) {K : Type*} [Group K] (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), D ≤ A → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    D ≤ Subgroup.normalizer (H : Set (MulAut K)) →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer (D : Set (MulAut K))) = ⊥

@[expose] def IsCompCoreFreeLocalType (p : ℕ) (B L : Subgroup G) : Prop :=
  IsCoreFreeLocalType p (autBar p B L)

@[expose] def I71I117At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (x : G) (L : Subgroup G),
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → GLAIsBmax p B → IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L → B ≤ Subgroup.normalizer (L : Set G) →
    IsChevSimple p (PSimple p L) → Nat.card B ≤ p * Nat.card ↥(B ⊓ innerModSubgroup p L)

@[expose] def I196At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X J B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X J →
    IsChevSimple p (PSimple p J) → IsElemAbelian p B →
    IsCompCoreFreeLocalType p B J ∨
      (p = 3 ∧ catalogIs (PSimple 3 J) (onLie (isL2 27)) ∧
        ∃ b ∈ B ⊓ Subgroup.normalizer (J : Set G), ¬ InducesInnerMod 3 J b)

@[expose] def I194At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → ∀ (X B A : Subgroup G), CFSG.Open.IsKGroup ↥X → B ≤ X → IsElemAbelian p B → A ≤ B →
    (∀ J : Subgroup G, GLAPComponent p X J → IsCompCoreFreeLocalType p B J) →
    GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (A : Set G)) ≤ GLAPPrimeCoreOf p X

end CFSG.LocalAnalysis.GLTheoremA
