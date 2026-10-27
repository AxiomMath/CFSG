module

public import CFSG.LocalAnalysis.GH72.Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups

section Vocabulary

variable {G : Type*} [Group G]

@[expose] abbrev O (H : Subgroup G) : Subgroup G := (CFSG.oddCore H).map H.subtype

@[expose] abbrev O2 (H : Subgroup G) : Subgroup G := CFSG.GorensteinWalter.twoResidualOf H

@[expose] abbrev Bar (H : Subgroup G) : Type _ := H ⧸ CFSG.oddCore H

@[expose] def bar (H K : Subgroup G) : Subgroup (Bar H) := (K.subgroupOf H).map (QuotientGroup.mk' _)

@[expose] abbrev C (a : G) : Subgroup G := centralizer ({a} : Set G)

@[expose] def IsIsolatedIn (H : Subgroup G) (t : G) : Prop :=
  t ∈ H ∧ orderOf t = 2 ∧ ∀ h ∈ H, Commute (h * t * h⁻¹) t → h * t * h⁻¹ = t

@[expose] def Covers (H M₀ OM : Subgroup G) : Prop := M₀ ≤ (H ⊓ M₀) ⊔ OM

@[expose] def IsE16 (E : Subgroup G) : Prop := CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 16

@[expose] def IsDih (D : Subgroup G) : Prop := ∃ a : ℕ, 1 ≤ a ∧ Nonempty (D ≃* DihedralGroup (2 ^ a))

@[expose] def IsDihNonab (D : Subgroup G) : Prop := ∃ a : ℕ, 2 ≤ a ∧ Nonempty (D ≃* DihedralGroup (2 ^ a))

@[expose] def IsL2OrA7 (L : Type*) [Group L] (qmin : ℕ) : Prop :=
  Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ qmin ≤ p ^ k ∧ Nonempty (L ≃* PSL(2, GaloisField p k))

@[expose] def IsL2PGL2OrA7OrV4 (L : Type*) [Group L] : Prop :=
  IsL2OrA7 L 5 ∨
    (∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 3 ≤ p ^ k ∧
      Nonempty (L ≃* CFSG.GorensteinWalter.PGL2 (GaloisField p k))) ∨
    IsKleinFour L

@[expose] def HasNormalTwoComplement (H : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).Normal ∧ Odd (Nat.card K) ∧
    ∃ n : ℕ, K.relIndex H = 2 ^ n

@[expose] def xySup (X Y : Subgroup G) (f : G → G → Subgroup G) : Subgroup G :=
  ⨆ (x : G) (_ : x ∈ X) (_ : x ≠ 1) (y : G) (_ : y ∈ Y) (_ : y ≠ 1), f x y

@[expose] def XYGenerated (X Y F : Subgroup G) : Prop :=
  F = xySup X Y fun x y => F ⊓ O (C x) ⊓ O (C y)

@[expose] def theta (X Y : Subgroup G) (a : G) : Subgroup G :=
  xySup X Y fun x y => C a ⊓ O (C x) ⊓ O (C y)

structure IsXYBalanced (X Y : Subgroup G) : Prop where
  a₁ : ∀ x ∈ X, x ≠ 1 → ∀ a ∈ X ⊔ Y, a ∉ Y → O (C x) ⊓ C a ≤ O (C a)
  a₂ : ∀ y ∈ Y, y ≠ 1 → ∀ b ∈ X ⊔ Y, b ∉ X → O (C y) ⊓ C b ≤ O (C b)
  b₁ : ∀ x ∈ X, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
    X ⊔ Y ≤ normalizer (D : Set G) → ⁅D, X⁆ ⊔ ⁅⁅D, Y⁆, ⁅D, Y⁆⁆ ≤ O (C x)
  b₂ : ∀ y ∈ Y, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
    X ⊔ Y ≤ normalizer (D : Set G) → ⁅D, Y⁆ ⊔ ⁅⁅D, X⁆, ⁅D, X⁆⁆ ≤ O (C y)
  c : ∀ (p : ℕ) (P : Subgroup G), p.Prime → p ≠ 2 → IsPGroup p P →
    X ⊔ Y ≤ normalizer (P : Set G) → XYGenerated X Y P →
    ∀ Q ≤ P, X ⊔ Y ≤ normalizer (Q : Set G) → XYGenerated X Y Q

structure DDDecomp (S S₁ S₂ : Subgroup G) : Prop where
  sup_eq : S₁ ⊔ S₂ = S
  inf_eq : S₁ ⊓ S₂ = ⊥
  commute : S₂ ≤ centralizer (S₁ : Set G)
  dih₁ : IsDih S₁
  dih₂ : IsDihNonab S₂

structure HasProductFusion (S₁ S₂ : Subgroup G) : Prop where
  conj₁ : ∀ x ∈ S₁, ∀ y ∈ S₁, orderOf x = 2 → orderOf y = 2 → IsConj x y
  conj₂ : ∀ x ∈ S₂, ∀ y ∈ S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y
  conj₃ : ∀ x ∈ S₁ ⊔ S₂, ∀ y ∈ S₁ ⊔ S₂, x ∉ S₁ → x ∉ S₂ → y ∉ S₁ → y ∉ S₂ →
    orderOf x = 2 → orderOf y = 2 → IsConj x y
  separate : ∀ x ∈ S₁ ⊔ S₂, ∀ y ∈ S₁ ⊔ S₂, orderOf x = 2 → IsConj x y →
    (x ∈ S₁ ↔ y ∈ S₁) ∧ (x ∈ S₂ ↔ y ∈ S₂)

@[expose] def IsMaxInvIn (p : ℕ) (A H P : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup p P ∧ A ≤ normalizer (P : Set G) ∧
    ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → A ≤ normalizer (Q : Set G) → P ≤ Q → Q = P

end Vocabulary

structure Sec3Setting (G : Type*) [Group G] [Finite G] where
  S : Sylow 2 G
  S₁ : Subgroup G
  S₂ : Subgroup G
  decomp : DDDecomp (S : Subgroup G) S₁ S₂
  noIndexTwo : ∀ N : Subgroup G, N.Normal → N.index ≠ 2

end CFSG.GH72

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups Pointwise

section QuotientShapes

variable {G : Type} [Group G]

@[expose] def QuotIs (K N : Subgroup G) (P : ∀ L : Type, Group L → Prop) : Prop :=
  ∃ (L : Type) (_ : Group L) (f : K →* L), Function.Surjective f ∧ f.ker = N.subgroupOf K ∧
    P L inferInstance

@[expose] def QuotIso (K N K' N' : Subgroup G) : Prop :=
  ∃ (L : Type) (_ : Group L) (f : K →* L) (f' : K' →* L), Function.Surjective f ∧
    Function.Surjective f' ∧ f.ker = N.subgroupOf K ∧ f'.ker = N'.subgroupOf K'

end QuotientShapes

structure Sec4Setting (G : Type) [Group G] [Finite G] extends Sec3Setting G where
  mc : MinimalCounterexample G
  fusion : HasProductFusion S₁ S₂
  z₁ : G
  z₂ : G
  hz₁ : z₁ ∈ S₁ ∧ orderOf z₁ = 2 ∧ S₁ ≤ C z₁
  hz₂ : z₂ ∈ S₂ ∧ orderOf z₂ = 2 ∧ S₂ ≤ C z₂

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

variable (A : Subgroup G)

@[expose] def X : Subgroup G := A ⊓ 𝔖.S₁
@[expose] def Y : Subgroup G := A ⊓ 𝔖.S₂
@[expose] def M : Subgroup G := centralizer (𝔖.X A : Set G)
@[expose] def N : Subgroup G := centralizer (𝔖.Y A : Set G)
@[expose] def M₀ : Subgroup G := ⁅O2 (𝔖.M A), O2 (𝔖.M A)⁆ ⊔ O (𝔖.M A)
@[expose] def N₀ : Subgroup G := ⁅O2 (𝔖.N A), O2 (𝔖.N A)⁆ ⊔ O (𝔖.N A)

variable {A} (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

@[expose] def PConstrainedWrt (p : ℕ) (A H Z : Subgroup G) : Prop :=
  ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (O H) ∧ A ≤ normalizer (P : Set G) ∧
    ¬ Z ≤ centralizer (P : Set G)

@[expose] def IsPLocalA (p : ℕ) (A H : Subgroup G) : Prop :=
  CFSG.IsPLocal p H ∧ A ≤ H ∧ ∃ P : Subgroup G, IsMaxInvIn p A ⊤ P ∧ P ≤ H

@[expose] def IsCoveringFirst (p : ℕ) (A H : Subgroup G) : Prop :=
  IsPLocalA p A H ∧ Covers H (𝔖.M₀ A) (O (𝔖.M A))

@[expose] def IsCoveringSecond (p : ℕ) (A H : Subgroup G) : Prop :=
  IsPLocalA p A H ∧ Covers H (𝔖.N₀ A) (O (𝔖.N A))

@[expose] def IsCovering (p : ℕ) (A H : Subgroup G) : Prop :=
  IsPLocalA p A H ∧ Covers H (𝔖.M₀ A) (O (𝔖.M A)) ∧ Covers H (𝔖.N₀ A) (O (𝔖.N A))

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)

end Sec4Setting

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

@[expose] def WA (A : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), theta (𝔖.X A) (𝔖.Y A) a

@[expose] def IsM1 (A M₁ : Subgroup G) : Prop :=
  M₁ ≤ 𝔖.M A ∧ (M₁.subgroupOf (𝔖.M A)).Normal ∧ CFSG.Open.IsQuasisimple M₁ ∧
    CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ M₁ ∧ QuotIso M₁ (O M₁) (𝔖.M₀ A) (O (𝔖.M A)) ∧
    ∀ T₁ : Subgroup G, T₁ ≤ 𝔖.S₁ → T₁ ≠ ⊥ →
      M₁ ≤ normalizer (T₁ : Set G) ∧ (M₁.subgroupOf (normalizer (T₁ : Set G))).Normal

@[expose] def IsN1 (A N₁ : Subgroup G) : Prop :=
  N₁ ≤ 𝔖.N A ∧ (N₁.subgroupOf (𝔖.N A)).Normal ∧ CFSG.Open.IsQuasisimple N₁ ∧
    CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ N₁ ∧ QuotIso N₁ (O N₁) (𝔖.N₀ A) (O (𝔖.N A)) ∧
    ∀ T₂ : Subgroup G, T₂ ≤ 𝔖.S₂ → T₂ ≠ ⊥ →
      N₁ ≤ normalizer (T₂ : Set G) ∧ (N₁.subgroupOf (normalizer (T₂ : Set G))).Normal

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

end Sec4Setting

end CFSG.GH72

