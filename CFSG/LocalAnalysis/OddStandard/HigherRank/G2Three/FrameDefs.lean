module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1

open Subgroup CFSG.Open
open scoped commutatorElement

section Vocabulary

variable {Γ : Type} [Group Γ]

@[expose] def conjClass (T : Subgroup Γ) (y : Γ) : Set Γ := {w | ∃ t ∈ T, w = t * y * t⁻¹}

@[expose] def conjSub (c : Γ) (Y : Subgroup Γ) : Subgroup Γ :=
  Y.map (MulAut.conj c).toMonoidHom

@[expose] def invols (T : Subgroup Γ) : Set Γ := {y | y ∈ T ∧ orderOf y = 2}

@[expose] def cen (T : Subgroup Γ) : Subgroup Γ := T ⊓ centralizer (T : Set Γ)

@[expose] def centIn (V X : Subgroup Γ) : Subgroup Γ := V ⊓ centralizer (X : Set Γ)

@[expose] def centEl (V : Subgroup Γ) (y : Γ) : Subgroup Γ := V ⊓ centralizer ({y} : Set Γ)

@[expose] def IsMaximalIn (V M : Subgroup Γ) : Prop :=
  M < V ∧ ∀ N : Subgroup Γ, M < N → N ≤ V → N = V

@[expose] def normIn (V X : Subgroup Γ) : Subgroup Γ := V ⊓ normalizer (X : Set Γ)

@[expose] def zSeries (n : ℕ) (T : Subgroup Γ) : Subgroup Γ :=
  (Subgroup.upperCentralSeries ↥T n).map T.subtype

@[expose] def omega1 (T : Subgroup Γ) : Subgroup Γ := closure {y | y ∈ T ∧ y ^ 2 = 1}

@[expose] def IsSylowIn (p : ℕ) (V P : Subgroup Γ) : Prop :=
  P ≤ V ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex V

@[expose] def IsE (n : ℕ) (Y : Type) [Group Y] : Prop :=
  IsElemAbelian 2 (⊤ : Subgroup Y) ∧ Nat.card Y = 2 ^ n

@[expose] def IsFrobeniusOfOrder (n : ℕ) (Y : Type) [Group Y] : Prop :=
  Nat.card Y = n ∧ ∃ W D : Subgroup Y, W.Normal ∧ W ⊔ D = ⊤ ∧ W ⊓ D = ⊥ ∧ W ≠ ⊥ ∧ D ≠ ⊥ ∧
    ∀ d ∈ D, d ≠ 1 → ∀ w ∈ W, d * w = w * d → w = 1

@[expose] def IsQ8StarQ8 (Y : Type) [Group Y] : Prop :=
  ∃ U V : Subgroup Y, Nonempty (↥U ≃* QuaternionGroup 2) ∧ Nonempty (↥V ≃* QuaternionGroup 2) ∧
    (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧ U ⊔ V = ⊤ ∧ Nat.card ↥(U ⊓ V) = 2

@[expose] def IsExtraspecialTwo (n : ℕ) (X : Subgroup Γ) : Prop :=
  Nat.card X = 2 ^ (2 * n + 1) ∧ Nat.card (cen X) = 2 ∧ ⁅X, X⁆ = cen X ∧ ∀ y ∈ X, y ^ 2 ∈ cen X

@[expose] def IsInternalDirect (X U V : Subgroup Γ) : Prop :=
  U ⊔ V = X ∧ U ⊓ V = ⊥ ∧ ∀ u ∈ U, ∀ v ∈ V, u * v = v * u

@[expose] def IsZ2xD8Decomp (X : Subgroup Γ) (c : Γ) (D : Subgroup Γ) : Prop :=
  IsInternalDirect X (closure {c}) D ∧ orderOf c = 2 ∧ Nonempty (↥D ≃* DihedralGroup 4) ∧
    Nonempty (↥X ≃* Multiplicative (ZMod 2) × DihedralGroup 4)

@[expose] def ActsRegularly (T V Z : Subgroup Γ) : Prop :=
  T ≤ normalizer (V : Set Γ) ∧ T ≤ normalizer (Z : Set Γ) ∧
    ∀ u ∈ V, u ∉ Z → ∀ v ∈ V, v ∉ Z → ∃! k : Γ, k ∈ T ∧ v⁻¹ * (k * u * k⁻¹) ∈ Z

@[expose] def orbitMod (T Z : Subgroup Γ) (u : Γ) : Set Γ :=
  {w | ∃ k ∈ T, (k * u * k⁻¹)⁻¹ * w ∈ Z}

@[expose] def IsOrbitMod (T Z : Subgroup Γ) (O : Set Γ) : Prop :=
  ∃ u ∈ O, O = orbitMod T Z u

@[expose] def SplitsOver (N F : Subgroup Γ) : Prop :=
  ∃ C : Subgroup Γ, C ≤ N ∧ F ⊓ C = ⊥ ∧ F ⊔ C = N

@[expose] def maxElemAbelian (T : Subgroup Γ) : Set (Subgroup Γ) :=
  {Y | Y ≤ T ∧ IsElemAbelian 2 Y ∧
    ∀ Y' : Subgroup Γ, Y ≤ Y' → Y' ≤ T → IsElemAbelian 2 Y' → Y' = Y}

variable [Finite Γ]

@[expose] noncomputable def thompsonRank (T : Subgroup Γ) : Subgroup Γ :=
  ⨆ (U : Subgroup Γ) (_ : U ≤ T) (_ : IsMulCommutative U)
    (_ : ∀ V : Subgroup Γ, V ≤ T → IsMulCommutative V → pRank 2 V ≤ pRank 2 U), U

@[expose] def SecProp (V N : Subgroup Γ)
    (P : (Y : Type) → [Group Y] → [Finite Y] → (↥V →* Y) → Prop) : Prop :=
  ∃ h : (N.subgroupOf V).Normal,
    haveI := h
    P (↥V ⧸ N.subgroupOf V) (QuotientGroup.mk' (N.subgroupOf V))

end Vocabulary

end CFSG.OddStandard.HigherRank.G2Three.Sec1
