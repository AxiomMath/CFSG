module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.Quasithin.Background.A1cTransfer
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin

variable {X : Type} [Group X]

@[expose] def T0 (T : Subgroup X) : Subgroup X := closure {t : X | t ∈ T ∧ t * t = 1}

@[expose] def Z0 (T : Subgroup X) : Set X :=
  {t : X | t ∈ T0 T ∧ t * t = 1 ∧ ∀ s ∈ T0 T, s * t = t * s}

@[expose] def IsDihedralGE8 (D : Subgroup X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥D ≃* DihedralGroup (2 ^ n))

@[expose] def IsMaximalClassTwoGroup (Q : Type*) [Group Q] : Prop :=
  IsPGroup 2 Q ∧ ∃ _ : Group.IsNilpotent Q, 2 ^ (Group.nilpotencyClass Q + 1) = Nat.card Q

structure Cfg34 (X : Type) [Group X] (T P Q : Subgroup X) (x z f h : X) : Prop where
  X_simple : IsSimpleGroup X
  X_nonab : ∃ a b : X, a * b ≠ b * a
  T_pgroup : IsPGroup 2 ↥T
  T_index : ¬ 2 ∣ T.index
  x_mem : x ∈ T
  x_order : orderOf x = 2
  x_central : ∀ t ∈ T, t * x = x * t
  P_le : P ≤ T
  Q_le : Q ≤ T
  P_norm : ∀ t ∈ T, ∀ a ∈ P, t * a * t⁻¹ ∈ P
  Q_norm : ∀ t ∈ T, ∀ a ∈ Q, t * a * t⁻¹ ∈ Q
  PQ_inf : P ⊓ Q = ⊥
  x_mem_Q : x ∈ Q
  P_dihedral : IsDihedralGE8 P
  z_mem : z ∈ P
  z_order : orderOf z = 2
  z_central : ∀ a ∈ P, a * z = z * a
  z_unique : ∀ c ∈ P, (∀ a ∈ P, a * c = c * a) → c = 1 ∨ c = z
  Q_shape : IsCyclic ↥Q ∨ IsMaximalClassTwoGroup ↥Q
  f_mem : f ∈ T
  f_order : orderOf f = 2
  f_not_mem : f ∉ P ⊔ Q
  f_cent : ∀ a ∈ P, f * a = a * f
  h_mem : h ∈ T
  h_sq : h * h = 1
  kf_abelian : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ P ⊔ Q
  kf_invol : ∀ t ∈ T, t * t = 1 → t ∈ (P ⊔ Q) ⊔ zpowers f ∨ ∃ r ∈ P ⊔ Q, t = r * h
  kf_h : h = 1 ∨ (h ∉ (P ⊔ Q) ⊔ zpowers f ∧ IsDihedralGE8 (P ⊔ zpowers h))
  kf_3B : ∀ t ∈ T, (∀ a ∈ P, t * a = a * t) ↔ t ∈ (Q ⊔ zpowers f) ⊔ zpowers z
  kf_conj_P : ∀ p ∈ P, orderOf p = 2 → ∃ g : X, g⁻¹ * z * g = p
  kf_conj_xP : ∀ p ∈ P, orderOf p = 2 → ∃ g : X, g⁻¹ * (x * z) * g = x * p
  kf_C : ∀ y ∈ T, y * y = 1 → y ∈ (P ⊔ Q) ⊔ zpowers f → y ∉ P →
    ∃ g ∈ centralizer ({x} : Set X), g⁻¹ * y * g ∈ (Q ⊔ zpowers f) ⊔ zpowers z
  kf_zC : ∀ g ∈ centralizer ({x} : Set X), g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ P
  kf_shear : ∀ w ∈ T, w * w = 1 → (∀ a ∈ P, w * a = a * w) → w ∉ Q ⊔ zpowers z →
    ∃ g : X, g⁻¹ * w * g ∈ zpowers w ⊔ P ∧ g⁻¹ * w * g ≠ w
  kf_N : ∃ N : Subgroup X, (∀ g ∈ centralizer ({x} : Set X), ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ N ⊓ T = Q

@[expose] def OddMove : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (H : Subgroup M), ¬ 2 ∣ H.index → H ≠ ⊤ →
    ∃ m : M, Odd (orderOf m) ∧ m ∉ H

@[expose] def AlperinStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T P : Subgroup X), IsPGroup 2 ↥T → ¬ 2 ∣ T.index → P ≤ T →
    (∃ g : X, (∀ a ∈ P, g⁻¹ * a * g ∈ T) ∧ ∃ a ∈ P, g⁻¹ * a * g ∉ P) →
    ∃ D : Subgroup X, P ≤ D ∧ D ≤ T ∧
      ¬ 2 ∣ (T ⊓ normalizer (D : Set X)).relIndex (normalizer (D : Set X)) ∧
      ∃ n ∈ normalizer (D : Set X), ∃ a ∈ P, n⁻¹ * a * n ∉ P

@[expose] def DihedralShapeFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup X), IsDihedralGE8 D →
    8 ≤ Nat.card ↥D ∧ IsPGroup 2 ↥D ∧
    (∀ a ∈ D, a ∈ closure {p : X | p ∈ D ∧ p * p = 1}) ∧
    ∀ z ∈ D, orderOf z = 2 → (∀ a ∈ D, a * z = z * a) →
      (∀ c ∈ D, (∀ a ∈ D, a * c = c * a) → c = 1 ∨ c = z) ∧
      (∃ w ∈ D, w * w = z) ∧ z ∈ ⁅D, D⁆ ∧
      ∃ A : Subgroup X, A ≤ D ∧ IsCyclic ↥A ∧ 2 * Nat.card ↥A = Nat.card ↥D ∧
        (∀ B : Subgroup X, B ≤ D → IsCyclic ↥B → Nat.card ↥B = Nat.card ↥A → B = A) ∧
        ∀ p ∈ D, p * p = 1 → (∀ c ∈ A, p * c = c * p) → p = 1 ∨ p = z

@[expose] def DihedralMaxFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (W : Subgroup X), IsDihedralGE8 W → 16 ≤ Nat.card ↥W →
    (∀ A B C : Subgroup X, A ≤ W → B ≤ W → C ≤ W → IsDihedralGE8 A → IsDihedralGE8 B →
      IsDihedralGE8 C → Nat.card ↥A * 2 = Nat.card ↥W → Nat.card ↥B * 2 = Nat.card ↥W →
      Nat.card ↥C * 2 = Nat.card ↥W → A = B ∨ B = C ∨ A = C) ∧
    (∀ A B : Subgroup X, A ≤ W → B ≤ W → IsDihedralGE8 A → IsDihedralGE8 B →
      Nat.card ↥A * 2 = Nat.card ↥W → Nat.card ↥B * 2 = Nat.card ↥W → A ≠ B →
      Nat.card ↥(A ⊓ B) * 2 = Nat.card ↥A ∧ A ⊓ B ≤ ⁅A, B⁆)

@[expose] def QShapeFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T Q : Subgroup X) (x : X), IsPGroup 2 ↥T → Q ≤ T →
    (∀ t ∈ T, ∀ a ∈ Q, t * a * t⁻¹ ∈ Q) → x ∈ Q → orderOf x = 2 → (∀ t ∈ T, t * x = x * t) →
    (IsCyclic ↥Q ∨ IsMaximalClassTwoGroup ↥Q) →
    (∀ z₁ ∈ Q, ∀ z₂ ∈ Q, z₁ ≠ 1 → z₂ ≠ 1 → z₁ ≠ z₂ → z₁ * z₁ = 1 → z₂ * z₂ = 1 →
      z₁ * z₂ = z₂ * z₁ → (∀ q ∈ Q, q * q = 1 → q * z₁ = z₁ * q ∧ q * z₂ = z₂ * q) →
      Nat.card ↥Q = 4) ∧
    (∃ Q₀ : Subgroup X, Q₀ ≤ Q ∧ (∀ t ∈ T, ∀ a ∈ Q₀, t * a * t⁻¹ ∈ Q₀) ∧ IsCyclic ↥Q₀ ∧
      ∀ q ∈ Q, q * q = 1 → (∀ c ∈ Q₀, q * c = c * q) → ∀ y ∈ Q, q * y = y * q) ∧
    (∀ q ∈ Q, (∀ y ∈ Q, q * y = y * q) → q * q = 1 → q ≠ 1 → q ≠ x → Nat.card ↥Q = 4) ∧
    (∀ a ∈ Q, ∀ b ∈ Q, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a →
      x = a ∨ x = b ∨ x = a * b)

section Lemmas

variable (T P Q : Subgroup X) (x z f : X)

@[expose] def Lemma35 : Prop :=
  ∃ g : X, g⁻¹ * f * g ∈ P ⊔ Q ∧ (∀ c ∈ T, c * f = f * c → g⁻¹ * c * g ∈ T) ∧
    IsExtremalIn 2 T (g⁻¹ * f * g)

@[expose] def Lemma37 : Prop := ∀ g : X, g⁻¹ * z * g ∈ Z0 T → g⁻¹ * z * g = z

@[expose] def Lemma38 : Prop := ∀ g : X, (∀ a ∈ P, g⁻¹ * a * g ∈ T) → g⁻¹ * z * g = z

@[expose] def Lemma39 : Prop :=
  ∀ y : X, (∃ g : X, g⁻¹ * z * g = y) → y ∈ T → y ∈ (P ⊔ Q) ⊔ zpowers f → y ∈ P

@[expose] def Lemma310 : Prop :=
  ∀ g : X, (∀ a ∈ P, g⁻¹ * a * g ∈ T) → ∀ a ∈ P, g⁻¹ * a * g ∈ P

@[expose] def Lemma311 : Prop :=
  ∀ u : X, u ∈ T → (∀ a ∈ P, u * a = a * u) → u * u = 1 → IsExtremalIn 2 T u →
    IsExtremalIn 2 T (u * z)

@[expose] def Lemma312 : Prop :=
  ∃ f₀ g : X, (f₀ = f ∨ f₀ = f * z) ∧ g ∈ normalizer (P : Set X) ∧ g⁻¹ * f₀ * g ∈ Q ∧
    IsExtremalIn 2 T (g⁻¹ * f₀ * g) ∧ ∀ c ∈ T, c * f₀ = f₀ * c → g⁻¹ * c * g ∈ T

@[expose] def Lemma313 : Prop := ∃ g : X, g⁻¹ * x * g = x * z

end Lemmas

end CFSG.GH74.GLS.C3.Layer1.P34
