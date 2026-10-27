module

public import CFSG.GH74.GLS.Bg.TwoGroups.Vocab
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup
open scoped commutatorElement

@[expose] def IG_9_16 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal] (x : X),
    Nat.card (centralizer ({(x : X ⧸ N)} : Set (X ⧸ N))) ≤ Nat.card (centralizer ({x} : Set X))

@[expose] def NormCentLift {X : Type} [Group X] (E H : Subgroup X) [E.Normal] : Prop :=
  normalizer (((H ⊔ E).map (QuotientGroup.mk' E) : Subgroup (X ⧸ E)) : Set (X ⧸ E)) =
      (normalizer (H : Set X) ⊔ E).map (QuotientGroup.mk' E) ∧
    centralizer (((H ⊔ E).map (QuotientGroup.mk' E) : Subgroup (X ⧸ E)) : Set (X ⧸ E)) =
      (centralizer (H : Set X) ⊔ E).map (QuotientGroup.mk' E)

@[expose] def IV2_14_4_H1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (E H : Subgroup X) [E.Normal],
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → H ⊓ E = ⊥ → ComplementsConj E H → NormCentLift E H

@[expose] def IV2_14_4_free : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (E : Subgroup X) [E.Normal] (x : X), orderOf x = 2 →
    IsElemAbelian 2 E → zpowers x ⊓ E = ⊥ →
      Nat.card ↥(E ⊓ centralizer ({x} : Set X)) ^ 2 = Nat.card ↥E → NormCentLift E (zpowers x)

@[expose] def IG_10_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (x : G) (n : ℕ) (Pi : ℕ → Subgroup G),
    orderOf x = 2 → (∀ g ∈ P, x * g * x⁻¹ ∈ P) → Pi 0 = ⊥ → Pi n = P →
    (∀ i < n, FreeSec2 x (Pi i) (Pi (i + 1))) →
    ∀ y : G, y * x⁻¹ ∈ P → y ^ 2 = 1 → ∃ c ∈ P, c * x * c⁻¹ = y

@[expose] def IG_10_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q₁ Q₂ : Subgroup G) (x : G), orderOf x = 2 →
    (∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) → Q₁ ⊓ Q₂ = ⊥ → (∀ g, g ∈ Q₂ ↔ x * g * x⁻¹ ∈ Q₁) →
    ∀ y : G, (∃ a ∈ Q₁ ⊔ Q₂, y = a * x) → y ^ 2 = 1 → ∃ c ∈ Q₁ ⊔ Q₂, c * x * c⁻¹ = y

section Aut44

variable (B : Type) [CommGroup B]

@[expose] def ZB : Subgroup B := (powMonoidHom 2 : B →* B).ker

theorem mem_ZB {b : B} : b ∈ ZB B ↔ b ^ 2 = 1 := by
  simp [ZB]

@[expose] def A0 : Subgroup (MulAut B) where
  carrier := {α | ∀ b : B, α b * b⁻¹ ∈ ZB B}
  mul_mem' := by
    intro α β hα hβ b
    have h : (α * β) b * b⁻¹ = (α (β b) * (β b)⁻¹) * (β b * b⁻¹) := by
      simp [MulAut.mul_apply]
    rw [h]
    exact mul_mem (hα (β b)) (hβ b)
  one_mem' := by
    intro b
    simp
  inv_mem' := by
    intro α hα b
    have h := hα (α⁻¹ b)
    have h' : α⁻¹ b * b⁻¹ = (α (α⁻¹ b) * (α⁻¹ b)⁻¹)⁻¹ := by
      simp
    rw [h']
    exact inv_mem h

@[expose] def iotaB : MulAut B := MulEquiv.inv B

@[expose] def commB (α : MulAut B) : Subgroup B := Subgroup.closure (Set.range fun b : B => b⁻¹ * α b)

@[expose] def CB (α : MulAut B) : Subgroup B where
  carrier := {b | α b = b}
  mul_mem' := by
    intro a b ha hb
    change α a = a at ha
    change α b = b at hb
    change α (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := by
    change α 1 = 1
    exact map_one α
  inv_mem' := by
    intro a ha
    change α a = a at ha
    change α a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[expose] def CBar (v : MulAut B) : Subgroup B where
  carrier := {b | v b * b⁻¹ ∈ ZB B}
  mul_mem' := by
    intro a b ha hb
    change v a * a⁻¹ ∈ ZB B at ha
    change v b * b⁻¹ ∈ ZB B at hb
    change v (a * b) * (a * b)⁻¹ ∈ ZB B
    have h : v (a * b) * (a * b)⁻¹ = (v a * a⁻¹) * (v b * b⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [h]
    exact mul_mem ha hb
  one_mem' := by
    change v 1 * (1 : B)⁻¹ ∈ ZB B
    simp
  inv_mem' := by
    intro a ha
    change v a * a⁻¹ ∈ ZB B at ha
    change v a⁻¹ * (a⁻¹)⁻¹ ∈ ZB B
    have h : v a⁻¹ * (a⁻¹)⁻¹ = (v a * a⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
    rw [h]
    exact inv_mem ha

@[expose] def IsPhi (z : B) (φ : MulAut B) : Prop :=
  commB B φ = zpowers z ∧ ∀ b : B, b ∈ CB B φ ↔ b ^ 2 ∈ zpowers z

@[expose] def IsDd (x d : MulAut B) : Prop :=
  d ∈ A0 B ∧ centralizer ({x} : Set (MulAut B)) ⊓ A0 B = zpowers (iotaB B) ⊔ zpowers d ∧
    Nat.card ↥(zpowers (iotaB B) ⊔ zpowers d) = 4 ∧
    (∀ a ∈ zpowers (iotaB B) ⊔ zpowers d, a * a = 1) ∧
    CB B d = ZB B ∧ CB B (d * iotaB B) = ZB B

end Aut44

@[expose] def IV2_2_1_order : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → Nat.card (MulAut B) = 96

@[expose] def IV2_2_1_a : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) →
    A0 B = O2 (⊤ : Subgroup (MulAut B)) ∧ IsElemAbelian 2 (A0 B) ∧ Nat.card (A0 B) = 16

@[expose] def IV2_2_1_b : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) →
    ∃ φ : MulAut B →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ φ.ker = A0 B

@[expose] def IV2_2_1_c : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) →
    Nonempty (↥(O2res (⊤ : Subgroup (MulAut B))) ≃* ↥(alternatingGroup (Fin 4)))

@[expose] def IV2_2_1_d : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ x : MulAut B, orderOf x = 3 →
    ∃ d : MulAut B, IsDd B x d

@[expose] def IV2_2_1_e : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ z ∈ ZB B, z ≠ 1 → ∃! φ : MulAut B, IsPhi B z φ

@[expose] def IV2_2_1_f1 : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ x : MulAut B, orderOf x = 3 →
    ∀ d : MulAut B, IsDd B x d → ∀ φ : B → MulAut B, (∀ z ∈ ZB B, z ≠ 1 → IsPhi B z (φ z)) →
      let A' : Set (MulAut B) := {d, d * iotaB B} ∪ {u | ∃ z ∈ ZB B, z ≠ 1 ∧ u = φ z}
      A' ⊆ A0 B ∧ ∀ u ∈ A0 B, u ≠ 1 → (u ∈ A' ↔ ∀ b : B, u b = b⁻¹ → b ^ 2 = 1)

@[expose] def IV2_2_1_f1' : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ x : MulAut B, orderOf x = 3 →
    ∀ d : MulAut B, IsDd B x d → ∀ φ : B → MulAut B, (∀ z ∈ ZB B, z ≠ 1 → IsPhi B z (φ z)) →
      let A' : Set (MulAut B) := {d, d * iotaB B} ∪ {u | ∃ z ∈ ZB B, z ≠ 1 ∧ u = φ z}
      ∀ u ∈ A0 B, u ≠ 1 →
        (u ∈ A' ↔ ∀ b : B,
          (⟨b, u⟩ : SemidirectProduct B (MulAut B) (MonoidHom.id (MulAut B))) ^ 2 = 1 →
            b ^ 2 = 1)

@[expose] def IV2_2_1_f2 : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ x : MulAut B, orderOf x = 3 →
    ∀ d : MulAut B, IsDd B x d → ∀ φ : B → MulAut B, (∀ z ∈ ZB B, z ≠ 1 → IsPhi B z (φ z)) →
      let A' : Set (MulAut B) := {d, d * iotaB B} ∪ {u | ∃ z ∈ ZB B, z ≠ 1 ∧ u = φ z}
      ∀ l : List (MulAut B), l.Nodup → (∀ w, w ∈ l ↔ w ∈ A') → l.prod = 1

@[expose] def IV2_2_1_g : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ v : MulAut B, v ∉ A0 B →
    (∃ k : ℕ, orderOf v = 2 ^ k) →
      Nat.card ↥(centralizer ({v} : Set (MulAut B)) ⊓ A0 B) ^ 2 = Nat.card (A0 B) ∧
      Nat.card ↥(ZB B ⊓ CB B v) ^ 2 = Nat.card (ZB B) ∧
      Nat.card (CBar B v) ^ 2 = Nat.card B * Nat.card (ZB B) ∧
      ∀ z : B, ZB B ⊓ CB B v = zpowers z → ∀ φ : MulAut B, IsPhi B z φ →
        centralizer ({v} : Set (MulAut B)) ⊓ A0 B = zpowers φ ⊔ zpowers (iotaB B)

@[expose] def IV2_2_1_h : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) →
    (∃ K : Subgroup (MulAut B), Nonempty (↥K ≃* Z2xS3)) ∧
    ∀ K L : Subgroup (MulAut B), Nonempty (↥K ≃* Z2xS3) → Nonempty (↥L ≃* Z2xS3) →
      ∃ g : MulAut B, ∀ a : MulAut B, a ∈ L ↔ g⁻¹ * a * g ∈ K

@[expose] def IV2_2_1_i : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) → ∀ x : MulAut B, orderOf x = 3 →
    ∀ d : MulAut B, IsDd B x d →
      ∃ K₁ K₂ : Subgroup (MulAut B), K₁ ≠ K₂ ∧ Nonempty (↥K₁ ≃* Equiv.Perm (Fin 4)) ∧
        Nonempty (↥K₂ ≃* Equiv.Perm (Fin 4)) ∧
        (∀ K : Subgroup (MulAut B), Nonempty (↥K ≃* Equiv.Perm (Fin 4)) → K = K₁ ∨ K = K₂) ∧
        (∀ a : MulAut B, a ∈ K₂ ↔ d⁻¹ * a * d ∈ K₁) ∧ (∀ a : MulAut B, a ∈ K₁ ↔ d⁻¹ * a * d ∈ K₂)

@[expose] def IV2_2_1_j : Prop :=
  ∀ (B : Type) [CommGroup B], Nonempty (B ≃* Z4Z4) →
    ∀ a ∈ O2 (O2res (⊤ : Subgroup (MulAut B))), a ≠ 1 → a * a = 1 →
      (∃ y ∈ ZB B, y ≠ 1 ∧ ∀ φ : MulAut B, IsPhi B y φ → a = φ * iotaB B) ∧ commB B a = ZB B

@[expose] def commAut {T : Type*} [Group T] (α : MulAut T) : Subgroup T :=
  Subgroup.closure (Set.range fun g : T => g⁻¹ * α g)

@[expose] def IV2_2_3 : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nat.card T = 64 →
    ∀ x : MulAut T, orderOf x = 3 → (∀ g : T, x g = g → g = 1) →
    ∀ A : Subgroup T, A.Normal → (∀ a ∈ A, x a ∈ A) → Nonempty (↥A ≃* Z4Z4) →
      centralizer (A : Set T) = A →
      (Om1 A = Om1 (⊤ : Subgroup T) → Nonempty (T ≃* SylSU3_4)) ∧
      (Om1 A ≠ Om1 (⊤ : Subgroup T) → Nonempty (T ≃* SylSL3_4))

@[expose] def IV2_2_7 : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsPGroup 2 T → ∀ t : T, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3) →
    ∀ α : MulAut T, α ≠ 1 → (∃ n : ℕ, orderOf α = 3 ^ n) → α t = t →
      (commAut α).Normal ∧ commAut α ⊓ zpowers t = ⊥ ∧ commAut α ⊔ zpowers t = ⊤ ∧
        InY ↥(commAut α)

@[expose] def IV2_2_18 : Prop :=
  ∀ (E : Type) [CommGroup E] [Finite E], (∀ e : E, e * e = 1) → Nat.card E = 16 →
    ∀ (X : Subgroup (MulAut E)) (S : Sylow 2 ↥X),
      (∀ s ∈ (S : Subgroup ↥X), s * s = 1) → Nat.card (S : Subgroup ↥X) = 4 →
      Nat.card {e : E // ∀ s ∈ (S : Subgroup ↥X), (s : MulAut E) e = e} = 2 →
      ∀ x ∈ (S : Subgroup ↥X), x ≠ 1 → Nonempty (↥(centralizer ({x} : Set ↥X)) ≃* Z2xS3) →
        ∃ a b : ↥X, a ≠ 1 ∧ a * a = 1 ∧ b ≠ 1 ∧ b * b = 1 ∧ ¬ IsConj a b

end CFSG.GH74.GLS.Bg.TwoGroups
