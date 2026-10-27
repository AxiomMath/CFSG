module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PinnedB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoLift4
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G]

@[expose] def EgElemAb (B : Subgroup G) : Prop :=
  (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ∀ x ∈ B, x * x = 1

@[expose] def egNL (L A : Subgroup G) : Subgroup G := normalizer (A : Set G) ⊓ L

@[expose] def egOrb (L A : Subgroup G) (a : G) : Set G := {x | ∃ n ∈ egNL L A, n * a * n⁻¹ = x}

@[expose] def egV (A : Subgroup G) (z : G) : Subgroup G := A ⊔ zpowers z

@[expose] def egM (A : Subgroup G) (z : G) : Subgroup G := normalizer (egV A z : Set G)

@[expose] def egLam (A : Subgroup G) (z : G) : Subgroup G := egM A z ⊓ centralizer (A : Set G)

structure LocalSetting (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) : Prop where
  order_z : orderOf z = 2
  z_central : zpowers z ≤ centralizer (L : Set G)
  centralizer_eq : centralizer ({z} : Set G) = L ⊔ zpowers z
  disjoint : Disjoint L (zpowers z)
  sporadic : IsSporadic L .M24
  conj_not_mem : ∀ g : G, g * z * g⁻¹ ∉ L

@[expose] def SextetType (L A : Subgroup G) : Prop :=
  A ≤ L ∧ ∃ e : L ≃* NativeSporadic.M24,
    ∀ x : L, (x : G) ∈ A ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24E1l

@[expose] def OctadType (L B : Subgroup G) : Prop :=
  B ≤ L ∧ ∃ e : L ≃* NativeSporadic.M24,
    ∀ x : L, (x : G) ∈ B ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24B0l

@[expose] def PairType (L A B : Subgroup G) : Prop :=
  A ≤ L ∧ B ≤ L ∧ ∃ e : L ≃* NativeSporadic.M24,
    (∀ x : L, (x : G) ∈ A ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24E1l) ∧
    (∀ x : L, (x : G) ∈ B ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24B0l)

theorem PairType.sextet {L A B : Subgroup G} (h : PairType L A B) : SextetType L A :=
  ⟨h.1, h.2.2.elim fun e he => ⟨e, he.1⟩⟩

theorem PairType.octad {L A B : Subgroup G} (h : PairType L A B) : OctadType L B :=
  ⟨h.2.1, h.2.2.elim fun e he => ⟨e, he.2⟩⟩

structure SextetFacts (L A : Subgroup G) : Prop where
  elem : EgElemAb A
  card_A : Nat.card A = 64
  cent : ∀ l ∈ L, (∀ a ∈ A, l * a = a * l) → l ∈ A
  orbits : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
    (∀ x ∈ A, x ≠ 1 → x ∈ egOrb L A a₁ ∨ x ∈ egOrb L A a₂) ∧ a₂ ∉ egOrb L A a₁ ∧
    Nat.card (egOrb L A a₁) = 45 ∧ Nat.card (egOrb L A a₂) = 18
  five : ∃ r ∈ egNL L A, orderOf r = 5 ∧ Nat.card {a : A | r * (a : G) * r⁻¹ = a} = 4 ∧
    ∃ Q : Subgroup G, Q ≤ egNL L A ∧ Q ≤ normalizer (zpowers r : Set G) ∧ Nat.card Q = 16

structure SextetFactsQ (L A : Subgroup G) : Prop where
  gen45 : ∀ a₁ ∈ A, a₁ ≠ 1 → Nat.card (egOrb L A a₁) = 45 →
    Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A
  fix : ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
    (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x
  omega : ∃ w ∈ egNL L A, w * w * w = 1 ∧
    (∀ n ∈ egNL L A, ∃ a ∈ A, n * w * n⁻¹ = w * a ∨ n * w * n⁻¹ = w⁻¹ * a) ∧
    ∀ a ∈ A, w * a * w⁻¹ = a → a = 1

@[expose] def ebasis4 (e : Fin 4 → G) (c : Fin 4 → ZMod 2) : G :=
  (List.ofFn fun i => e i ^ (c i).val).prod

@[expose] def LiftDataB (L B : Subgroup G) : Prop :=
  ∃ (e : Fin 4 → G) (s t : G),
    (∀ i, e i ∈ B) ∧
    (∀ c d : Fin 4 → ZMod 2, ebasis4 e c = ebasis4 e d → c = d) ∧
    s ∈ egNL L B ∧ t ∈ egNL L B ∧ s * s = 1 ∧ t * t = 1 ∧ (s * t) * (s * t) = 1 ∧
    (∀ i, s * e i * s⁻¹ = ebasis4 e (fun j => CFSG.EvenSporadicStandard.M23Std.liftA1 i j)) ∧
    (∀ i, t * e i * t⁻¹ = ebasis4 e (fun j => CFSG.EvenSporadicStandard.M23Std.liftA2 i j))

@[expose] def SplitDataB (L B : Subgroup G) : Prop :=
  ∀ (z : G) (W : Subgroup G),
    z ∈ W → z * z = 1 → z ∉ B → (∀ h ∈ egNL L B, z * h = h * z) → (∀ u ∈ B, z * u = u * z) →
    B ≤ W → (∀ w ∈ W, ∀ u ∈ B, w * u = u * w) → (∀ w ∈ W, w * w ∈ B) →
    (∀ h ∈ egNL L B, ∀ w ∈ W, h * w * h⁻¹ ∈ W) →
    (∀ w ∈ W, z * (w⁻¹ * z * w) ∈ B) → (∀ u ∈ B, ∃ w ∈ W, z * (w⁻¹ * z * w) = u) →
    (∀ w ∈ W, z * w = w * z → w ∈ B ⊔ zpowers z) →
    ∃ Y : Subgroup G, B ≤ Y ∧ Y ≤ W ∧ z ∉ Y ∧ (∀ h ∈ egNL L B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) ∧
      ∀ w ∈ W, w ∈ Y ∨ z * w ∈ Y

structure OctadBasics (L B : Subgroup G) : Prop where
  elem : EgElemAb B
  card_B : Nat.card B = 16
  big_N : 20160 < Nat.card (egNL L B)
  cent : ∀ l ∈ L, (∀ b ∈ B, l * b = b * l) → l ∈ B
  trans : ∀ x ∈ B, ∀ y ∈ B, x ≠ 1 → y ≠ 1 → ∃ n ∈ egNL L B, n * x * n⁻¹ = y
  fix : ∀ x ∈ B, x ≠ 1 → ∀ w ∈ B,
    (∀ n ∈ egNL L B, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x

structure CompatFacts (L A B : Subgroup G) : Prop where
  B_le_NA : B ≤ egNL L A
  A_le_NB : A ≤ egNL L B
  card_inf : Nat.card (A ⊓ B : Subgroup G) = 4
  comm_A : ∀ x ∈ B, x ∉ A →
    (∀ a ∈ A, a * (x * a⁻¹ * x⁻¹) ∈ B) ∧
      ∀ b ∈ A ⊓ B, ∃ a ∈ A, b = a * (x * a⁻¹ * x⁻¹)
  Z_ex : ∃ Z : Subgroup G, Z ≤ A ∧ EgElemAb Z ∧ Nat.card Z = 16 ∧ Z ⊓ B = ⊥ ∧
    Subgroup.closure {x : G | x ∈ Z ∧ (∀ b ∈ B, b * (x * b⁻¹ * x⁻¹) ∈ A ⊓ B) ∧
      ∀ c ∈ A ⊓ B, ∃ b ∈ B, c = b * (x * b⁻¹ * x⁻¹)} = Z ∧
    ∃ y ∈ egNL L B, y ∈ normalizer (Z : Set G) ∧ y * y * y = 1 ∧
      (∀ b ∈ B, y * b * y⁻¹ = b ↔ b ∈ A) ∧
      Subgroup.closure {w : G | ∃ x ∈ Z, w = x * (y * x⁻¹ * y⁻¹)} = Z

structure TranslationData (A : Subgroup G) (z : G) : Prop where
  conj : ∀ m ∈ egM A z, ∃ a ∈ A, m * z * m⁻¹ = z * a
  trans : ∀ a ∈ A, ∃ t ∈ egLam A z, t * z * t⁻¹ = z * a

structure CData (A : Subgroup G) (z : G) (C : Subgroup G) : Prop where
  A_le : A ≤ C
  C_le : C ≤ egLam A z
  norm : ∀ m ∈ egM A z, ∀ c ∈ C, m * c * m⁻¹ ∈ C
  z_not_mem : z ∉ C
  card : Nat.card C = 4096
  comm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c
  sq_mem : ∀ c ∈ C, c * c ∈ A
  comm_z : ∀ c ∈ C, z * c * z⁻¹ * c⁻¹ ∈ A
  onto : ∀ a ∈ A, ∃ c ∈ C, z * c * z⁻¹ * c⁻¹ = a
  lam_eq : ∀ t ∈ egLam A z, t ∈ C ∨ z * t ∈ C
  dichotomy : (∀ c ∈ C, c * c = 1) ∨ (∀ c ∈ C, z * c * z⁻¹ = c⁻¹)

structure NData (B : Subgroup G) (z : G) (D : Subgroup G) : Prop where
  B_le : B ≤ D
  D_le : D ≤ egLam B z
  elem : EgElemAb D
  card : Nat.card D = 256
  z_not_mem : z ∉ D
  norm : ∀ n ∈ egM B z, ∀ d ∈ D, n * d * n⁻¹ ∈ D
  comm_z : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ ∈ B
  onto : ∀ b ∈ B, ∃ d ∈ D, z * d * z⁻¹ * d⁻¹ = b
  lam_eq : ∀ t ∈ egLam B z, t ∈ D ∨ z * t ∈ D

end CFSG.EvenSporadicStandard.M24Std
