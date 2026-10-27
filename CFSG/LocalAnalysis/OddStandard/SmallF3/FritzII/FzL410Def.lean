module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316B
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G]

@[expose] def fz410F (P : Subgroup G) (t s : G) : Subgroup G :=
  P ⊓ centralizer ({t * s} : Set G)

@[expose] def fz410CR (R : Subgroup G) (i : G) : Subgroup G :=
  R ⊓ centralizer ({i} : Set G)

@[expose] def fz410ZCR (R : Subgroup G) (i : G) : Subgroup G :=
  fz410CR R i ⊓ centralizer ((fz410CR R i : Subgroup G) : Set G)

structure Fz410Fus (R Z : Subgroup G) (i : G) : Prop where
  mem : i ∈ R
  card_C : Nat.card (fz410CR R i) = 64
  sq_pair : ∃ x ∈ fz410CR R i, ∃ y ∈ fz410CR R i, x ^ 2 ≠ 1 ∧ y ^ 2 ≠ 1 ∧ x ^ 2 ≠ y ^ 2
  card_ZC : Nat.card (fz410ZCR R i) = 8
  cls : ∀ r ∈ R, ∃ z ∈ Z, r * i * r⁻¹ = i * z

@[expose] def fz410CS (T : Subgroup G) (t a b : G) : Subgroup G :=
  T ⊓ centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)

@[expose] def fz410ZCS (T : Subgroup G) (t a b : G) : Subgroup G :=
  fz410CS T t a b ⊓ centralizer ((fz410CS T t a b : Subgroup G) : Set G)

structure Fz410Facts (t s : G) (Z E P Q R T : Subgroup G) : Prop where
  charR : ∀ u ∈ normalizer (T : Set G), ∀ x ∈ R, u * x * u⁻¹ ∈ R
  charP : ∀ n ∈ normalizer (R : Set G), ∀ x ∈ P, n * x * n⁻¹ ∈ P
  rq : ∀ x ∈ R, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ E
  qc : ∀ x ∈ R, ((∀ e ∈ E, x * e = e * x) ↔ x ∈ Q)
  sqZ : ∀ x ∈ R, x ^ 2 ∈ Z
  P_comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  ef : ∀ a ∈ E, a ∈ fz410F P t s → a ∈ Z
  centP : ∀ i ∈ R, i ∉ P →
    ((∀ a ∈ P, (i * a = a * i ↔ a ∈ E)) ∨ (∀ a ∈ P, (i * a = a * i ↔ a ∈ fz410F P t s)) ∨
      (∀ a ∈ P, i * a = a * i → a ^ 2 = 1))
  invF : ∀ i ∈ R, i ∉ P → i ^ 2 = 1 → (∀ a ∈ P, (i * a = a * i ↔ a ∈ fz410F P t s)) →
    ∃ e ∈ E, i = e * (t * s)
  fus_t : Fz410Fus R Z t
  fus_ets : ∀ e ∈ E, Fz410Fus R Z (e * (t * s))
  card_S : Nat.card ↥(T ⊓ centralizer ({t} : Set G)) = 128
  slem : ∀ a ∈ T ⊓ centralizer ({t} : Set G), ∀ b ∈ T ⊓ centralizer ({t} : Set G),
    a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a →
    Nat.card (fz410CS T t a b) = 64 → (∀ x ∈ fz410CS T t a b, x ^ 4 = 1) →
    Nat.card (fz410ZCS T t a b) = 8 → fz410CS T t a b ≤ R

@[expose] def fz410M (R E : Subgroup G) : Subgroup G :=
  normalizer (R : Set G) ⊓ normalizer (E : Set G)

structure Fz410IsOm (E P Q A : Subgroup G) : Prop where
  E_le : E ≤ A
  le_Q : A ≤ Q
  card : Nat.card A = 2 * Nat.card E
  not_le_P : ¬ A ≤ P

abbrev Fz410Om (E P Q : Subgroup G) : Type := {A : Subgroup G // Fz410IsOm E P Q A}

end CFSG.OddStandard.SmallF3.FritzII
