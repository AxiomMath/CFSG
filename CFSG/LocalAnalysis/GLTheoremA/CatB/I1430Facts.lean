module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1430TwoLocal (H : Type) [Group H] [Finite H] (r : ℕ) : Prop :=
  ∃ U E : Subgroup H, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set H) ∧
    IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r

@[expose] def I1430Model {Q : Type} [Group Q] [Finite Q] (K I₀ : Subgroup Q) (y : Q) : Prop :=
  K.Normal ∧ CFSG.Open.IsQuasisimple ↥K ∧ (∀ z ∈ Subgroup.center ↥K, ∃ n : ℕ, z ^ 3 ^ n = 1) ∧
    y ∈ Subgroup.normalizer (K : Set Q) ∧ y ^ 3 = 1 ∧ ¬ K ≤ Subgroup.centralizer ({y} : Set Q) ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Q)) I₀ ∧ IsTypeWithCenter 3 I₀ isA6 1 ∧
    IsCatalogGroup (↥K ⧸ Subgroup.center ↥K)

@[expose] def isBOfTwo (ℓ : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B m q => m = ℓ ∧ q.card = 2
    | _ => False

@[expose] def I1430Out : TauCeti.CFSGIndex → Prop := fun i =>
  isType1430 i ∨ (∃ n : ℕ, 12 ≤ n ∧ isAltN n i) ∨ sporIs .Suz i ∨ sporIs .ONan i ∨
    (∃ ℓ : ℕ, 4 ≤ ℓ ∧ isBOfTwo ℓ i)

@[expose] def I1430Cls : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ : Subgroup Q) (y : Q), I1430Model K I₀ y →
    catalogIs (↥K ⧸ Subgroup.center ↥K) I1430Out ∧
    (catalogIs (↥K ⧸ Subgroup.center ↥K) (sporIs .ONan) → Nat.card (Subgroup.center ↥K) = 1) ∧
    (catalogIs (↥K ⧸ Subgroup.center ↥K) isSp48 →
      ¬ ∃ g ∈ K, ∀ k ∈ K, y⁻¹ * k * y = g * k * g⁻¹)

@[expose] def I1430M23Alt : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
    (∀ z ∈ Subgroup.center H, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    ∀ n : ℕ, 12 ≤ n → catalogIs (H ⧸ Subgroup.center H) (isAltN n) →
      I1430TwoLocal H (3 + CFSG.Open.pRank 3 (Subgroup.center H))

@[expose] def I1430M23Suz : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
    (∀ z ∈ Subgroup.center H, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    catalogIs (H ⧸ Subgroup.center H) (sporIs .Suz) →
      I1430TwoLocal H (3 + CFSG.Open.pRank 3 (Subgroup.center H))

@[expose] def I1430M23ON : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
    (∀ z ∈ Subgroup.center H, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    catalogIs (H ⧸ Subgroup.center H) (sporIs .ONan) → Nat.card (Subgroup.center H) = 1 →
      I1430TwoLocal H (3 + CFSG.Open.pRank 3 (Subgroup.center H))

@[expose] def I1430M23Chev : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
    (∀ z ∈ Subgroup.center H, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    ∀ ℓ : ℕ, 4 ≤ ℓ → catalogIs (H ⧸ Subgroup.center H) (isBOfTwo ℓ) →
      I1430TwoLocal H (3 + CFSG.Open.pRank 3 (Subgroup.center H))

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
