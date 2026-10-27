module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76a

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank

section Facts

variable {G : Type} [Group G]

@[expose] def DeltaCentral (A : Subgroup G) (p : G) (Z : Subgroup G) : Prop :=
  ∀ x ∈ A ⊓ centralizer ({p} : Set G), x ∈ centralizer (conjCommuting A p) →
    (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Z

structure DeltaNormal (A : Subgroup G) (p : G) (Z : Subgroup G) : Prop where
  le : Z ≤ A ⊓ centralizer ({p} : Set G)
  le_normalizer : A ⊓ centralizer ({p} : Set G) ≤ normalizer (Z : Set G)
  isPGroup : IsPGroup 2 Z
  le_centralizer : Z ≤ centralizer (conjCommuting A p)

@[expose] def NoPairOrbit (A : Subgroup G) (p : G) : Prop :=
  ∀ u ∈ A ⊓ centralizer ({p} : Set G), u ^ 2 = 1 →
    (∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u ∨ a * u * a⁻¹ = u * p) →
      ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u

end Facts

@[expose] def ClassicalModel.IsAlphaClass {G : Type} [Group G] {A : Subgroup G}
    (D : ClassicalModel A) (p : G) : Prop :=
  match D.family with
  | .linear => ∃ ℓ : ℕ, D.HasRank p ℓ
  | .unitary => ∃ ℓ : ℕ, D.HasRank p ℓ
  | .symplectic => (∃ ℓ : ℕ, D.SuzukiType p .a ℓ) ∨ D.SuzukiType p .b 1
  | .orthPlus => ∃ ℓ : ℕ, D.SuzukiType p .a ℓ
  | .orthMinus => ∃ ℓ : ℕ, D.SuzukiType p .a ℓ

@[expose] def DeltaAlpha (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = fam → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ p : G, D.IsAlphaClass p → DeltaCentral A p (D.alpha p)

@[expose] def AutAlpha (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = fam → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ p : G, D.IsAlphaClass p →
        RegularOn A (D.alpha p) (nonidentity (D.alpha p)) ∧ AutCyclic A (D.alpha p) (D.q - 1)

@[expose] def PairOrbitFree (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = fam → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ (p : G) (ℓ : ℕ), D.HasRank p ℓ → NoPairOrbit A p

@[expose] def SymplecticJ23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), (1 < ℓ ∧ D.SuzukiType p .b ℓ) ∨ D.SuzukiType p .c ℓ →
        ∃ a b : G, ((1 < ℓ ∧ D.SuzukiType p .b ℓ ∧ D.SuzukiType a .a (ℓ - 1)) ∨
            (D.SuzukiType p .c ℓ ∧ D.SuzukiType a .a ℓ)) ∧ D.SuzukiType b .b 1 ∧
          DeltaNormal A p (D.alpha a ⊔ D.alpha b) ∧ DeltaCentral A p (D.alpha a ⊔ D.alpha b) ∧
          D.alpha b ≤ centralizer (D.alpha a : Set G) ∧ p ∉ D.alpha a ∧ p ∉ D.alpha b ∧
          RegularOn A (D.alpha a ⊔ D.alpha b)
            {j | j ∈ D.alpha a ⊔ D.alpha b ∧ j ∉ D.alpha a ∧ j ∉ D.alpha b} ∧
          AutDiagonal A (D.alpha a ⊔ D.alpha b) (D.alpha a) (D.alpha b) (D.q - 1)

@[expose] def OrthJ4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    (D.family = .orthPlus ∨ D.family = .orthMinus) → CFSG.Open.IsQuasisimple ↥A →
      Odd (Nat.card (center A)) → 4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), D.SuzukiType p .c ℓ →
        ∃ Z : Subgroup G, DeltaNormal A p Z ∧ DeltaCentral A p Z ∧
          RegularOn A Z (nonidentity Z) ∧ AutCyclic A Z (D.q - 1)

@[expose] def Classical222Facts : Prop :=
  (∀ fam : Family, DeltaAlpha fam) ∧ (∀ fam : Family, AutAlpha fam) ∧
    (∀ fam : Family, PairOrbitFree fam) ∧ SymplecticJ23 ∧ OrthJ4

section Split

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def CaseI (D : ClassicalModel A) (p : G) : Prop :=
  match D.family with
  | .linear => Case1 D p
  | .unitary => Case1 D p
  | .symplectic => Case1 D p ∨ Case23 D p
  | .orthPlus => Case1 D p ∨ Case4 D p
  | .orthMinus => Case1 D p ∨ Case4 D p

@[expose] def CaseQTwo (D : ClassicalModel A) (T : Subgroup G) (t : G) : Prop :=
  match D.family with
  | .linear => D.HasRank t 2
  | .unitary => False
  | .symplectic => Odd (Nat.card (center A)) ∧ Nat.card T = 4 ∧
      ∃ a ∈ A ⊓ centralizer ({t} : Set G), a ∈ normalizer (T : Set G) ∧
        a ∉ centralizer (T : Set G)
  | .orthPlus => False
  | .orthMinus => False

end Split

@[expose] def Classical222Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    4 ≤ D.q → Hyp221 A T → Conclusion222 A T D.q (CaseI D) fun _ => False

@[expose] def Classical222Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.q = 2 → Hyp221 A T → ∃ t ∈ T, t ≠ 1 ∧ CaseQTwo D T t

end CFSG.ComponentClassification.RankTwoClassical
