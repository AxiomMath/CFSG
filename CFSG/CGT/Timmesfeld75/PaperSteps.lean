module

public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def SimpleCaseUpTo (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
    (∃ a b : G, a * b ≠ b * a) → ∀ T : Subgroup G, IsWC T → 4 ≤ Nat.card T → ListGroup G ∧
      ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y

variable {G : Type} [Group G]

structure MaxPair (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  conj : ∃ x : G, T₁ = conjSubgroup x T
  ne : T₁ ≠ T
  nontriv : normIn T T₁ ≠ ⊥
  maximal : ∀ g : G, conjSubgroup g T ≠ T →
    Nat.card (normIn T (conjSubgroup g T)) ≤ Nat.card (normIn T T₁)

@[expose] def hSub (T L₁ : Subgroup G) : Subgroup G :=
  T ⊔ ⨆ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g L₁

@[expose] def NaturalSL (T H : Subgroup G) (n m : ℕ) : Prop :=
  ∃ _ : (T.subgroupOf H).Normal,
    ∃ (e : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 m))
      (φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m)),
      ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
        φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
          Multiplicative.ofAdd (((e (QuotientGroup.mk h) : SL(n, GaloisField 2 m)) :
            Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ t)))

@[expose] def IsHatA (k : ℕ) (Y : Type) [Group Y] : Prop :=
  commutator Y = ⊤ ∧ ∃ Z : Subgroup Y, Z ≤ Subgroup.center Y ∧ Nat.card Z ∣ 3 ∧
    ∃ _ : Z.Normal, Nonempty (Y ⧸ Z ≃* alternatingGroup (Fin k))

structure StepHyp (T T₁ : Subgroup G) : Prop where
  finite : Finite G
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  pair : MaxPair T T₁
  card : 4 ≤ Nat.card T
  ind : SimpleCaseUpTo (Nat.card G)

@[expose] def Step57 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ →
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y

@[expose] def Step511 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → 4 < Nat.card T →
    ∃ n m : ℕ, Nat.card T / Nat.card (normIn T T₁) = 2 ^ m ∧ Nat.card T = (2 ^ m) ^ n ∧
      (NaturalSL T (hSub T (normIn T₁ T)) n m ∨
        (Nat.card T = 16 ∧ ∃ _ : (T.subgroupOf (hSub T (normIn T₁ T))).Normal,
          (IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
            IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))))

@[expose] def Step69 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Nat.card T = 4 → ListGroup G

@[expose] def Step68 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → ∀ m : ℕ, 2 ≤ m →
    Nat.card T / Nat.card (normIn T T₁) = 2 ^ m → Nat.card T = (2 ^ m) ^ 2 →
    NaturalSL T (hSub T (normIn T₁ T)) 2 m → ListGroup G

@[expose] def Step610 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Nat.card T = 16 →
    ∀ _ : (T.subgroupOf (hSub T (normIn T₁ T))).Normal,
      (IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
        IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) → ListGroup G

@[expose] def Step79 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → ∀ n m : ℕ, 4 ≤ n → 1 ≤ m →
    ¬ (n = 4 ∧ m = 1) → Nat.card T / Nat.card (normIn T T₁) = 2 ^ m →
    Nat.card T = (2 ^ m) ^ n → NaturalSL T (hSub T (normIn T₁ T)) n m → ListGroup G

@[expose] def Step711 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → ∀ m : ℕ, 2 ≤ m →
    Nat.card T / Nat.card (normIn T T₁) = 2 ^ m → Nat.card T = (2 ^ m) ^ 3 →
    NaturalSL T (hSub T (normIn T₁ T)) 3 m → ListGroup G

@[expose] def Step81 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ →
    Nat.card T / Nat.card (normIn T T₁) = 2 ^ 1 → Nat.card T = (2 ^ 1) ^ 3 →
    NaturalSL T (hSub T (normIn T₁ T)) 3 1 → ListGroup G

@[expose] def Step82 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ →
    Nat.card T / Nat.card (normIn T T₁) = 2 ^ 1 → Nat.card T = (2 ^ 1) ^ 4 →
    NaturalSL T (hSub T (normIn T₁ T)) 4 1 → ListGroup G

@[expose] def BenderListInput : Prop :=
  ∀ (K : Type) [Group K], CFSG.BenderSuzuki.IsBenderGroup K → ListGroup K

@[expose] def BenderTransitiveInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (T : Subgroup K), StrongWC T → T ≠ ⊥ →
    CFSG.BenderSuzuki.IsBenderGroup K → ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set K), g * x * g⁻¹ = y

end CFSG.CGT.Timmesfeld75
