module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def IsHallTwoPrimeOf (D X : Subgroup G) : Prop :=
  D ≤ X ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.relIndex X = 2 ^ k

@[expose] def nonIdentity (Z : Subgroup G) : Set G := {z | z ∈ Z ∧ z ≠ 1}

@[expose] def ActsRegularlyOn (B : Subgroup G) (Δ : Set G) : Prop :=
  (∀ b ∈ B, ∀ z ∈ Δ, b⁻¹ * z * b ∈ Δ) ∧
    (∀ z ∈ Δ, ∀ z' ∈ Δ, ∃ b ∈ B, b⁻¹ * z * b = z') ∧
    ∀ z ∈ Δ, ∀ b ∈ B, b⁻¹ * z * b = z → b = 1

open scoped Classical in
@[expose] noncomputable def lin2Z (L R : Subgroup G) : Subgroup G :=
  if centerOf L = ⊥ then centerOf R else centerOf L

@[expose] def strongClosure (A T : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | y ∈ T ∧ ∃ a ∈ A, ∃ g : G, y = g⁻¹ * a * g}

@[expose] def weakClosure (A T : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : conjR A g ≤ T), conjR A g

@[expose] def IsSpecialTwoGroup (P : Subgroup G) : Prop :=
  IsPGroup 2 P ∧ ⁅P, P⁆ = centerOf P ∧ ⁅P, P⁆ ≠ ⊥ ∧ IsElemAbelian 2 (centerOf P) ∧
    ∀ x ∈ P, x ^ 2 ∈ ⁅P, P⁆

@[expose] def lin2Delta (R Z : Subgroup G) (x : G) : Set G :=
  {u | u ∈ centerOf R ∧ u ∉ Z ∧ u ∉ conjR Z x}

structure Lin2Cfg (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (n : ℕ)
    (D : Subgroup G) : Prop where
  cs : ConstrainedSetting G T M H S L
  single : conjJoin S L = L
  one_lt : 1 < n
  lin2 : IsLin2Type L n
  hall : IsHallTwoPrimeOf D (L ⊓ M)
  norm : D ≤ Subgroup.normalizer ((L ⊓ S : Subgroup G) : Set G)

structure Lin2Cfg2 (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (n : ℕ)
    (D : Subgroup G) : Prop where
  cs : ConstrainedSetting G T M H S L
  double : conjJoin S L ≠ L
  one_lt : 1 < n
  lin2 : IsLin2Type L n
  hall : IsHallTwoPrimeOf D (conjJoin S L ⊓ M)
  norm : D ≤ Subgroup.normalizer ((conjJoin S L ⊓ S : Subgroup G) : Set G)

@[expose] def Lin2BProps (T S R D B : Subgroup G) : Prop :=
  D ≤ B ∧ IsHallTwoPrimeOf B (T ⊔ D) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
    ((T ⊔ D : Subgroup G) : Set G) = (T : Set G) * (B : Set G) ∧
    S ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) ∧
    B ≤ Subgroup.normalizer (R : Set G) ∧
    T ⊔ D ≤ Subgroup.normalizer ((R ⊔ B : Subgroup G) : Set G) ∧
    R ⊓ Subgroup.centralizer (B : Set G) = ⊥ ∧
    R ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T ∧
    R ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
    ∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S → B = D ⊔ conjR D x

@[expose] def Lin2Statement
    (P : ∀ (G : Type) [Group G] [Finite G] (T M H S L D : Subgroup G) (n : ℕ),
      Lin2Cfg G T M H S L n D → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L D : Subgroup G) (n : ℕ)
    (h : Lin2Cfg G T M H S L n D), P G T M H S L D n h

end CFSG.QuasithinUnique.Lin2
