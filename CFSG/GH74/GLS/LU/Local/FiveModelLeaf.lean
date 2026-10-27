module

public import CFSG.GH74.GLS.LU.Local.FiveBundles

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.LU.Local.Five

abbrev Z4Z4 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

variable {Gs : Type} [Group Gs]

@[expose] def IsTorus (z' u' : Gs) (K₁' K₂' H' : Subgroup Gs) : Prop :=
  H' ≤ centralizer ((UU z' u' : Subgroup Gs) : Set Gs) ∧ Nonempty (↥H' ≃* Z4Z4) ∧
    ∀ h ∈ H', cjL h K₁' = K₁' ∧ cjL h K₂' = K₂'

structure FiveModelBase (z' : Gs) (S' : Sylow 2 Gs) : Prop where
  lay_eq : layerTimesSylow z' (S' : Subgroup Gs) = Cz z'
  card_C : Nat.card ↥(Cz z') = 28800
  A0_bot : A0 z' = ⊥

@[expose] def FiveModelBaseLeaf : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs], LieModel Gs .PSL 4 5 1 →
    ∀ (z' : Gs) (S' : Sylow 2 Gs), (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
      orderOf z' = 2 → FiveModelBase z' S'

structure FiveModelFacts (z' : Gs) (S' : Sylow 2 Gs) (K₁' K₂' : Subgroup Gs) (t' u' : Gs) : Prop where
  P_two : IsPGroup 2 ↥(centralizer ((UU z' u' : Subgroup Gs) : Set Gs))
  P_card : Nat.card ↥(centralizer ((UU z' u' : Subgroup Gs) : Set Gs)) = 64
  torus_exists : ∃ H' : Subgroup Gs, IsTorus z' u' K₁' K₂' H'
  torus_unique : ∀ A B : Subgroup Gs, IsTorus z' u' K₁' K₂' A → IsTorus z' u' K₁' K₂' B → A = B
  torus_facts : ∀ H' : Subgroup Gs, IsTorus z' u' K₁' K₂' H' → z' ∈ H' ∧ u' ∈ H' ∧
    (∀ p ∈ centralizer ((UU z' u' : Subgroup Gs) : Set Gs), cjL p H' = H') ∧
    (∀ p ∈ centralizer ((UU z' u' : Subgroup Gs) : Set Gs), p * p ∈ H')
  w_exists : ∃ w' ∈ K₁', w' * w' = z' ∧ w' * u' * w'⁻¹ = u' * z'
  t_conj : ∃ p : Gs, p * z' = z' * p ∧ p * u' = u' * p ∧ p * t' * p⁻¹ = z' * t'
  X1_exists : ∀ (H' : Subgroup Gs) (w' : Gs), IsTorus z' u' K₁' K₂' H' →
    (w' ∈ K₁' ∧ w' * w' = z' ∧ w' * u' * w'⁻¹ = u' * z') →
    ∃ X₁' : Subgroup Gs, X₁' ≤ K₁' ∧ Nat.card ↥X₁' = 5 ∧ (∀ h ∈ H', cjL h X₁' = X₁') ∧
      Subgroup.closure ((X₁' : Set Gs) ∪ {w'}) = K₁' ∧ (∀ x ∈ X₁', u' * x * u'⁻¹ = x⁻¹) ∧
      normalizer ((XB t' X₁' : Subgroup Gs) : Set Gs) ⊓ Cz z' = XB t' X₁' ⊔ K₁' ⊔ H' ∧
      centralizer ((XB t' X₁' : Subgroup Gs) : Set Gs) ⊓ Cz z' = XB t' X₁' ⊔ K₁' ∧
      normalizer ((XX t' X₁' : Subgroup Gs) : Set Gs) ⊓ Cz z' = XX t' X₁' ⊔ H' ⊔ zpowers t' ∧
      (∀ R : Subgroup Gs, IsSylowIn 5 R (Cz z') → (∀ h ∈ H', cjL h R = R) →
        ∃ w ∈ zpowers w' ⊔ zpowers (t' * w' * t'⁻¹), R = cjL w (XX t' X₁')) ∧
      (∀ A : Subgroup Gs, A ≤ XX t' X₁' → Nat.card ↥A = 5 → (∀ h ∈ H', cjL h A = A) →
        A = X₁' ∨ A = XB t' X₁') ∧
      Nat.card ↥(XZ t' X₁') = 5
  diag : ∀ τ : Gs, τ ∈ Cz z' → τ * τ = 1 → τ ≠ 1 → τ ≠ z' → ∀ Z : Subgroup Gs, Z ≤ Cz z' →
    Nat.card ↥Z = 5 → (∀ s ∈ Z, τ * s = s * τ) →
    ∃ A : Subgroup Gs, A ≤ K₁' ⊔ K₂' ∧ IsElemAb 5 A ∧ Nat.card ↥A = 25 ∧
      A ⊓ (zpowers z' ⊔ zpowers τ) = ⊥ ∧
      centralizer ((Z : Subgroup Gs) : Set Gs) ⊓ Cz z' = A ⊔ (zpowers z' ⊔ zpowers τ) ∧
      (∀ g ∈ centralizer ((Z : Subgroup Gs) : Set Gs) ⊓ Cz z', ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
      ∀ v ∈ Cz z', v ∈ normalizer (K₁' : Set Gs) → (∀ s ∈ Z, v * s * v⁻¹ = s⁻¹) →
        ∀ a ∈ A, v * a * v⁻¹ = a⁻¹
  no_inv : ∀ H' : Subgroup Gs, IsTorus z' u' K₁' K₂' H' → ∀ R : Subgroup Gs, R ≤ Cz z' →
    (∀ h ∈ H', cjL h R = R) → (∀ r ∈ R, ¬ 2 ∣ orderOf r ∧ ¬ 5 ∣ orderOf r) → R = ⊥
  sylow_torus : ∀ A : Subgroup Gs, (∀ h ∈ A, h * z' = z' * h ∧ h * u' = u' * h) →
    Nonempty (↥A ≃* Z4Z4) → (∃ R : Subgroup Gs, IsSylowIn 5 R (Cz z') ∧ ∀ h ∈ A, cjL h R = R) →
    ∀ h ∈ A, cjL h K₁' = K₁' ∧ cjL h K₂' = K₂'

@[expose] def FiveModelLeaf : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs], LieModel Gs .PSL 4 5 1 →
    ∀ (z' : Gs) (S' : Sylow 2 Gs) (K₁' K₂' : Subgroup Gs) (t' u' : Gs),
      LUComps Gs 5 z' K₁' K₂' → LUSyl Gs z' S' K₁' K₂' t' u' →
        FiveModelFacts z' S' K₁' K₂' t' u'

end CFSG.GH74.GLS.LU.Local.Five
