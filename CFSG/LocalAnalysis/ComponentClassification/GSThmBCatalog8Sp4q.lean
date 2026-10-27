module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Q3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat8

abbrev ordL2 (q : ℕ) : ℕ := q * (q ^ 2 - 1) / 2

structure IsAdmQ (K₀ : Type) [Group K₀] (q : ℕ) (α : MulAut K₀) : Prop where
  sq : α * α = 1
  out : α ∉ Inn K₀
  dvd : ordL2 (q ^ 2) ∣ Nat.card (Eight.fixSubgroup α)

end Cat8

@[expose] def CFSp4F2 : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ α : MulAut K₀, Cat8.IsAdmQ K₀ (p ^ f) α →
    ∀ Q : Subgroup (MulAut K₀),
      Q ≤ (Cat8.Inn K₀ ⊔ zpowers α) ⊓ centralizer ({α} : Set (MulAut K₀)) →
      (∃ T : Sylow 2 ↥((Cat8.Inn K₀ ⊔ zpowers α) ⊓ centralizer ({α} : Set (MulAut K₀))),
        (T : Subgroup _) = Q.subgroupOf
          ((Cat8.Inn K₀ ⊔ zpowers α) ⊓ centralizer ({α} : Set (MulAut K₀)))) →
      ∃ g : MulAut K₀, g ∈ Cat8.Inn K₀ ∧ g ∈ normalizer (Q : Set (MulAut K₀)) ∧ g ∉ Q ∧
        g * g ∈ Q ∧ α * (g⁻¹ * α * g) ∈ Cat8.Inn K₀

@[expose] def CFL2Inv : Prop :=
  ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
    IsSec8JType Y₀ p f → ∀ φ : MulAut Y₀, φ * φ = 1 → φ ≠ 1 →
    ∃ Lφ : Subgroup (MulAut Y₀), Lφ ≤ centralizer ({φ} : Set (MulAut Y₀)) ∧
      (∀ T : Subgroup (MulAut Y₀), T ≤ centralizer ({φ} : Set (MulAut Y₀)) → ⁅T, T⁆ = T →
        T ≤ Lφ) ∧
      Nat.card Lφ ≤ Cat8.ordL2 (p ^ f) ∧
      (∀ N : Subgroup (MulAut Y₀), N ≤ Lφ → (N.subgroupOf Lφ).Normal → Odd (Nat.card N) →
        N = ⊥) ∧
      (Nat.card Lφ = Cat8.ordL2 (p ^ f) → ∀ y ∈ centralizer ({φ} : Set (MulAut Y₀)),
        (∀ l ∈ Lφ, y * l = l * y) → y = 1 ∨ y = φ)

@[expose] def CFSp4Layer : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
    IsSec8Socle K₀ p f → ∀ ε : MulAut K₀, Cat8.IsAdmQ K₀ (p ^ f) ε →
    ∀ α : MulAut K₀, α * α = 1 → ∀ R R₁ : Subgroup K₀, R ≤ layerIn (Eight.fixSubgroup α) →
      (R.subgroupOf (layerIn (Eight.fixSubgroup α))).Normal → R₁ ≤ R →
      (R₁.subgroupOf R).Normal → Odd (Nat.card R₁) → (∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ R₁) →
      R.relIndex (layerIn (Eight.fixSubgroup α)) ≤ Cat8.ordL2 (p ^ f) →
      R.relIndex (layerIn (Eight.fixSubgroup α)) = Cat8.ordL2 (p ^ f) ∧
        ∃ y ∈ Cat8.Inn K₀ ⊔ zpowers ε, y * α = α * y ∧
          (∀ t ∈ layerIn (Eight.fixSubgroup α), y t = t) ∧
          (orderOf y = 4 ∨ (Odd (orderOf y) ∧ y ≠ 1))

@[expose] def CFSec8JOrder : Prop :=
  ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8JType Y₀ p f → Nat.card Y₀ = Cat8.ordL2 ((p ^ f) ^ 2)

@[expose] def CFSec8Order : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (Y₀ : Type) [Group Y₀] [Finite Y₀] (p f : ℕ), p.Prime →
    p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f → IsSec8Socle K₀ p f → IsSec8JType Y₀ p f →
      Nat.card Y₀ < Nat.card K₀

end CFSG.ComponentClassification.GSThmB
