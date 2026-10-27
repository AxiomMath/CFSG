module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Sec8T84FactTwist : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P B₁ B₂ : Subgroup G), IsOm6M L → IsSylow2Of P L →
    B₁ ≠ B₂ → IsNormalE16In P B₁ → IsNormalE16In P B₂ →
    (∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 → B = B₁ ∨ B = B₂) →
    ∀ γ : G, γ ∈ normalizer (P : Set G) → γ * γ = 1 → InducesOutsideGStar L 6 (-1) γ →
      ∃ r ∈ P, (γ * r) * (γ * r) = 1 ∧ InducesOutsideGStar L 6 (-1) (γ * r) ∧
        Nat.card ↥((B₁ ⊔ B₂) ⊓ centralizer ({γ * r} : Set G)) = 4 ∧
        IsElemAb2 ((B₁ ⊔ B₂) ⊓ centralizer ({γ * r} : Set G)) 2

@[expose] def Sec8T84FactGamInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L → ∀ s : G, s * s = 1 →
    InducesOutsideGStar L 6 (-1) s → ∀ l ∈ L ⊓ centralizer ({s} : Set G),
      (∀ x ∈ layerCent L s, l * l * x = x * (l * l)) → l ∈ layerCent L s ⊔ oddCoreIn L

@[expose] def Sec8T84FactI4m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L → ∀ s : G, orderOf s = 2 →
    s ∈ normalizer (L : Set G) → InducesTypeSome L s 6 (-1) 4 (-1) →
      ∀ A : Subgroup G, IsComponentIn A (L ⊓ centralizer ({s} : Set G)) →
        ∃ u ∈ L ⊓ centralizer ({s} : Set G), orderOf u = 2 ∧ ¬ InnerOn A u

@[expose] def Sec8T84FactOm5Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsOm5Q K →
    ∀ x : G, x ∈ normalizer (K : Set G) → Odd (orderOf x) → InnerOn K x

@[expose] def Sec8T84FactOm5Tab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsOm5Q K → ∀ t : G, orderOf t = 2 →
    t ∈ normalizer (K : Set G) → ∀ A : Subgroup G,
      IsComponentIn A (K ⊓ centralizer ({t} : Set G)) → IsL29 A →
        ∃ u ∈ K ⊓ centralizer ({t} : Set G), orderOf u = 2 ∧ ¬ InnerOn A u

@[expose] def Sec8T84FactS4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (E H P F : Subgroup Y), IsElemAb2 E 4 → E.Normal →
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) → E ⊓ H = ⊥ → E ⊔ H = ⊤ →
    (∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ h ∈ H, h * a * h⁻¹ = b) → IsSylow2Of P ⊤ →
    Sec8T84PFacts Y E P F →
      E ⊔ F ≤ twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y)) ∧
      (∀ y ∈ twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y)),
        (∃ k : ℕ, orderOf y = 3 ^ k) → y ≠ 1 →
          orderOf y = 3 ∧ ∀ u ∈ E ⊔ F, y * u = u * y → u = 1) ∧
      ∀ a : ↥(twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y))) ≃*
          ↥(twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y))),
        (∀ x, a (a x) = x) →
        Nat.card {x : ↥(twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y))) //
          (x : Y) ∈ E ⊔ F ∧ a x = x} = 4 →
        (∀ x : ↥(twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y))),
          (x : Y) ∈ E ⊔ F → a x = x → x * x = 1) →
          ∃ y : ↥(twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y))), orderOf y = 3 ∧ a y = y

end CFSG.OddStandard.SmallF3.Omega
