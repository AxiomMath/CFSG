module

public import CFSG.GH74.E2.CaseIG
public import CFSG.GH74.E2.CaseIIG

public section

namespace CFSG.GH74.E2

open Subgroup

@[expose] def NoCaseIA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G), IsCompCen t K →
    ShapeA6 ↥K → Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    ∀ A : Subgroup G, CaseI t A → ∀ (B : Subgroup G) (c : G), B ≤ A → B ≤ K → Nat.card B = 9 →
      c ∈ A → orderOf c = 3 → (∀ k ∈ K, c * k = k * c) →
      (∀ a ∈ A, ∃ (i : ℤ) (b : G), b ∈ B ∧ a = c ^ i * b) → False

@[expose] def NoCaseIL33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G), IsCompCen t K →
    ShapeL33 ↥K → Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    ∀ A : Subgroup G, CaseI t A → ∀ (B : Subgroup G) (c : G), B ≤ A → B ≤ K → Nat.card B = 9 →
      c ∈ A → orderOf c = 3 → (∀ k ∈ K, c * k = k * c) →
      (∀ a ∈ A, ∃ (i : ℤ) (b : G), b ∈ B ∧ a = c ^ i * b) → False

@[expose] def NoCaseIM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G), IsCompCen t K →
    ShapeM11 ↥K → Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    ∀ A : Subgroup G, CaseI t A → ∀ (B : Subgroup G) (c : G), B ≤ A → B ≤ K → Nat.card B = 9 →
      c ∈ A → orderOf c = 3 → (∀ k ∈ K, c * k = k * c) →
      (∀ a ∈ A, ∃ (i : ℤ) (b : G), b ∈ B ∧ a = c ^ i * b) → False

theorem noCaseIQ8_of_shapes (hA : NoCaseIA6) (hL : NoCaseIL33) (hM : NoCaseIM11) : NoCaseIQ8 := by
  intro G _ _ hH t K hK hsh hQ A hA' B c hBA hBK hB hcA hc hcK hdec
  rcases hsh with h | h | h
  · exact hA G hH t K hK h hQ A hA' B c hBA hBK hB hcA hc hcK hdec
  · exact hL G hH t K hK h hQ A hA' B c hBA hBK hB hcA hc hcK hdec
  · exact hM G hH t K hK h hQ A hA' B c hBA hBK hB hcA hc hcK hdec

@[expose] def NoCaseIIAlphaA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeA6 ↥K → B ≤ K →
    (∀ b ∈ B, ∀ q ∈ Qt t, b * q = q * b) → (∀ k ∈ K, t' * k = k * t') → False

@[expose] def NoCaseIIAlphaL33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeL33 ↥K → B ≤ K →
    (∀ b ∈ B, ∀ q ∈ Qt t, b * q = q * b) → (∀ k ∈ K, t' * k = k * t') → False

@[expose] def NoCaseIIAlphaM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeM11 ↥K → B ≤ K →
    (∀ b ∈ B, ∀ q ∈ Qt t, b * q = q * b) → (∀ k ∈ K, t' * k = k * t') → False

theorem noCaseIIAlpha_of_shapes (hA : NoCaseIIAlphaA6) (hL : NoCaseIIAlphaL33)
    (hM : NoCaseIIAlphaM11) : NoCaseIIAlpha := by
  intro G _ _ hH t t' a A B K hc hK hsh hBK hBQ ht'K
  rcases hsh with h | h | h
  · exact hA G hH t t' a A B K hc hK h hBK hBQ ht'K
  · exact hL G hH t t' a A B K hc hK h hBK hBQ ht'K
  · exact hM G hH t t' a A B K hc hK h hBK hBQ ht'K

@[expose] def NoCaseIIBetaA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeA5 ↥K →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

@[expose] def NoCaseIIBetaL27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeL27 ↥K →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

@[expose] def NoCaseIIBetaA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeA6 ↥K →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

@[expose] def NoCaseIIBetaL217 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeL217 ↥K →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

@[expose] def NoCaseIIBetaL33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeL33 ↥K →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

@[expose] def NoCaseIIBetaM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → ShapeM11 ↥K →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

theorem noCaseIIBeta_of_shapes (hA5 : NoCaseIIBetaA5) (hL7 : NoCaseIIBetaL27)
    (hA6 : NoCaseIIBetaA6) (hL17 : NoCaseIIBetaL217) (hL3 : NoCaseIIBetaL33)
    (hM : NoCaseIIBetaM11) : NoCaseIIBeta := by
  intro G _ _ hH t t' a A B K hc hK hsh hQ hcard
  rcases hsh with h | h | h | h | h | h
  · exact hA5 G hH t t' a A B K hc hK h hQ hcard
  · exact hL7 G hH t t' a A B K hc hK h hQ hcard
  · exact hA6 G hH t t' a A B K hc hK h hQ hcard
  · exact hL17 G hH t t' a A B K hc hK h hQ hcard
  · exact hL3 G hH t t' a A B K hc hK h hQ hcard
  · exact hM G hH t t' a A B K hc hK h hQ hcard

end CFSG.GH74.E2
