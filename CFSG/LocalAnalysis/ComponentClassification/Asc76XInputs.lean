module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.Asc76

@[expose] def GoldschmidtEscape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G), IsSylowOf 2 T ⊤ → V ≤ T →
    IsElemAbelian 2 V → (∀ g : G, rightConjugate V g ≤ T → rightConjugate V g = V) →
    (∃ v ∈ V, ∃ g : G, g⁻¹ * v * g ∈ T ∧ g⁻¹ * v * g ∉ V) →
    ∃ U : Subgroup G, U ≤ V ∧ ∃ h : G, rightConjugate U h ≤ T ∧ ¬ rightConjugate U h ≤ V ∧
      ∀ w ∈ rightConjugate U h,
        Nat.card (⁅V, zpowers w⁆ : Subgroup G) ≤ V.relIndex (rightConjugate U h)

structure BenderFacts : Prop where
  sylow_inf : ∀ (L : Type) [Group L] [Finite L], IsSzOrU3 L → ∀ P Q : Sylow 2 L, P ≠ Q →
    (P : Subgroup L) ⊓ Q = ⊥
  sylow_transitive : ∀ (L : Type) [Group L] [Finite L], IsSzOrU3 L →
    ∀ P S₀ S : Sylow 2 L, S₀ ≠ P → S ≠ P → ∃ r ∈ (P : Subgroup L), r • S₀ = S
  aut_fix_sylow : ∀ (L : Type) [Group L] [Finite L], IsSzOrU3 L → ∀ (P : Sylow 2 L)
    (φ : MulAut L), (∀ x ∈ (P : Subgroup L), φ x = x) →
    ∃ c ∈ (P : Subgroup L), c ∈ centralizer ((P : Subgroup L) : Set L) ∧ φ = MulAut.conj c
  center_sq : ∀ (L : Type) [Group L] [Finite L], IsSzOrU3 L → ∀ P : Sylow 2 L,
    ∀ c ∈ (P : Subgroup L), c ∈ centralizer ((P : Subgroup L) : Set L) → c ^ 2 = 1
  involution_center : ∀ (L : Type) [Group L] [Finite L], IsSzOrU3 L → ∀ P : Sylow 2 L,
    ∀ x ∈ (P : Subgroup L), x ^ 2 = 1 → x ∈ centralizer ((P : Subgroup L) : Set L)
  aut_involution_center : ∀ (L : Type) [Group L] [Finite L], IsSzOrU3 L → ∀ P : Sylow 2 L,
    ∀ φ : MulAut L, φ * φ = 1 → (∀ x ∈ (P : Subgroup L), φ x ∈ (P : Subgroup L)) →
    ∀ z ∈ (P : Subgroup L), z ∈ centralizer ((P : Subgroup L) : Set L) → φ z = z
  cover : ∀ (Y : Type) [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal], Z ≤ center Y →
    Nat.card Z = 2 → IsSzOrU3 (Y ⧸ Z) → ¬ Z ≤ commutator Y ∨ Nonempty (Y ⧸ Z ≃* Sz 1)

end CFSG.ComponentClassification.Asc76X
