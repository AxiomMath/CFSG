module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree
open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

structure FusionFacts {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (q : ℕ) : Prop where
  odd_inf : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G)))
  invol_conj : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 →
    ∃ a ∈ A, a * x * a⁻¹ = y
  elem_inner : ∀ E : Subgroup G, E ≤ normalizer (A : Set G) →
    IsElemAbelian 2 E →
    4 * q * Nat.card ↥(E ⊓ centralizer (A : Set G)) < Nat.card E →
      E ≤ A ⊔ centralizer (A : Set G)
  cent_sylow : ∀ V : Subgroup G, IsSylowOf 2 V A →
    normalizer (A : Set G) ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G)
  outer_fuse : ∀ y ∈ normalizer (A : Set G), y * y = 1 →
    y ∉ A ⊔ centralizer (A : Set G) →
    ∀ c ∈ A ⊓ centralizer ({y} : Set G), c * c = 1 →
      ∃ b ∈ A, b * y * b⁻¹ = y * c
  outer_perfect : ∀ y ∈ normalizer (A : Set G), y * y = 1 →
    y ∉ A ⊔ centralizer (A : Set G) →
    ∃ D : Subgroup G, D ≤ A ⊓ centralizer ({y} : Set G) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, orderOf c = 2
  perfect_inv : ∀ D : Subgroup G, D ≤ normalizer (A : Set G) →
    ⁅D, D⁆ = D → ∀ c ∈ D, c * c = 1 → c ∈ A

end CFSG.LocalAnalysis.EvenBN.LinearThree
