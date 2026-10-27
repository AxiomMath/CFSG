module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup

variable {G : Type*} [Group G]

@[expose] def IsClassicalInvolutionWitness (t : G) (R : Subgroup G) : Prop :=
  R ≤ centralizer ({t} : Set G) ∧ (R.subgroupOf (centralizer ({t} : Set G))).IsSubnormal ∧
    (∀ P : Sylow 2 R, ¬ IsMulCommutative (P : Subgroup R)) ∧
    (t ∈ R ∧ ∀ x ∈ R, orderOf x = 2 → x = t) ∧
    (∀ r ∈ R, (∃ n : ℕ, orderOf r = 2 ^ n) → ∀ g : G,
      g⁻¹ * r * g ∈ centralizer ({t} : Set G) → g⁻¹ * r * g ∈ normalizer (R : Set G)) ∧
    ∀ g ∈ centralizer ({t} : Set G), g ∉ normalizer (R : Set G) →
      ⁅conjugate R g, R⁆ ≤
        (oddCore (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype

@[expose] def ClassicalInvolution (t : G) : Prop :=
  orderOf t = 2 ∧ ∃ R : Subgroup G, IsClassicalInvolutionWitness t R

theorem normal_unique_involution_classical {t : G} (ht : orderOf t = 2) {R : Subgroup G}
    (hRC : R ≤ centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (centralizer ({t} : Set G))).Normal) (htR : t ∈ R)
    (huniq : ∀ x ∈ R, orderOf x = 2 → x = t)
    (hsyl : ∀ P : Sylow 2 R, ¬ IsMulCommutative (P : Subgroup R)) :
    IsClassicalInvolutionWitness t R ∧ ClassicalInvolution t := by
  have hCN : centralizer ({t} : Set G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hwit : IsClassicalInvolutionWitness t R :=
    ⟨hRC, hRn.isSubnormal, hsyl, ⟨htR, huniq⟩, fun _ _ _ _ hg => hCN hg,
      fun _ hg hgN => absurd (hCN hg) hgN⟩
  exact ⟨hwit, ht, R, hwit⟩

end CFSG.ComponentClassification.SmallLocal
