module

public import CFSG.ClassicalInvolution.Generic.LineModelLinear
public import CFSG.ClassicalInvolution.Generic.LineModelUnitary

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ClassicalInvolution.Generic

section RankCount

variable {G : Type*} [Group G]

theorem exists_ne_one_mem_inf_of_relIndex_two {A C₁ C₂ : Subgroup G} (h₁ : C₁ ≤ A)
    (hr₁ : C₁.relIndex A = 2) (hr₂ : C₂.relIndex A = 2) (h8 : 8 ≤ Nat.card A) :
    ∃ x ∈ C₁ ⊓ C₂, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : C₁ ⊓ C₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
  have hle : (C₁ ⊓ C₂).relIndex A ≤ 4 := by
    have := Subgroup.relIndex_inf_le (H := C₁) (K := C₂) (L := A)
    rw [hr₁, hr₂] at this
    omega
  have hmul : (C₁ ⊓ C₂).relIndex A = Nat.card A := by
    have h1 := ((C₁ ⊓ C₂).subgroupOf A).card_mul_index
    have h3 : Nat.card ((C₁ ⊓ C₂).subgroupOf A) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h₁)).toEquiv, hbot,
        Subgroup.card_bot]
    rw [h3, one_mul] at h1
    exact h1
  omega

end RankCount

section RankFrame

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable (F) in
structure RankFrame (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) : Prop where
  odd : Odd (Nat.card F)
  five : 5 ≤ Nat.card F
  inv : ConjInvariant Ω
  elem : ∀ x ∈ A, x * x = 1
  eq_sigma : S = sigmaSet F Ω A
  two_le : ∃ K ∈ S, ∃ L ∈ S, K ≠ L
  card : 8 ≤ Nat.card A

theorem ToralFrame.toRankFrame {Ω : Set (Subgroup G)} {A : Subgroup G} {S : Set (Subgroup G)}
    (Fr : ToralFrame F Ω A S) : RankFrame F Ω A S where
  odd := Fr.odd
  five := Fr.five
  inv := Fr.inv
  elem := Fr.elem
  eq_sigma := Fr.eq_sigma
  two_le := Fr.exists_ne
  card := Fr.card

namespace RankFrame

variable {Ω : Set (Subgroup G)} {A : Subgroup G} {S : Set (Subgroup G)}
  (Fr : RankFrame F Ω A S)

include Fr

theorem finite : Finite F := by
  by_contra h
  rw [not_finite_iff_infinite] at h
  have := Fr.odd
  rw [Nat.card_eq_zero_of_infinite] at this
  exact absurd this (by decide)

theorem subset : S ⊆ Ω := by
  rw [Fr.eq_sigma]
  exact fun _ h => h.1

theorem mem_iff {K : Subgroup G} : K ∈ S ↔ K ∈ Ω ∧ InSigma F A K := by
  rw [Fr.eq_sigma]
  exact Iff.rfl

theorem inSigma {K : Subgroup G} (hK : K ∈ S) : InSigma F A K :=
  (Fr.mem_iff.mp hK).2

theorem conj_mem {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) {K : Subgroup G}
    (hK : K ∈ S) : conjSub n K ∈ S :=
  Fr.mem_iff.mpr ⟨Fr.inv n K (Fr.subset hK), (Fr.inSigma hK).conj hn⟩

theorem mem_of_isUniqueInvolution {K : Subgroup G} (hK : K ∈ S) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ A := by
  have := Fr.finite
  exact (Fr.inSigma hK).unique_involution_mem Fr.odd hz

theorem relIndex_axisSub {K : Subgroup G} (hK : K ∈ S) : (axisSub A K).relIndex A = 2 := by
  obtain ⟨φ, rfl, hD⟩ := Fr.inSigma hK
  exact hD.index_two

theorem exists_ne_one_mem_axisSub_inf_axisSub {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) :
    ∃ x ∈ axisSub A K ⊓ axisSub A L, x ≠ 1 :=
  exists_ne_one_mem_inf_of_relIndex_two inf_le_left (Fr.relIndex_axisSub hK)
    (Fr.relIndex_axisSub hL) Fr.card

end RankFrame

@[expose] def RankLocalA2 (A : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ∀ x ∈ axisSub A K ⊓ axisSub A L, x ≠ 1 →
    Commutes K L ∨ IsLine A K L

theorem a2Dichotomy_of_rankFrame {Ω : Set (Subgroup G)} {A : Subgroup G}
    {S : Set (Subgroup G)} (Fr : RankFrame F Ω A S) (h : RankLocalA2 A S) : A2Dichotomy A S :=
  fun K hK L hL hKL => by
    obtain ⟨x, hx, hx1⟩ := Fr.exists_ne_one_mem_axisSub_inf_axisSub hK hL
    exact h K hK L hL hKL x hx hx1

end RankFrame

section Models

variable {F : Type} [Field F] {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

theorem a2Dichotomy_of_rankFrame_linear (Fr : RankFrame F Ω A S)
    (h : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearA2Pair F A K L ∨ LinearA2Pair F A L K) : A2Dichotomy A S := by
  have := Fr.finite
  intro K hK L hL hKL
  rcases h K hK L hL hKL with hc | hp | hp
  · exact Or.inl hc
  · exact Or.inr (hp.isLine (Fr.inSigma hK) (Fr.inSigma hL) Fr.odd Fr.five).1
  · exact Or.inr (hp.isLine (Fr.inSigma hL) (Fr.inSigma hK) Fr.odd Fr.five).2

theorem a2Dichotomy_of_rankFrame_unitary {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ}
    [Fact p.Prime] [CharP K₀ p] (Fr : RankFrame F Ω A S) (hK : Nat.card K₀ = (p ^ f) ^ 2)
    (h : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      Commutes P Q ∨ UnitaryA2Pair K₀ p f A P Q ∨ UnitaryA2Pair K₀ p f A Q P) :
    A2Dichotomy A S := by
  have := Fr.finite
  intro P hP Q hQ hPQ
  rcases h P hP Q hQ hPQ with hc | hp | hp
  · exact Or.inl hc
  · exact Or.inr (hp.isLine hK (Fr.inSigma hP) (Fr.inSigma hQ) Fr.odd Fr.five).1
  · exact Or.inr (hp.isLine hK (Fr.inSigma hQ) (Fr.inSigma hP) Fr.odd Fr.five).2

end Models

end CFSG.ClassicalInvolution
