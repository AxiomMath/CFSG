module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3I

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def U4InvolutionCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G) (x : G) (p k m : ℕ), p.Prime → p ≠ 2 →
    1 ≤ k → IsQuasisimple ↥Q →
    Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 p k →
    (Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ k + 1)) →
    x ∈ normalizer (Q : Set G) → x * x = 1 → x ∉ centralizer (Q : Set G) →
    Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 p m →
    m = 2 * k ∧
      ((∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
          ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8) ∨
        ∀ w ∈ GSThmB.layerIn (Q ⊓ centralizer {x}), orderOf w = 2 →
          ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {w} ∧
            X₂ ≤ Q ⊓ centralizer {w} ∧ (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers w ∧
            IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂)

namespace C3

theorem l4u4InvolutionCentralizerFact_of_u4 (hU4 : U4InvolutionCentralizerFact) :
    L4U4InvolutionCentralizerFact := by
  intro G _ _ Q x p k m hp hp2 hk hQ hQm hxN hx2 hxC hLm
  rcases hQm with ⟨hL4, hZ⟩ | ⟨hU, hZ⟩
  · exact l4_case Q x p k m hp hp2 hk hQ hL4 hZ hxN hx2 hxC hLm
  · exact hU4 G Q x p k m hp hp2 hk hQ hU hZ hxN hx2 hxC hLm

end C3

end CFSG.ComponentClassification.HarrisLit
