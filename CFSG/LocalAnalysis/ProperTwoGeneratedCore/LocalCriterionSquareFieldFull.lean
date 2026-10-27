module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldElementary

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups IsMulCommutative

variable {F : Type u} [Field F] [Finite F]

theorem original_outer_involution_field_conjugacy_and_centralizer {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (a : Gamma F) (ha : orderOf a = 2) (houter : a ∉ linearKernel F) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧
      (∀ c : F, a.right c = c ^ (2 ^ s)) ∧
      Nat.card (fixedField a.right) = 2 ^ s ∧
      ∃ x : SL(2, F),
        a = (SemidirectProduct.inl x : Gamma F) * SemidirectProduct.inr a.right *
          (SemidirectProduct.inl x)⁻¹ ∧
        centralizerS a = (fixedSL2 a.right).map (MulAut.conj x).toMonoidHom := by
  let : CharP F 2 := char_two_of_card hcard
  obtain ⟨hane, hapow, _hacocycle⟩ := outer_involution_cocycle a ha houter
  obtain ⟨s, hs, hns, hfrob, hfixed⟩ := finite_field_involution_exact hn hcard
    a.right hapow hane
  exact ⟨s, hs, hns, hfrob, hfixed,
    outer_involution_conjugator_and_centralizer a ha houter⟩

theorem original_outer_elementary_field_conjugacy_and_rank {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (a : Gamma F) (ha : a ∈ A) (houter : a ∉ linearKernel F) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧
      (∀ c : F, a.right c = c ^ (2 ^ s)) ∧
      Nat.card (fixedField a.right) = 2 ^ s ∧
      (∃ x : SL(2, F),
        a = (SemidirectProduct.inl x : Gamma F) * SemidirectProduct.inr a.right *
          (SemidirectProduct.inl x)⁻¹ ∧
        centralizerS a = (fixedSL2 a.right).map (MulAut.conj x).toMonoidHom) ∧
      Nat.card (A ⧸ linearIntersection A) = 2 ∧
      Nat.card A = 2 * Nat.card (linearIntersection A) ∧
      Nat.card (linearIntersection A) ≤ 2 ^ s ∧
      Nat.card A ≤ 2 ^ (s + 1) ∧
      Module.finrank (ZMod 2) (Additive (linearIntersection A)) ≤ s ∧
      Module.finrank (ZMod 2) (Additive (intersectionS A)) ≤ s ∧
      Module.finrank (ZMod 2) (Additive A) ≤ s + 1 := by
  let : CharP F 2 := char_two_of_card hcard
  obtain ⟨s, hs, hns, hfrob, hfixed, hquotient, hfactor, hI, hA, hrI, hrS, hrA⟩ :=
    original_outer_elementary_card_and_rank hn hcard A a ha houter
  exact ⟨s, hs, hns, hfrob, hfixed,
    outer_involution_conjugator_and_centralizer a (elementary_outer_order A a ha houter)
      houter, hquotient, hfactor, hI, hA, hrI, hrS, hrA⟩

theorem original_even_SL2_outer_involution_field_conjugacy_and_rank {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) :
    (∀ a : Gamma F, orderOf a = 2 → a ∉ linearKernel F →
      ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧
        (∀ c : F, a.right c = c ^ (2 ^ s)) ∧
        Nat.card (fixedField a.right) = 2 ^ s ∧
        ∃ x : SL(2, F),
          a = (SemidirectProduct.inl x : Gamma F) * SemidirectProduct.inr a.right *
            (SemidirectProduct.inl x)⁻¹ ∧
          centralizerS a = (fixedSL2 a.right).map (MulAut.conj x).toMonoidHom) ∧
    (∀ (A : Subgroup (Gamma F)) (_ : CFSG.IsElementaryAbelian 2 A),
      ¬A ≤ linearKernel F →
      Nat.card (A ⧸ linearIntersection A) = 2 ∧
      ∀ a : Gamma F, a ∈ A → a ∉ linearKernel F →
        ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧
          (∀ c : F, a.right c = c ^ (2 ^ s)) ∧
          Nat.card (fixedField a.right) = 2 ^ s ∧
          (∃ x : SL(2, F),
            a = (SemidirectProduct.inl x : Gamma F) * SemidirectProduct.inr a.right *
              (SemidirectProduct.inl x)⁻¹ ∧
            centralizerS a = (fixedSL2 a.right).map (MulAut.conj x).toMonoidHom) ∧
          Nat.card (A ⧸ linearIntersection A) = 2 ∧
          Nat.card A = 2 * Nat.card (linearIntersection A) ∧
          Nat.card (linearIntersection A) ≤ 2 ^ s ∧
          Nat.card A ≤ 2 ^ (s + 1) ∧
          Module.finrank (ZMod 2) (Additive (linearIntersection A)) ≤ s ∧
          Module.finrank (ZMod 2) (Additive (intersectionS A)) ≤ s ∧
          Module.finrank (ZMod 2) (Additive A) ≤ s + 1) := by
  refine ⟨?_, ?_⟩
  · intro a ha houter
    exact original_outer_involution_field_conjugacy_and_centralizer hn hcard a ha houter
  · intro A hA houter
    let : CFSG.IsElementaryAbelian 2 A := hA
    exact ⟨original_elementary_quotient_card hcard A houter,
      fun a ha haouter => original_outer_elementary_field_conjugacy_and_rank
        hn hcard A a ha haouter⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
