module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullPartition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

universe u v

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

theorem central_involution_translate_isInvolution
    (u x : G) (hu : IsInvolution u) (hx : IsInvolution x)
    (huZ : u ∈ Subgroup.center G) (hxu : x ≠ u) : IsInvolution (u * x) := by
  have hcomm : Commute u x := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp huZ x).symm
  refine ⟨?_, by rw [hcomm.mul_pow 2, hu.sq_eq_one, hx.sq_eq_one, one_mul]⟩
  intro hmul
  apply hxu
  have heq := congrArg (fun y : G => u * y) hmul
  simpa only [← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul, mul_one] using heq

theorem normal_quotient_central_involution_action
    (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (u : G) (huZ : u ∈ Subgroup.center G) : normalQuotientConjugation L N u = 1 := by
  have huK : u ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l _
    exact Subgroup.mem_center_iff.mp huZ l
  have hker : u ∈ (MulAut.conjNormal (H := L)).ker := by
    rw [normal_conjugation_ker]
    exact huK
  have hconj : MulAut.conjNormal (H := L) u = 1 := hker
  change CFSG.FiveTransitive.CharacteristicAutomorphism.quotient N
    (MulAut.conjNormal u) = 1
  rw [hconj, map_one]

theorem normal_quotient_inner_of_two_hull_cosets
    (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (u x : G) (huZ : u ∈ Subgroup.center G)
    (hexhaust : x = u ∨ x ∈ L ∨ u * x ∈ L) :
    normalQuotientConjugation L N x ∈ innerAutomorphismSubgroup (L ⧸ N) := by
  have huaction := normal_quotient_central_involution_action L N u huZ
  have hinner (l : L) : normalQuotientConjugation L N (l : G) =
      MulAut.conj (QuotientGroup.mk' N l) := by
    change CFSG.FiveTransitive.CharacteristicAutomorphism.quotient N
      (MulAut.conjNormal (l : G)) = _
    rw [MulAut.conjNormal_val, characteristic_quotient_conj]
  rcases hexhaust with hxu | hxL | huxL
  · rw [hxu, huaction]
    exact Subgroup.one_mem _
  · exact ⟨QuotientGroup.mk' N ⟨x, hxL⟩, (hinner ⟨x, hxL⟩).symm⟩
  · refine ⟨QuotientGroup.mk' N ⟨u * x, huxL⟩, ?_⟩
    have h := hinner ⟨u * x, huxL⟩
    rw [map_mul, huaction, one_mul] at h
    exact h.symm

theorem every_involution_inner_of_pair [Finite G]
    (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (hdouble : MulAction.IsMultiplyPretransitive L X 2)
    (a b : X) (hab : a ≠ b)
    (hrank : twoRank ↥((MulAction.stabilizer G a) ⊓ (MulAction.stabilizer G b)) ≤ 1)
    (u : G) (hu : IsInvolution u) (huZ : u ∈ Subgroup.center G)
    (huL : u ∉ L) (hua : u • a = a) (hub : u • b = b)
    (z : G) (hzL : z ∈ L) (hz : IsInvolution z) (hza : z • a = a) :
    ∀ x : G, IsInvolution x →
      normalQuotientConjugation L N x ∈ innerAutomorphismSubgroup (L ⧸ N) := by
  intro x hx
  exact normal_quotient_inner_of_two_hull_cosets L N u x huZ
    (entire_involution_two_hull_cosets L hdouble a b hab hrank u hu huZ huL
      hua hub z hzL hz hza x hx)

theorem entire_disjoint_involution_partition_of_pair [Finite G]
    (L : Subgroup G) [L.Normal]
    (hdouble : MulAction.IsMultiplyPretransitive L X 2)
    (a b : X) (hab : a ≠ b)
    (hrank : twoRank ↥((MulAction.stabilizer G a) ⊓ (MulAction.stabilizer G b)) ≤ 1)
    (u : G) (hu : IsInvolution u) (huZ : u ∈ Subgroup.center G)
    (huL : u ∉ L) (hua : u • a = a) (hub : u • b = b)
    (z : G) (hzL : z ∈ L) (hz : IsInvolution z) (hza : z • a = a) :
    {x : G | IsInvolution x} = ({u} : Set G) ∪ {x : G | x ∈ L ∧ IsInvolution x} ∪
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint ({u} : Set G) {x : G | x ∈ L ∧ IsInvolution x} ∧
      Disjoint ({u} : Set G)
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint {x : G | x ∈ L ∧ IsInvolution x}
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) := by
  refine ⟨?_, hull_involution_three_sets_disjoint L u huL⟩
  ext x
  constructor
  · intro hx
    rcases entire_involution_two_hull_cosets L hdouble a b hab hrank u hu huZ huL
        hua hub z hzL hz hza x hx with hxu | hxL | huxL
    · exact Or.inl (Or.inl hxu)
    · exact Or.inl (Or.inr ⟨hxL, hx⟩)
    · by_cases hxu : x = u
      · exact Or.inl (Or.inl hxu)
      · refine Or.inr ⟨u * x, ⟨huxL, ?_⟩, ?_⟩
        · exact central_involution_translate_isInvolution u x hu hx huZ hxu
        · change u * (u * x) = x
          rw [← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul]
  · rintro ((hx | hx) | hx)
    · have hxu := Set.mem_singleton_iff.mp hx
      exact hxu.symm ▸ hu
    · exact hx.2
    · obtain ⟨l, hl, rfl⟩ := hx
      exact central_involution_translate_isInvolution u l hu hl.2 huZ
        (fun h => huL (h ▸ hl.1))

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
