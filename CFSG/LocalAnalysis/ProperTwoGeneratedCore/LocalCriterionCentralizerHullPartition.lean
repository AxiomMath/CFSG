module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullInnerLift

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

universe u

variable {G : Type u} [Group G]

theorem square_one_inner_representative_difference
    (L : Subgroup G) [L.Normal] (x : G) (hx : x ^ 2 = 1)
    (l : L) (hl : l ^ 2 = 1) (haction : MulAut.conjNormal x = MulAut.conj l) :
    x * (l : G) ∈ Subgroup.centralizer (L : Set G) ∧ (x * (l : G)) ^ 2 = 1 := by
  have hlG : (l : G) ^ 2 = 1 := congrArg Subtype.val hl
  have hfix := congrArg (fun a : MulAut L => (a l : G)) haction
  have hconj : x * (l : G) * x⁻¹ = l := by
    simpa only [MulAut.conjNormal_apply, MulAut.conj_apply,
      mul_assoc, mul_inv_cancel, mul_one] using hfix
  have hcomm : Commute x (l : G) := by
    rw [commute_iff_eq]
    have heq := congrArg (fun a : G => a * x) hconj
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq
  refine ⟨?_, by rw [hcomm.mul_pow 2, hx, hlG, one_mul]⟩
  have hkernel : x * (l : G) ∈ (MulAut.conjNormal (H := L)).ker := by
    change MulAut.conjNormal (x * (l : G)) = 1
    rw [map_mul, MulAut.conjNormal_val, haction, ← pow_two, ← map_pow, hl, map_one]
  exact normal_conjugation_ker L ▸ hkernel

theorem involution_eq_or_hull_translate
    (L : Subgroup G) [L.Normal] (u : G)
    (hunique : ∀ k : G, k ∈ Subgroup.centralizer (L : Set G) → IsInvolution k → k = u)
    (x : G) (hx : IsInvolution x)
    (hrepresentative : ∃ l : L, l ^ 2 = 1 ∧ MulAut.conjNormal x = MulAut.conj l) :
    x = u ∨ ∃ l : L, IsInvolution l ∧ (x = (l : G) ∨ x = u * (l : G)) := by
  obtain ⟨l, hl, haction⟩ := hrepresentative
  obtain ⟨hcentral, hsquare⟩ := square_one_inner_representative_difference L x hx.sq_eq_one
    l hl haction
  by_cases hlone : l = 1
  · have hxcentral : x ∈ Subgroup.centralizer (L : Set G) := by
      simpa only [hlone, Subgroup.coe_one, mul_one] using hcentral
    exact Or.inl (hunique x hxcentral hx)
  · right
    refine ⟨l, ⟨hlone, hl⟩, ?_⟩
    have hlG : (l : G) ^ 2 = 1 := congrArg Subtype.val hl
    have hll : (l : G) * l = 1 := by simpa only [pow_two] using hlG
    have hxl : (x * (l : G)) * l = x := by rw [mul_assoc, hll, mul_one]
    by_cases hone : x * (l : G) = 1
    · left
      have heq := congrArg (fun a : G => a * l) hone
      simpa only [hxl, one_mul] using heq
    · right
      have heq := congrArg (fun a : G => a * l)
        (hunique (x * (l : G)) hcentral ⟨hone, hsquare⟩)
      simpa only [hxl] using heq

theorem hull_involution_three_sets_disjoint (L : Subgroup G) (u : G) (huL : u ∉ L) :
    Disjoint ({u} : Set G) {x : G | x ∈ L ∧ IsInvolution x} ∧
      Disjoint ({u} : Set G)
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint {x : G | x ∈ L ∧ IsInvolution x}
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro x hx hxL
    exact huL (Set.mem_singleton_iff.mp hx ▸ hxL.1)
  · intro x hx htranslate
    have hxu := Set.mem_singleton_iff.mp hx
    subst x
    obtain ⟨l, hl, hmul⟩ := htranslate
    apply hl.2.ne_one
    have heq : u * l = u * 1 := by simpa only [mul_one] using hmul
    exact mul_left_cancel heq
  · intro x hx
    rintro ⟨l, hl, rfl⟩
    have humem := L.mul_mem hx.1 (L.inv_mem hl.1)
    apply huL
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using humem

theorem entire_involution_partition_of_inner_quotient_actions [Finite G]
    (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (hodd : Odd (Nat.card N)) (hcentral : N ≤ Subgroup.center L)
    (hgen : Subgroup.closure {x : L | IsInvolution x} = ⊤)
    (hcenter : Odd (Nat.card (Subgroup.center L))) (u : G)
    (hu : IsInvolution u) (huZ : u ∈ Subgroup.center G) (huL : u ∉ L)
    (hunique : ∀ k : G, k ∈ Subgroup.centralizer (L : Set G) → IsInvolution k → k = u)
    (hinner : ∀ x : G, IsInvolution x →
      normalQuotientConjugation L N x ∈ innerAutomorphismSubgroup (L ⧸ N)) :
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
    have hlift := normal_quotient_inner_square_one_lift L N hodd hcentral hgen hcenter
      x hx.sq_eq_one (hinner x hx)
    rcases involution_eq_or_hull_translate L u hunique x hx hlift with hxu | ⟨l, hl, hxl⟩
    · exact Or.inl (Or.inl (Set.mem_singleton_iff.mpr hxu))
    · have hlG : IsInvolution (l : G) :=
        ⟨fun h => hl.ne_one (Subtype.ext h), congrArg Subtype.val hl.sq_eq_one⟩
      rcases hxl with rfl | rfl
      · exact Or.inl (Or.inr ⟨l.property, hlG⟩)
      · exact Or.inr ⟨l, ⟨l.property, hlG⟩, rfl⟩
  · rintro ((hx | hx) | hx)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact hu
    · exact hx.2
    · obtain ⟨l, hl, rfl⟩ := hx
      have hcomm : Commute u l := by
        rw [commute_iff_eq]
        exact (Subgroup.mem_center_iff.mp huZ l).symm
      refine ⟨?_, by rw [hcomm.mul_pow 2, hu.sq_eq_one, hl.2.sq_eq_one, one_mul]⟩
      intro hmul
      have heq := congrArg (fun a : G => a * l) hmul
      have hll : l * l = 1 := by simpa only [pow_two] using hl.2.sq_eq_one
      have hul : u = l := by simpa only [mul_assoc, hll, mul_one, one_mul] using heq
      exact huL (hul.symm ▸ hl.1)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
