module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrbitGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G]

theorem local_entire_involution_set
    (L H U T : Subgroup G) (u : G) (hu : IsInvolution u)
    (huZ : u ∈ Subgroup.center G) (huL : u ∉ L)
    (hUL : U ≤ L) (hUT : U ≤ T) (hTH : T ≤ H) (huT : u ∈ T)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x})
    (hpartition : ∀ x : G, IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    {x : G | x ∈ T ∧ IsInvolution x} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1})) := by
  have hroot (x : G) : x ∈ U ∧ x ≠ 1 ↔ x ∈ L ∧ x ∈ H ∧ IsInvolution x := by
    rw [show x ∈ U ↔ x ∈ ({1} : Set G) ∪
      {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x} from Set.ext_iff.mp hU x]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨rfl | hx, hne⟩
      · exact (hne rfl).elim
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hx.2.2.ne_one⟩
  ext x
  constructor
  · rintro ⟨hxT, hx⟩
    rcases hpartition x hx with rfl | hxL | ⟨l, hlL, hl, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ((hroot x).mpr ⟨hxL, hTH hxT, hx⟩))
    · have hlH : l ∈ H := by
        have hmem := H.mul_mem (H.inv_mem (hTH huT)) (hTH hxT)
        simpa only [inv_mul_cancel_left] using hmem
      exact Or.inr ⟨l, (hroot l).mpr ⟨hlL, hlH, hl⟩, rfl⟩
  · rintro ((hx | hx) | hx)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨huT, hu⟩
    · exact ⟨hUT hx.1, ((hroot x).mp hx).2.2⟩
    · obtain ⟨l, hl, rfl⟩ := hx
      have hlInv := ((hroot l).mp hl).2.2
      have hcomm : Commute u l := by
        rw [commute_iff_eq]
        exact (Subgroup.mem_center_iff.mp huZ l).symm
      refine ⟨T.mul_mem huT (hUT hl.1), ?_, ?_⟩
      · intro hmul
        have heq : u = l := by
          have h := congrArg (fun x : G => x * l) hmul
          simpa only [mul_assoc, ← pow_two, hlInv.sq_eq_one, mul_one, one_mul] using h
        exact huL (heq.symm ▸ hUL hl.1)
      · rw [hcomm.mul_pow 2, hu.sq_eq_one, hlInv.sq_eq_one, one_mul]

theorem central_root_internal_factors
    (U : Subgroup G) (u : G) (hu : IsInvolution u)
    (huZ : u ∈ Subgroup.center G) (huU : u ∉ U) :
    Disjoint (Subgroup.zpowers u) U ∧
      ∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k := by
  have horder : orderOf u = 2 := orderOf_eq_prime_iff.mpr ⟨hu.sq_eq_one, hu.ne_one⟩
  refine ⟨Subgroup.disjoint_def.mpr ?_, ?_⟩
  · intro x hxE hxU
    rcases (mem_zpowers_involution_iff horder).mp hxE with hx | rfl
    · exact hx
    · exact (huU hxU).elim
  · intro e he k _
    have heZ : e ∈ Subgroup.center G := (Subgroup.zpowers_le.mpr huZ) he
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp heZ k).symm

theorem local_omega_one_internal_product
    (U T : Subgroup G) (u : G) (hu : IsInvolution u)
    (huZ : u ∈ Subgroup.center G) (huU : u ∉ U)
    [IsElementaryAbelian 2 U] (hUT : U ≤ T) (huT : u ∈ T)
    (hInv : {x : G | x ∈ T ∧ IsInvolution x} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1}))) :
    (CFSG.omega₁ (G := T) (p := 2)).map T.subtype = Subgroup.zpowers u ⊔ U ∧
      Disjoint (Subgroup.zpowers u) U ∧
      (∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) ∧
      IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) := by
  obtain ⟨hdisj, hcomm⟩ := central_root_internal_factors U u hu huZ huU
  have hrootCentral : U ≤ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hcomm e he k hk).eq
  let : IsElementaryAbelian 2 (Subgroup.zpowers u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hu.sq_eq_one
  have helem := IsElementaryAbelian.sup_of_le_centralizer (p := 2) hrootCentral
  refine ⟨?_, hdisj, hcomm, helem⟩
  rw [omega_one_map_eq_entire_involution_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rw [hInv] at hx
    rcases hx with (hx | hx) | hx
    · have hxu := Set.mem_singleton_iff.mp hx
      subst x
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    · exact Subgroup.mem_sup_right hx.1
    · obtain ⟨l, hl, rfl⟩ := hx
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers u) hl.1
  · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨huT, hu⟩)) ?_
    intro k hk
    by_cases hkone : k = 1
    · exact hkone ▸ Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hUT hk, hkone,
        elemPow_eq_one_of_isElementaryAbelian k hk⟩

theorem local_omega_one_product_equivalence
    (U T : Subgroup G) (u : G)
    (hOmega : (CFSG.omega₁ (G := T) (p := 2)).map T.subtype = Subgroup.zpowers u ⊔ U)
    (hdisj : Disjoint (Subgroup.zpowers u) U)
    (hcomm : ∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) :
    ∃ e : Subgroup.zpowers u × U ≃*
      ↥((CFSG.omega₁ (G := T) (p := 2)).map T.subtype),
      ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b := by
  refine ⟨(commutingJoinEquiv _ _ hdisj hcomm).trans
    (MulEquiv.subgroupCongr hOmega.symm), ?_⟩
  intro a b
  exact commutingJoinEquiv_apply _ _ hdisj hcomm a b

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
