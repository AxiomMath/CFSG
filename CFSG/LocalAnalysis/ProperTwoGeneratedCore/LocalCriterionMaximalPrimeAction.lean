module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeOddHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoLocalHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {K Ω : Type*} [Group K] [Finite K] [MulAction K Ω] [Finite Ω]

theorem odd_central_involution_class_pair_flips_card_le_two
    (J : Subgroup K) [J.Normal] (hJodd : Odd (Nat.card J))
    (s : K) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (K ⧸ J))
    (hno : ∀ r ∈ involutionPointClass s, ∀ a : Ω, r • a ≠ a)
    (hflip : ∀ a b : Ω, a ≠ b → ∃ r ∈ involutionPointClass s, r • a = b) :
    Nat.card Ω ≤ 2 := by
  classical
  by_cases hempty : IsEmpty Ω
  · let := hempty
    simp
  have : Nonempty Ω := not_isEmpty_iff.mp hempty
  let L := involutionPointHull s
  let W := L ⊓ J
  obtain ⟨_, _, hWodd, hcases⟩ :=
    pointClass_hull_odd_intersection_decomposition J hJodd s hs hcentral
  have hLno : ∀ r ∈ L, orderOf r = 2 → ∀ a : Ω, r • a ≠ a := by
    intro r hr hrorder a
    obtain ⟨w, hw⟩ := pointClass_hull_involution_odd_conjugate J hJodd s hs hcentral hr hrorder
    exact hno r ⟨(w : K), hw⟩ a
  have hstabilizer (a : Ω) :
      (MulAction.stabilizer L a).map L.subtype ≤ W := by
    let C := MulAction.stabilizer L a
    have hCodd : Odd (Nat.card C) := by
      apply CFSG.ProperTwoGeneratedCore.odd_card_of_no_order_two
      intro c hc hcorder
      exact hLno (c : K) c.property ((Subgroup.orderOf_coe c).trans hcorder) a
        (MulAction.mem_stabilizer_iff.mp hc)
    have hAodd : Odd (Nat.card (C.map L.subtype)) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hCodd
    exact odd_subgroup_le_pointClass_hull_odd_intersection J hJodd s hs hcentral
      (C.map L.subtype) (Subgroup.map_subtype_le C) hAodd
  have hWfix : ∀ x ∈ W, ∀ a : Ω, x • a = a := by
    intro x hx a
    by_contra hnot
    obtain ⟨r, hr, hra⟩ := hflip a (x • a) (Ne.symm hnot)
    have hrL : r ∈ L := Subgroup.subset_closure hr
    let c : L := ⟨x⁻¹ * r, L.mul_mem (L.inv_mem hx.1) hrL⟩
    have hc : c ∈ MulAction.stabilizer L a := by
      apply MulAction.mem_stabilizer_iff.mpr
      change (x⁻¹ * r) • a = a
      rw [mul_smul, hra, inv_smul_smul]
    have hcW : x⁻¹ * r ∈ W :=
      hstabilizer a (Subgroup.mem_map_of_mem L.subtype hc)
    have hrW : r ∈ W := by
      have hm := W.mul_mem hx hcW
      simpa only [mul_inv_cancel_left] using hm
    exact hWodd.ne_two_of_dvd_nat (W.orderOf_dvd_natCard hrW)
      (order_two_of_mem_pointClass hs hr)
  let a : Ω := Classical.choice inferInstance
  have hcover : ∀ b : Ω, b = a ∨ b = s • a := by
    intro b
    by_cases hba : b = a
    · exact Or.inl hba
    obtain ⟨r, hr, hrb⟩ := hflip a b (Ne.symm hba)
    have hrL : r ∈ L := Subgroup.subset_closure hr
    rcases hcases r hrL with hrsW | hrW
    · right
      have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
      have heq := hWfix (r * s) hrsW (s • a)
      rw [← mul_smul, mul_assoc, hss, mul_one, hrb] at heq
      exact heq
    · left
      exact hrb.symm.trans (hWfix r hrW a)
  have hsub : (Set.univ : Set Ω) ⊆ {a, s • a} := by
    intro b _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcover b
  have hn := Set.ncard_le_ncard hsub
  have hpair : ({a, s • a} : Set Ω).ncard ≤ 2 := by
    have ha : a ∉ ({s • a} : Set Ω) := by
      intro heq
      exact hno s (distinguished_mem_pointClass s) a (Set.mem_singleton_iff.mp heq).symm
    rw [Set.ncard_insert_of_notMem ha, Set.ncard_singleton]
  simpa only [Set.ncard_univ] using hn.trans hpair

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
