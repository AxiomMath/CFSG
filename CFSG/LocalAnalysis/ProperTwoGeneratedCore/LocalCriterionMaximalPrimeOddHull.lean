module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem mem_involution_zpowers_iff {s x : G} (hs : orderOf s = 2) :
    x ∈ Subgroup.zpowers s ↔ x = 1 ∨ x = s := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hs]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, pow_zero _⟩
    · exact ⟨1, by omega, pow_one _⟩

omit [Finite G] in
theorem pointClass_hull_normal (s : G) : (involutionPointHull s).Normal := by
  constructor
  intro x hx g
  change g * x * g⁻¹ ∈ Subgroup.closure (involutionPointClass s)
  apply Subgroup.closure_induction (p := fun x _ =>
    g * x * g⁻¹ ∈ Subgroup.closure (involutionPointClass s)) ?_ ?_ ?_ ?_ hx
  · intro a ha
    apply Subgroup.subset_closure
    simpa only [inv_inv, rightConjugateElem] using pointClass_right_conjugate_mem ha g⁻¹
  · simpa only [mul_one, mul_inv_cancel] using
      (Subgroup.closure (involutionPointClass s)).one_mem
  · intro a b _ _ ha hb
    simpa only [mul_assoc, inv_mul_cancel_left] using
      (Subgroup.closure (involutionPointClass s)).mul_mem ha hb
  · intro a _ ha
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      (Subgroup.closure (involutionPointClass s)).inv_mem ha

omit [Finite G] in
theorem pointClass_hull_le_odd_involution_sup
    (J : Subgroup G) [J.Normal] (s : G) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (G ⧸ J)) :
    involutionPointHull s ≤ J ⊔ Subgroup.zpowers s := by
  let q := QuotientGroup.mk' J
  apply (Subgroup.closure_le (J ⊔ Subgroup.zpowers s)).mpr
  rintro x ⟨g, rfl⟩
  have hqconj : q (rightConjugateElem s g) = q s := by
    have hc := Subgroup.mem_center_iff.mp hcentral (q g)
    change q (g⁻¹ * s * g) = q s
    rw [map_mul, map_mul, map_inv, mul_assoc, ← hc, inv_mul_cancel_left]
  have hxJ : rightConjugateElem s g * s ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (rightConjugateElem s g * s) = 1
    rw [map_mul, hqconj, ← map_mul]
    have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
    rw [hss, map_one]
  have hm := (J ⊔ Subgroup.zpowers s).mul_mem
    (Subgroup.mem_sup_left hxJ) (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
  change rightConjugateElem s g ∈ J ⊔ Subgroup.zpowers s
  simpa only [mul_assoc, hss, mul_one] using hm

theorem pointClass_hull_odd_intersection_decomposition
    (J : Subgroup G) [J.Normal] (hJodd : Odd (Nat.card J))
    (s : G) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (G ⧸ J)) :
    let L := involutionPointHull s
    let W := L ⊓ J
    L = W ⊔ Subgroup.zpowers s ∧ W.relIndex L = 2 ∧
      Odd (Nat.card W) ∧
      ∀ l ∈ L, l * s ∈ W ∨ l ∈ W := by
  let L := involutionPointHull s
  let W := L ⊓ J
  have hsL : s ∈ L := Subgroup.subset_closure (distinguished_mem_pointClass s)
  have hsJ : s ∉ J := by
    intro hmem
    exact hJodd.ne_two_of_dvd_nat (J.orderOf_dvd_natCard hmem) hs
  have hcases : ∀ l ∈ L, l * s ∈ W ∨ l ∈ W := by
    intro l hl
    have hlSup := pointClass_hull_le_odd_involution_sup J s hs hcentral hl
    obtain ⟨j, hj, t, ht, hjt⟩ := Subgroup.mem_sup_of_normal_left.mp hlSup
    rcases (mem_involution_zpowers_iff hs).mp ht with ht1 | hts
    · right
      refine ⟨hl, ?_⟩
      rw [← hjt, ht1, mul_one]
      exact hj
    · left
      refine ⟨L.mul_mem hl hsL, ?_⟩
      have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
      rw [← hjt, hts, mul_assoc, hss, mul_one]
      exact hj
  have hrel : W.relIndex L = 2 :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
      ⟨s, hsL, fun hm => hsJ hm.2, hcases⟩
  have hdecomp : L = W ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · intro l hl
      rcases hcases l hl with hls | hlW
      · have hm := (W ⊔ Subgroup.zpowers s).mul_mem
          (Subgroup.mem_sup_left hls) (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
        have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
        simpa only [mul_assoc, hss, mul_one] using hm
      · exact Subgroup.mem_sup_left hlW
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hsL)
  exact ⟨hdecomp, hrel, hJodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right), hcases⟩

theorem pointClass_hull_involution_odd_conjugate
    (J : Subgroup G) [J.Normal] (hJodd : Odd (Nat.card J))
    (s : G) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (G ⧸ J))
    {x : G} (hxL : x ∈ involutionPointHull s) (hx : orderOf x = 2) :
    x ∈ conjugacyWithin (involutionPointHull s ⊓ J) s := by
  obtain ⟨_, _, hWodd, hcases⟩ :=
    pointClass_hull_odd_intersection_decomposition J hJodd s hs hcentral
  rcases hcases x hxL with hxs | hxW
  · have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
    have hxx : x * x = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hx).1
    have hinv : s⁻¹ * (x * s) * s = (x * s)⁻¹ := by
      have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      simp only [hsi, hxi, mul_inv_rev, mul_assoc, hss, mul_one]
    have hc := inverted_odd_element_mul_involution_conjugate
      (involutionPointHull s ⊓ J) hWodd hss hxs hinv
    simpa only [mul_assoc, hss, mul_one] using hc
  · exact False.elim (hWodd.ne_two_of_dvd_nat
      ((involutionPointHull s ⊓ J).orderOf_dvd_natCard hxW) hx)

theorem odd_subgroup_le_pointClass_hull_odd_intersection
    (J : Subgroup G) [J.Normal] (hJodd : Odd (Nat.card J))
    (s : G) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (G ⧸ J))
    (A : Subgroup G) (hAL : A ≤ involutionPointHull s) (hAodd : Odd (Nat.card A)) :
    A ≤ involutionPointHull s ⊓ J := by
  let q := QuotientGroup.mk' J
  have hqs : orderOf (q s) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, (orderOf_eq_prime_iff.mp hs).1, map_one]
    · intro heq
      have hsJ : s ∈ J := (QuotientGroup.eq_one_iff _).mp heq
      exact hJodd.ne_two_of_dvd_nat (J.orderOf_dvd_natCard hsJ) hs
  intro a ha
  refine ⟨hAL ha, ?_⟩
  have hqa : q a ∈ Subgroup.zpowers (q s) := by
    have hsup := pointClass_hull_le_odd_involution_sup J s hs hcentral (hAL ha)
    obtain ⟨j, hj, t, ht, hjt⟩ := Subgroup.mem_sup_of_normal_left.mp hsup
    rw [← hjt, map_mul, show q j = 1 from (QuotientGroup.eq_one_iff _).mpr hj, one_mul]
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem q ht
  rcases (mem_involution_zpowers_iff hqs).mp hqa with heq | heq
  · exact (QuotientGroup.eq_one_iff _).mp heq
  · have hdvd : 2 ∣ Nat.card A := by
      have hm := orderOf_map_dvd q a
      rw [heq, hqs] at hm
      exact hm.trans (A.orderOf_dvd_natCard ha)
    exact False.elim (hAodd.not_two_dvd_nat hdvd)

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
