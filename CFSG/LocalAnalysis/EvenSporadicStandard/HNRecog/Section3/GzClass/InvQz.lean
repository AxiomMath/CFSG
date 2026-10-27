module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzInvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj_invQz {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

private theorem eq_one_or_eq_of_mem_zpowers_invQz {G : Type} [Group G] {z q : G}
    (hz : orderOf z = 2) (hq : q ∈ Subgroup.zpowers z) : q = 1 ∨ q = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  rw [← zpow_mod_orderOf, hz]
  have hn : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hn with hn | hn
  · left
    rw [hn]
    simp
  · right
    rw [hn]
    simp

theorem isConj_of_mem_Qz_involution (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hOrb : GzOrbitFacts a z) {t : G} (htQ : t ∈ Qz z)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : IsConj a t ∨ IsConj z t := by
  classical
  have hNot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hGz : Nat.card ↥(Gx z) = 2 ^ 9 * 7200 := card_centralizer_z_of_isF5Type h
  have hordA : ∀ q : G, IsConj a q → orderOf q = 2 := fun q hq =>
    (orderOf_eq_of_isConj_invQz hq).symm.trans h.orderOf_a
  have hordB : ∀ q : G, IsConj z q → orderOf q = 2 := fun q hq =>
    (orderOf_eq_of_isConj_invQz hq).symm.trans h.orderOf_z
  have hsq : ∀ q : G, orderOf q = 2 → q ^ 2 = 1 := fun q hq => by
    rw [← hq]
    exact pow_orderOf_eq_one q
  have hAcard : Nat.card ↥{q : G | q ∈ Qz z ∧ IsConj a q} = 120 := by
    obtain ⟨c, hc⟩ := hOrb.orbit_QA.1.nonempty
    have h2 := hOrb.orbit_QA.1.card_mul_card_stab hc
    rw [hOrb.orbit_QA.2 c hc, hGz, show (2 : ℕ) ^ 11 * 15 = 30720 by norm_num,
      show (2 : ℕ) ^ 9 * 7200 = 3686400 by norm_num] at h2
    omega
  have hBcard : Nat.card ↥{q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} = 150 := by
    obtain ⟨c, hc⟩ := hOrb.orbit_QB.1.nonempty
    have h2 := hOrb.orbit_QB.1.card_mul_card_stab hc
    rw [hOrb.orbit_QB.2 c hc, hGz, show (2 : ℕ) ^ 13 * 3 = 24576 by norm_num,
      show (2 : ℕ) ^ 9 * 7200 = 3686400 by norm_num] at h2
    omega
  have hAN : {q : G | q ∈ Qz z ∧ IsConj a q} ⊆
      {q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} := by
    intro q hq
    have hqQ : q ∈ Qz z := hq.1
    have hqA : IsConj a q := hq.2
    have hord : orderOf q = 2 := hordA q hqA
    refine ⟨hqQ, hsq q hord, fun hqz => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers_invQz h.orderOf_z hqz with h1 | h3
    · have := hord
      rw [h1, orderOf_one] at this
      omega
    · exact hNot (h3 ▸ hqA)
  have hBN : {q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} ⊆
      {q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} := by
    intro q hq
    have hqQ : q ∈ Qz z := hq.1
    have hqB : IsConj z q := hq.2.1
    have hqz : q ≠ z := hq.2.2
    have hord : orderOf q = 2 := hordB q hqB
    refine ⟨hqQ, hsq q hord, fun hmem => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers_invQz h.orderOf_z hmem with h1 | h3
    · have := hord
      rw [h1, orderOf_one] at this
      omega
    · exact hqz h3
  have hABdisj : Disjoint {q : G | q ∈ Qz z ∧ IsConj a q}
      {q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} := by
    rw [Set.disjoint_left]
    intro q hqA hqB
    exact hNot (hqA.2.trans hqB.2.1.symm)
  obtain ⟨S, hpart, hcard0, hcard1⟩ := inv_classes_G hC h hOrb.irreducible
  have hNunion : S 0 ∪ S 1 =
      {q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} := by
    apply Set.Subset.antisymm
    · intro q hq
      rcases hq with hq | hq
      · exact hpart.subset 0 hq
      · exact hpart.subset 1 hq
    · intro q hq
      obtain ⟨i, hi⟩ := hpart.cover q hq
      fin_cases i
      · exact Set.mem_union_left _ hi
      · exact Set.mem_union_right _ hi
  have hNcard : ({q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} : Set G).ncard =
      270 := by
    rw [← hNunion, Set.ncard_union_eq (hpart.disjoint 0 1 (by decide))]
    have h0 : (S 0).ncard = 150 := by
      simpa only [Nat.card_coe_set_eq] using hcard0
    have h1 : (S 1).ncard = 120 := by
      simpa only [Nat.card_coe_set_eq] using hcard1
    omega
  have hABncard : ({q : G | q ∈ Qz z ∧ IsConj a q} ∪
      {q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} : Set G).ncard = 270 := by
    rw [Set.ncard_union_eq hABdisj]
    have h0 : {q : G | q ∈ Qz z ∧ IsConj a q}.ncard = 120 := by
      simpa only [Nat.card_coe_set_eq] using hAcard
    have h1 : {q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z}.ncard = 150 := by
      simpa only [Nat.card_coe_set_eq] using hBcard
    omega
  have hABeq : ({q : G | q ∈ Qz z ∧ IsConj a q} ∪
      {q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z}) =
      {q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} :=
    Set.eq_of_subset_of_ncard_le (Set.union_subset hAN hBN) (by omega)
  by_cases htz : t ∈ Subgroup.zpowers z
  · right
    rcases eq_one_or_eq_of_mem_zpowers_invQz h.orderOf_z htz with h1 | h3
    · exact absurd h1 ht1
    · simpa [h3] using (IsConj.refl z)
  · have ht : t ∈ ({q : G | q ∈ Qz z ∧ IsConj a q} ∪
        {q : G | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z}) := by
      rw [hABeq]
      exact ⟨htQ, ht2, htz⟩
    rcases ht with htA | htB
    · exact Or.inl htA.2
    · exact Or.inr htB.2.1

end CFSG.EvenSporadicStandard.HNRecog.Section3
