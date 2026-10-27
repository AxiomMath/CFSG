module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

private theorem sixA_isConj_conj {u v k : G} (h : IsConj u v) : IsConj u (k * v * k⁻¹) :=
  h.trans (isConj_iff.2 ⟨k, rfl⟩)

private theorem sixA_conj_fix {y k : G} (hk : k ∈ Gx y) : k * y * k⁻¹ = y := by
  have h : k * y = y * k := (mem_Gx.mp hk).symm
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem sixA_not_isConj (hT : TableVFacts a z) : ¬ IsConj a z := by
  intro hac
  obtain ⟨c, hc⟩ := (hT.partition.orbit 0).nonempty
  have hc' : c ∈ orb2A a a := hc
  exact Set.disjoint_left.mp (hT.partition.disjoint 0 1 (by decide)) hc
    ⟨hc'.1, hac.symm.trans hc'.2⟩

theorem sixA_not_both (hnc : ¬ IsConj a z) {w : G} (h1 : IsConj a w) (h2 : IsConj z w) : False :=
  hnc (h1.trans h2.symm)

theorem sixA_mem_Gxy_of_orders (h : IsF5Type a z) (hx : x ∈ orb6A a a) {c : G}
    (hc : orderOf c = 2) (hac : orderOf (a * c) = 2) (hxc : orderOf (x * c) = 2) :
    c ∈ Gxy a x := by
  have hc2 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hac2 : (a * c) ^ 2 = 1 := by rw [← hac]; exact pow_orderOf_eq_one (a * c)
  have hxc2 : (x * c) ^ 2 = 1 := by rw [← hxc]; exact pow_orderOf_eq_one (x * c)
  rw [mem_Gxy, mem_Gx, mem_Gx]
  exact ⟨comm_of_sq_mul (sixA_a_sq h) hc2 hac2, comm_of_sq_mul (sixA_x_sq h hx) hc2 hxc2⟩

private theorem sixA_mem_Gxy_of_classes (h : IsF5Type a z) (hx : x ∈ orb6A a a) {c : G}
    (hc : IsConj a c ∨ IsConj z c) (hac : IsConj a (a * c) ∨ IsConj z (a * c))
    (hxc : IsConj a (x * c) ∨ IsConj z (x * c)) : c ∈ Gxy a x ∧ orderOf c = 2 :=
  ⟨sixA_mem_Gxy_of_orders h hx
      (hc.elim (perp_orderOf_of_isConj_a h) (perp_orderOf_of_isConj_z h))
      (hac.elim (perp_orderOf_of_isConj_a h) (perp_orderOf_of_isConj_z h))
      (hxc.elim (perp_orderOf_of_isConj_a h) (perp_orderOf_of_isConj_z h)),
    hc.elim (perp_orderOf_of_isConj_a h) (perp_orderOf_of_isConj_z h)⟩

theorem sixA_subset (h : IsF5Type a z) (hx : x ∈ orb6A a a) (i : Fin 5) :
    sixASet a z x i ⊆ {t | t ∈ Gxy a x ∧ orderOf t = 2} := by
  intro c hc
  fin_cases i
  · change c = (a * x) ^ 3 at hc
    change c ∈ Gxy a x ∧ orderOf c = 2
    rw [hc]
    exact ⟨sixA_b_mem_Gxy_x h hx, sixA_orderOf_b h hx⟩
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hc
    change c ∈ Gxy a x ∧ orderOf c = 2
    exact sixA_mem_Gxy_of_classes h hx (Or.inl hc.1.1) (Or.inr hc.1.2) (Or.inr hc.2.2)
  · change (IsConj z c ∧ IsConj z (a * c)) ∧ (IsConj z c ∧ IsConj z (x * c)) at hc
    change c ∈ Gxy a x ∧ orderOf c = 2
    exact sixA_mem_Gxy_of_classes h hx (Or.inr hc.1.1) (Or.inr hc.1.2) (Or.inr hc.2.2)
  · change (IsConj a c ∧ IsConj a (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hc
    change c ∈ Gxy a x ∧ orderOf c = 2
    exact sixA_mem_Gxy_of_classes h hx (Or.inl hc.1.1) (Or.inl hc.1.2) (Or.inr hc.2.2)
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj a (x * c)) at hc
    change c ∈ Gxy a x ∧ orderOf c = 2
    exact sixA_mem_Gxy_of_classes h hx (Or.inl hc.1.1) (Or.inr hc.1.2) (Or.inl hc.2.2)

private theorem sixA_disjoint_lt (h : IsF5Type a z) (hx : x ∈ orb6A a a)
    (hnc : ¬ IsConj a z) {i j : Fin 5} (hij : i < j) :
    Disjoint (sixASet a z x i) (sixASet a z x j) := by
  rw [Set.disjoint_left]
  intro c hi hj
  fin_cases i <;> fin_cases j
  all_goals try exact absurd hij (by decide)
  · change c = (a * x) ^ 3 at hi
    change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hj
    rw [hi] at hj
    exact sixA_not_both hnc (sixA_conj_ab h hx) hj.1.2
  · change c = (a * x) ^ 3 at hi
    change (IsConj z c ∧ IsConj z (a * c)) ∧ (IsConj z c ∧ IsConj z (x * c)) at hj
    rw [hi] at hj
    exact sixA_not_both hnc (sixA_of_mem hx).2.2 hj.1.1
  · change c = (a * x) ^ 3 at hi
    change (IsConj a c ∧ IsConj a (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hj
    rw [hi] at hj
    exact sixA_not_both hnc (sixA_conj_y h hx) hj.2.2
  · change c = (a * x) ^ 3 at hi
    change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj a (x * c)) at hj
    rw [hi] at hj
    exact sixA_not_both hnc (sixA_conj_ab h hx) hj.1.2
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hi
    change (IsConj z c ∧ IsConj z (a * c)) ∧ (IsConj z c ∧ IsConj z (x * c)) at hj
    exact sixA_not_both hnc hi.1.1 hj.1.1
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hi
    change (IsConj a c ∧ IsConj a (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hj
    exact sixA_not_both hnc hj.1.2 hi.1.2
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hi
    change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj a (x * c)) at hj
    exact sixA_not_both hnc hj.2.2 hi.2.2
  · change (IsConj z c ∧ IsConj z (a * c)) ∧ (IsConj z c ∧ IsConj z (x * c)) at hi
    change (IsConj a c ∧ IsConj a (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hj
    exact sixA_not_both hnc hj.1.1 hi.1.1
  · change (IsConj z c ∧ IsConj z (a * c)) ∧ (IsConj z c ∧ IsConj z (x * c)) at hi
    change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj a (x * c)) at hj
    exact sixA_not_both hnc hj.1.1 hi.1.1
  · change (IsConj a c ∧ IsConj a (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hi
    change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj a (x * c)) at hj
    exact sixA_not_both hnc hi.1.2 hj.1.2

theorem sixA_disjoint (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hnc : ¬ IsConj a z) (i j : Fin 5)
    (hij : i ≠ j) : Disjoint (sixASet a z x i) (sixASet a z x j) := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact sixA_disjoint_lt h hx hnc hij
  · exact (sixA_disjoint_lt h hx hnc hij).symm

theorem sixA_conj_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a) (i : Fin 5) {k c : G}
    (hk : k ∈ Gxy a x) (hc : c ∈ sixASet a z x i) : k * c * k⁻¹ ∈ sixASet a z x i := by
  obtain ⟨hka, hkx⟩ := mem_Gxy.mp hk
  have hkac : k * a * k⁻¹ = a := sixA_conj_fix hka
  have hkxc : k * x * k⁻¹ = x := sixA_conj_fix hkx
  fin_cases i
  · change c = (a * x) ^ 3 at hc
    change k * c * k⁻¹ = (a * x) ^ 3
    rw [hc, sixA_comm_b_of_mem hk]
    group
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hc
    change (IsConj a (k * c * k⁻¹) ∧ IsConj z (a * (k * c * k⁻¹))) ∧
      (IsConj a (k * c * k⁻¹) ∧ IsConj z (x * (k * c * k⁻¹)))
    exact ⟨⟨sixA_isConj_conj hc.1.1,
        by rw [mul_conj_of_fix hkac]; exact sixA_isConj_conj hc.1.2⟩,
      sixA_isConj_conj hc.1.1,
      by rw [mul_conj_of_fix hkxc]; exact sixA_isConj_conj hc.2.2⟩
  · change (IsConj z c ∧ IsConj z (a * c)) ∧ (IsConj z c ∧ IsConj z (x * c)) at hc
    change (IsConj z (k * c * k⁻¹) ∧ IsConj z (a * (k * c * k⁻¹))) ∧
      (IsConj z (k * c * k⁻¹) ∧ IsConj z (x * (k * c * k⁻¹)))
    exact ⟨⟨sixA_isConj_conj hc.1.1,
        by rw [mul_conj_of_fix hkac]; exact sixA_isConj_conj hc.1.2⟩,
      sixA_isConj_conj hc.1.1,
      by rw [mul_conj_of_fix hkxc]; exact sixA_isConj_conj hc.2.2⟩
  · change (IsConj a c ∧ IsConj a (a * c)) ∧ (IsConj a c ∧ IsConj z (x * c)) at hc
    change (IsConj a (k * c * k⁻¹) ∧ IsConj a (a * (k * c * k⁻¹))) ∧
      (IsConj a (k * c * k⁻¹) ∧ IsConj z (x * (k * c * k⁻¹)))
    exact ⟨⟨sixA_isConj_conj hc.1.1,
        by rw [mul_conj_of_fix hkac]; exact sixA_isConj_conj hc.1.2⟩,
      sixA_isConj_conj hc.1.1,
      by rw [mul_conj_of_fix hkxc]; exact sixA_isConj_conj hc.2.2⟩
  · change (IsConj a c ∧ IsConj z (a * c)) ∧ (IsConj a c ∧ IsConj a (x * c)) at hc
    change (IsConj a (k * c * k⁻¹) ∧ IsConj z (a * (k * c * k⁻¹))) ∧
      (IsConj a (k * c * k⁻¹) ∧ IsConj a (x * (k * c * k⁻¹)))
    exact ⟨⟨sixA_isConj_conj hc.1.1,
        by rw [mul_conj_of_fix hkac]; exact sixA_isConj_conj hc.1.2⟩,
      sixA_isConj_conj hc.1.1,
      by rw [mul_conj_of_fix hkxc]; exact sixA_isConj_conj hc.2.2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
