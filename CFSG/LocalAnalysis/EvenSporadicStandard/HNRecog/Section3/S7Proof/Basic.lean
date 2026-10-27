module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Hyps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpRows

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem s7_isConj_conj {u v : G} (k : G) (h : IsConj u v) : IsConj u (k * v * k⁻¹) :=
  h.trans (isConj_iff.mpr ⟨k, rfl⟩)

private theorem s7_conj_fix {a k : G} (hk : k ∈ Gx a) : k * a * k⁻¹ = a := by
  rw [← mem_Gx.mp hk]
  group

private theorem s7_mul_conj {a t k : G} (hk : k ∈ Gx a) :
    a * (k * t * k⁻¹) = k * (a * t) * k⁻¹ :=
  mul_conj_of_fix (s7_conj_fix hk)

theorem s7_sq_of_isConj_a {a z t : G} (H : S7Hyps a z) (ht : IsConj a t) : t ^ 2 = 1 := by
  have h := pow_orderOf_eq_one t
  rwa [perp_orderOf_of_isConj_a H.isF5 ht] at h

theorem s7_sq_of_isConj_z {a z t : G} (H : S7Hyps a z) (ht : IsConj z t) : t ^ 2 = 1 := by
  have h := pow_orderOf_eq_one t
  rwa [perp_orderOf_of_isConj_z H.isF5 ht] at h

theorem s7_ne_one_of_isConj_a {a z t : G} (H : S7Hyps a z) (ht : IsConj a t) : t ≠ 1 := by
  intro h
  have h2 := perp_orderOf_of_isConj_a H.isF5 ht
  rw [h, orderOf_one] at h2
  omega

theorem s7_ne_one_of_isConj_z {a z t : G} (H : S7Hyps a z) (ht : IsConj z t) : t ≠ 1 := by
  intro h
  have h2 := perp_orderOf_of_isConj_z H.isF5 ht
  rw [h, orderOf_one] at h2
  omega

theorem s7_not_isConj {a z : G} (H : S7Hyps a z) : ¬ IsConj a z := by
  intro haz
  have hT5 := H.tableV.self
  obtain ⟨b, hb⟩ := (hT5.partition.orbit 0).nonempty
  have hb' : b ∈ orb2A a a := hb
  have hdisj := hT5.partition.disjoint 0 1 (by decide)
  have hb1 : b ∈ orb2B a z a := ⟨hb'.1, haz.symm.trans hb'.2⟩
  exact Set.disjoint_left.mp hdisj hb hb1

theorem s7_not_both {a z t : G} (H : S7Hyps a z) (h1 : IsConj a t) (h2 : IsConj z t) : False := by
  exact s7_not_isConj H (h1.trans h2.symm)

theorem s7_comm_orb2A {a z x t : G} (H : S7Hyps a z) (hx : IsConj a x) (ht : t ∈ orb2A a x) :
    x * t = t * x := by
  exact comm_of_sq_mul (s7_sq_of_isConj_a H hx) (s7_sq_of_isConj_a H ht.1)
    (s7_sq_of_isConj_a H ht.2)

theorem s7_comm_orb2B {a z x t : G} (H : S7Hyps a z) (hx : IsConj a x) (ht : t ∈ orb2B a z x) :
    x * t = t * x := by
  exact comm_of_sq_mul (s7_sq_of_isConj_a H hx) (s7_sq_of_isConj_a H ht.1)
    (s7_sq_of_isConj_z H ht.2)

theorem s7_comm_orb2BB {a z x t : G} (H : S7Hyps a z) (hx : IsConj a x) (ht : t ∈ orb2BB a z x) :
    x * t = t * x := by
  exact comm_of_sq_mul (s7_sq_of_isConj_a H hx) (s7_sq_of_isConj_z H ht.1)
    (s7_sq_of_isConj_z H ht.2)

theorem s7_D_subset {a z x : G} (H : S7Hyps a z) (hx : IsConj a x) :
    orb2A a a ∩ orb2A a x ⊆ {t | t ∈ Gxy a x ∧ orderOf t = 2} := by
  intro t ht
  refine ⟨mem_Gxy.mpr ⟨mem_Gx.mpr ?_, mem_Gx.mpr (s7_comm_orb2A H hx ht.2)⟩,
    perp_orderOf_of_isConj_a H.isF5 ht.1.1⟩
  exact s7_comm_orb2A H (IsConj.refl a) ht.1

theorem s7_E2_subset {a z x : G} (H : S7Hyps a z) (hx : IsConj a x) :
    orb2B a z a ∩ orb2B a z x ⊆ {t | t ∈ Gxy a x ∧ orderOf t = 2} := by
  intro t ht
  refine ⟨mem_Gxy.mpr ⟨mem_Gx.mpr ?_, mem_Gx.mpr (s7_comm_orb2B H hx ht.2)⟩,
    perp_orderOf_of_isConj_a H.isF5 ht.1.1⟩
  exact s7_comm_orb2B H (IsConj.refl a) ht.1

theorem s7_E3_subset {a z x : G} (H : S7Hyps a z) (hx : IsConj a x) :
    orb2BB a z a ∩ orb2BB a z x ⊆ {t | t ∈ Gxy a x ∧ orderOf t = 2} := by
  intro t ht
  refine ⟨mem_Gxy.mpr ⟨mem_Gx.mpr ?_, mem_Gx.mpr (s7_comm_orb2BB H hx ht.2)⟩,
    perp_orderOf_of_isConj_z H.isF5 ht.1.1⟩
  exact s7_comm_orb2BB H (IsConj.refl a) ht.1

theorem s7_conj_orb2A {a x t : G} (k : G) (ht : t ∈ orb2A a x) :
    k * t * k⁻¹ ∈ orb2A a (k * x * k⁻¹) := by
  refine ⟨s7_isConj_conj k ht.1, ?_⟩
  rw [show k * x * k⁻¹ * (k * t * k⁻¹) = k * (x * t) * k⁻¹ by group]
  exact s7_isConj_conj k ht.2

theorem s7_conj_D {a x t k : G} (hk : k ∈ Gxy a x) (ht : t ∈ orb2A a a ∩ orb2A a x) :
    k * t * k⁻¹ ∈ orb2A a a ∩ orb2A a x := by
  exact perp_conj_mem_inter hk ht

theorem s7_conj_E2 {a z x t k : G} (hk : k ∈ Gxy a x) (ht : t ∈ orb2B a z a ∩ orb2B a z x) :
    k * t * k⁻¹ ∈ orb2B a z a ∩ orb2B a z x := by
  obtain ⟨hk1, hk2⟩ := mem_Gxy.mp hk
  refine ⟨⟨s7_isConj_conj k ht.1.1, ?_⟩, ⟨s7_isConj_conj k ht.2.1, ?_⟩⟩
  · rw [s7_mul_conj hk1]
    exact s7_isConj_conj k ht.1.2
  · rw [s7_mul_conj hk2]
    exact s7_isConj_conj k ht.2.2

theorem s7_conj_E3 {a z x t k : G} (hk : k ∈ Gxy a x) (ht : t ∈ orb2BB a z a ∩ orb2BB a z x) :
    k * t * k⁻¹ ∈ orb2BB a z a ∩ orb2BB a z x := by
  obtain ⟨hk1, hk2⟩ := mem_Gxy.mp hk
  refine ⟨⟨s7_isConj_conj k ht.1.1, ?_⟩, ⟨s7_isConj_conj k ht.2.1, ?_⟩⟩
  · rw [s7_mul_conj hk1]
    exact s7_isConj_conj k ht.1.2
  · rw [s7_mul_conj hk2]
    exact s7_isConj_conj k ht.2.2

theorem s7_disjoint {a z : G} (H : S7Hyps a z) (x : G) :
    ∀ i j : Fin 3, i ≠ j → Disjoint (s7Set a z x i) (s7Set a z x j) := by
  have h01 : Disjoint (orb2A a a ∩ orb2A a x) (orb2B a z a ∩ orb2B a z x) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact s7_not_both H ht.1.2 ht'.1.2
  have h02 : Disjoint (orb2A a a ∩ orb2A a x) (orb2BB a z a ∩ orb2BB a z x) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact s7_not_both H ht.1.1 ht'.1.1
  have h12 : Disjoint (orb2B a z a ∩ orb2B a z x) (orb2BB a z a ∩ orb2BB a z x) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact s7_not_both H ht.1.1 ht'.1.1
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01
  · exact h02
  · exact h01.symm
  · exact absurd rfl hij
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact absurd rfl hij

theorem s7_mem_sSet_four {a z c t : G} (H : S7Hyps a z) (hc : IsConj a c)
    (hord : orderOf (a * c) = 3) (ht : t ∈ orb2A a a ∩ orb2A a c) : c ∈ sSet a z t 4 := by
  have ha2 : a * a = 1 := by simpa [pow_two] using s7_sq_of_isConj_a H (IsConj.refl a)
  have ht2 : orderOf t = 2 := perp_orderOf_of_isConj_a H.isF5 ht.1.1
  refine ⟨⟨hc, ?_, ?_, ?_⟩, hord⟩
  · exact IsConj.trans ht.2.2 (isConj_iff.mpr ⟨t, by group⟩)
  · intro hca
    rw [hca, ha2, orderOf_one] at hord
    omega
  · intro hca
    rw [hca, ← mul_assoc, ha2, one_mul, ht2] at hord
    omega

theorem s7_swap_D {a x t : G} (hx : IsConj a x) (ht : t ∈ orb2A a a ∩ orb2A a x) :
    t ∈ orb2A x x ∩ orb2A x a := by
  exact ⟨⟨hx.symm.trans ht.1.1, hx.symm.trans ht.2.2⟩, hx.symm.trans ht.1.1, hx.symm.trans ht.1.2⟩

theorem s7_orderOf_swap (a x : G) : orderOf (x * a) = orderOf (a * x) := by
  have h : SemiconjBy a⁻¹ (a * x) (x * a) := by
    show a⁻¹ * (a * x) = x * a * a⁻¹
    group
  exact (SemiconjBy.orderOf_eq a⁻¹ h).symm

end CFSG.EvenSporadicStandard.HNRecog.Section3
