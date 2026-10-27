module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem conj_fix_of_mem_Gx {a k : G} (hk : k ∈ Gx a) : k * a * k⁻¹ = a := by
  rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]

private theorem mul_comm_of_mem_Gx {a k : G} (hk : k ∈ Gx a) : a * k = k * a := by
  calc a * k = (k * a * k⁻¹) * k := by rw [conj_fix_of_mem_Gx hk]
    _ = k * a := by group

private theorem isConj_conj {k a x : G} (h : IsConj a x) :
    IsConj (k * a * k⁻¹) (k * x * k⁻¹) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨k * c * k⁻¹, by group⟩

private theorem orderOf_conj (k x : G) : orderOf (k * x * k⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj k) x)

private theorem mul_conj_eq {a c k : G} (hk : k ∈ Gx a) :
    a * (k * c * k⁻¹) = k * (a * c) * k⁻¹ := by
  have hak := mul_comm_of_mem_Gx hk
  calc a * (k * c * k⁻¹) = (a * k) * c * k⁻¹ := by group
    _ = (k * a) * c * k⁻¹ := by rw [hak]
    _ = k * (a * c) * k⁻¹ := by group

private theorem conj_mem_sBase {a x c k : G} (hk : k ∈ Gx a) (hc : c ∈ sBase a x) :
    k * c * k⁻¹ ∈ sBase a (k * x * k⁻¹) := by
  obtain ⟨hcA, hcx, hca, hcax⟩ := hc
  have hka := conj_fix_of_mem_Gx hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hka] using isConj_conj (k := k) hcA
  · rw [show (k * x * k⁻¹) * (k * c * k⁻¹) = k * (x * c) * k⁻¹ by group]
    simpa [hka] using isConj_conj (k := k) hcx
  · intro h
    apply hca
    have h' : k * c * k⁻¹ = k * a * k⁻¹ := by rw [h, hka]
    have := congrArg (fun t => k⁻¹ * t * k) h'
    simpa using this
  · intro h
    apply hcax
    have hax : a * (k * x * k⁻¹) = k * (a * x) * k⁻¹ := mul_conj_eq hk
    have h' : k * c * k⁻¹ = k * (a * x) * k⁻¹ := by rw [hax] at h; exact h
    have := congrArg (fun t => k⁻¹ * t * k) h'
    simpa using this

theorem perp_conj_mem_orb2A {a k x : G} (hk : k ∈ Gx a) (hx : x ∈ orb2A a a) :
    k * x * k⁻¹ ∈ orb2A a a := by
  obtain ⟨hxA, hxax⟩ := hx
  have hka := conj_fix_of_mem_Gx hk
  refine ⟨?_, ?_⟩
  · simpa [hka] using isConj_conj (k := k) hxA
  · rw [mul_conj_eq hk]
    simpa [hka] using isConj_conj (k := k) hxax

theorem perp_conj_mem_inter {a c k x : G} (hk : k ∈ Gxy a c) (hx : x ∈ orb2A a a ∩ orb2A a c) :
    k * x * k⁻¹ ∈ orb2A a a ∩ orb2A a c := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hk1, hk2⟩ := mem_Gxy.mp hk
  have hka := conj_fix_of_mem_Gx hk1
  obtain ⟨hx2A, hx2cx⟩ := hx2
  refine ⟨perp_conj_mem_orb2A hk1 hx1, ?_, ?_⟩
  · simpa [hka] using isConj_conj (k := k) hx2A
  · rw [mul_conj_eq hk2]
    simpa [hka] using isConj_conj (k := k) hx2cx

theorem perp_conj_mem_sSet {a z x c k : G} (h : IsF5Type a z) (hk : k ∈ Gx a) (i : Fin 6)
    (hc : c ∈ sSet a z x i) : k * c * k⁻¹ ∈ sSet a z (k * x * k⁻¹) i := by
  fin_cases i <;> simp [sSet, -isConj_iff] at hc ⊢
  · obtain ⟨hbase, hAc⟩ := hc
    exact ⟨conj_mem_sBase hk hbase, by
      rw [mul_conj_eq hk]
      exact IsConj.trans hAc (isConj_iff.mpr ⟨k, rfl⟩)⟩
  · obtain ⟨hbase, hzc⟩ := hc
    exact ⟨conj_mem_sBase hk hbase, by
      rw [mul_conj_eq hk]
      exact IsConj.trans hzc (isConj_iff.mpr ⟨k, rfl⟩)⟩
  · obtain ⟨hbase, hp⟩ := hc
    exact ⟨conj_mem_sBase hk hbase, by rw [mul_conj_eq hk, conj_pow, hp]⟩
  · obtain ⟨hbase, hz⟩ := hc
    refine ⟨conj_mem_sBase hk hbase, ?_⟩
    rw [mul_conj_eq hk, conj_pow]
    exact IsConj.trans hz (isConj_iff.mpr ⟨k, rfl⟩)
  · obtain ⟨hbase, ho⟩ := hc
    exact ⟨conj_mem_sBase hk hbase, by rw [mul_conj_eq hk, orderOf_conj, ho]⟩
  · obtain ⟨hbase, hp⟩ := hc
    exact ⟨conj_mem_sBase hk hbase, by rw [mul_conj_eq hk, conj_pow, hp]⟩

theorem perp_self_mem_inter {a z b c : G} (h : IsF5Type a z) (hb : b ∈ orb2A a a)
    (hc : c ∈ sBase a b) : b ∈ orb2A a a ∩ orb2A a c := by
  obtain ⟨_, hbc, _⟩ := hc
  exact ⟨hb, hb.1, IsConj.trans hbc (isConj_iff.mpr ⟨c, by group⟩)⟩

theorem perp_mem_sBase {a z b c x : G} (h : IsF5Type a z) (hc : c ∈ sBase a b)
    (hx : x ∈ orb2A a a ∩ orb2A a c) (hord : 3 ≤ orderOf (a * c)) : c ∈ sBase a x := by
  obtain ⟨hcA, _, hca, _⟩ := hc
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨_, hxc⟩ := hx2
  refine ⟨hcA, ?_, hca, ?_⟩
  · exact IsConj.trans hxc (isConj_iff.mpr ⟨c⁻¹, by group⟩)
  · intro hcax
    have ha2 : a * a = 1 := by
      simpa [pow_two, h.orderOf_a] using pow_orderOf_eq_one a
    have hx2order : orderOf x = 2 := perp_orderOf_of_isConj_a h hx1.1
    rw [hcax, ← mul_assoc, ha2, one_mul, hx2order] at hord
    omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
