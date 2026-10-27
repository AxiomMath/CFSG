module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Bookkeep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Compat3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

private theorem sq_eq_one_of_orderOf_eq_two {X : Type*} [Group X] {x : X} (hx : orderOf x = 2) :
    x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

theorem cp_exists_perp_4A (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    ∃ d, d ∈ orb2A a a ∩ orb2A a y := by
  have hpart := h.loc.tableV.self.partition
  have h2A : IsConjOrbit (Gx a) (orb2A a a) := by simpa [tab5Set] using hpart.orbit 0
  have h4A : IsConjOrbit (Gx a) (orb4A a z a) := by simpa [tab5Set] using hpart.orbit 2
  obtain ⟨b₀, hb₀⟩ := h2A.nonempty
  have hIV := h.loc.tableIV.self.partition b₀ hb₀
  obtain ⟨y₀, hy₀⟩ := (hIV.orbit 3).nonempty
  have hy₀4A : y₀ ∈ orb4A a z a := by
    have h1 : y₀ ∈ sBase a b₀ ∧ IsConj z ((a * y₀) ^ 2) := by simpa [sSet] using hy₀
    exact ⟨h1.1.1, h1.2⟩
  obtain ⟨d₀, hd₀⟩ := (h.loc.perp.self.class_4A b₀ hb₀ y₀ (by simpa [sSet] using hy₀)).nonempty
  obtain ⟨k, hk, hky⟩ := h4A.transitive y₀ hy₀4A y hy
  have hka : k * a * k⁻¹ = a := by
    rw [← mem_Gx.1 hk, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨k * d₀ * k⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact hd₀.1.1.trans (isConj_iff.2 ⟨k, rfl⟩)
  · have e : a * (k * d₀ * k⁻¹) = k * (a * d₀) * k⁻¹ := by
      calc a * (k * d₀ * k⁻¹) = (k * a * k⁻¹) * (k * d₀ * k⁻¹) := by rw [hka]
        _ = k * (a * d₀) * k⁻¹ := by group
    rw [e]
    exact hd₀.1.2.trans (isConj_iff.2 ⟨k, rfl⟩)
  · exact hd₀.2.1.trans (isConj_iff.2 ⟨k, rfl⟩)
  · have e : y * (k * d₀ * k⁻¹) = k * (y₀ * d₀) * k⁻¹ := by
      calc y * (k * d₀ * k⁻¹) = (k * y₀ * k⁻¹) * (k * d₀ * k⁻¹) := by rw [hky]
        _ = k * (y₀ * d₀) * k⁻¹ := by group
    rw [e]
    exact hd₀.2.2.trans (isConj_iff.2 ⟨k, rfl⟩)

theorem cp_not_comm_of_orb4A (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    a * y ≠ y * a := by
  intro hcomm
  have ha2 : a * a = 1 := sq_eq_one_of_orderOf_eq_two h.typ.orderOf_a
  have hy2 : y * y = 1 := sq_eq_one_of_orderOf_eq_two (h.orderOf_eq_two (Or.inl hy.1))
  have hsq : (a * y) ^ 2 = 1 := by
    rw [pow_two]
    calc a * y * (a * y) = a * (y * a) * y := by group
      _ = a * (a * y) * y := by rw [hcomm]
      _ = (a * a) * (y * y) := by group
      _ = 1 := by rw [ha2, hy2, mul_one]
  have h2 := h.orderOf_eq_two (Or.inr hy.2)
  rw [hsq, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem cp_class_perp_4A (h : F5Std a z) {c : G} (hc : c ∈ orb4A a z a) :
    IsConjOrbit (Gxy a c) (orb2A a a ∩ orb2A a c) := by
  obtain ⟨d, hd⟩ := cp_exists_perp_4A h hc
  have hdG : d ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hd.1
  have hdc : d ∈ Gx c := h.mem_Gx_of_orb2A hc.1 hd.2
  have hnc := cp_not_comm_of_orb4A h hc
  have hcd : c * d = d * c := mem_Gx.1 hdc
  have hmem : c ∈ sSet a z d 3 := by
    have h1 : c ∈ sBase a d ∧ IsConj z ((a * c) ^ 2) := by
      refine ⟨⟨hc.1, ?_, ?_, ?_⟩, hc.2⟩
      · rw [← hcd]
        exact hd.2.2
      · intro hca
        apply hnc
        rw [hca]
      · intro hca
        apply hnc
        have had : a * d = d * a := mem_Gx.1 hdG
        rw [hca]
        calc a * (a * d) = a * (d * a) := by rw [had]
          _ = (a * d) * a := by rw [mul_assoc]
    simpa [sSet] using h1
  exact h.loc.perp.self.class_4A d hd.1 c hmem

theorem cp_isInvReps_4A (hC : Cover4A) (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a)
    {d : G} (hd : d ∈ orb2A a a ∩ orb2A a y) : IsInvReps a y (InvIn (Gxyz a d y)) := by
  have hdG : d ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hd.1
  have hdy : d ∈ Gx y := h.mem_Gx_of_orb2A hy.1 hd.2
  have hsub : ∀ g, g ∈ Gxyz a d y → g ∈ Gxy a y := fun g hg =>
    mem_Gxy.2 ⟨(mem_Gxyz.1 hg).1, (mem_Gxyz.1 hg).2.2⟩
  obtain ⟨hz1, hz2⟩ := cp_central_inv h hy.1 (k := 2) (Or.inr hy.2)
  refine ⟨fun r hr => ⟨hsub r hr.1, hr.2⟩, fun t ht => hC h y hy d hd t ht, ?_⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨r, -, hgr⟩ := Set.mem_iUnion₂.mp hg
    exact mem_Gxy.2 ⟨(mem_Gxyz.1 hgr).1, (mem_Gxyz.1 hgr).2.2⟩
  · intro g hg
    refine Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨(a * y) ^ 2, ?_, ?_⟩)
    · have hcomm : Commute d ((a * y) ^ 2) := by
        have h1 : Commute d a := (mem_Gx.1 hdG).symm
        have h2 : Commute d y := (mem_Gx.1 hdy).symm
        exact (h1.mul_right h2).pow_right 2
      exact ⟨mem_Gxyz.2 ⟨(mem_Gxy.1 hz1.1).1, mem_Gx.2 hcomm.eq, (mem_Gxy.1 hz1.1).2⟩, hz1.2⟩
    · rw [hz2]
      exact hg

theorem cp_agree_trans (F : Fam a α) (ha : orderOf a = 2) {y d r r' : G}
    (hr : r ∈ InvIn (Gxy a y)) (hr' : r' ∈ InvIn (Gxy a y))
    (h1 : F.app d y = F.app r y ∨ F.app d y = F.app r (a * y * a⁻¹))
    (h2 : F.app d y = F.app r' y ∨ F.app d y = F.app r' (a * y * a⁻¹)) :
    F.app r y = F.app r' y ∨ F.app r y = F.app r' (a * y * a⁻¹) := by
  have hc2 : α a * α a = 1 :=
    sq_eq_one_of_orderOf_eq_two (((cp_alpha_iso F ha).orderOf_eq (self_mem_Gx a)).trans ha)
  have hci : (α a)⁻¹ = α a := inv_eq_of_mul_eq_one_right hc2
  rw [cp_app_conj_a F hr, hci] at h1
  rw [cp_app_conj_a F hr', hci] at h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.symm.trans h2)
  · exact Or.inr (h1.symm.trans h2)
  · refine Or.inr ?_
    have e : F.app r y = α a * (α a * F.app r y * α a) * α a := by
      calc F.app r y = (α a * α a) * F.app r y * (α a * α a) := by rw [hc2]; group
        _ = α a * (α a * F.app r y * α a) * α a := by group
    rw [e, ← h1, h2]
  · refine Or.inl ?_
    have h3 : α a * F.app r y * α a = α a * F.app r' y * α a := h1.symm.trans h2
    exact mul_left_cancel (mul_right_cancel h3)

theorem cp_compat_perp_4A (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) {y : G} (hy : y ∈ orb4A a z a) {d : G} (hd : d ∈ orb2A a a ∩ orb2A a y)
    {r : G} (hr : r ∈ InvIn (Gxyz a d y)) :
    F.app d y = F.app r y ∨ F.app d y = F.app r (a * y * a⁻¹) := by
  by_cases hrd : r = d
  · exact Or.inl (by rw [hrd])
  have hdG : d ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hd.1
  have hdy : d ∈ Gx y := h.mem_Gx_of_orb2A hy.1 hd.2
  have hd2 : orderOf d = 2 := h.orderOf_eq_two (Or.inl hd.1.1)
  have hrz := mem_Gxyz.1 hr.1
  have hnc := cp_not_comm_of_orb4A h hy
  have hda : d ≠ a := by
    intro hda
    apply hnc
    rw [hda] at hdy
    exact (mem_Gx.1 hdy).symm
  have hra : r ≠ a := by
    intro hra
    apply hnc
    rw [hra] at hrz
    exact (mem_Gx.1 hrz.2.2).symm
  have hrad : r ≠ a * d := by
    intro hrad
    apply hnc
    have h1 : y * (a * d) = (a * d) * y := mem_Gx.1 (by rw [← hrad]; exact hrz.2.2)
    have h2 : y * d = d * y := mem_Gx.1 hdy
    have h3 : (y * a) * d = (a * y) * d := by
      calc (y * a) * d = y * (a * d) := by rw [mul_assoc]
        _ = (a * d) * y := h1
        _ = a * (d * y) := by rw [mul_assoc]
        _ = a * (y * d) := by rw [h2]
        _ = (a * y) * d := by rw [mul_assoc]
    exact (mul_right_cancel h3).symm
  have hrGxy : r ∈ InvIn (Gxy a d) := ⟨mem_Gxy.2 ⟨hrz.1, hrz.2.1⟩, hr.2⟩
  have hyGxy : y ∈ Gxy d r :=
    mem_Gxy.2 ⟨mem_Gx.2 (mem_Gx.1 hdy).symm, mem_Gx.2 (mem_Gx.1 hrz.2.2).symm⟩
  rcases compat_three h h' hα F ⟨hdG, hd2⟩ hd.1.1 hda (Or.inl hd.1) hrGxy hra hrd hrad with
    h1 | h1
  · exact Or.inl (h1 y hyGxy)
  · exact Or.inr (h1 y hyGxy)

theorem cp_fam_4A_base (hC : Cover4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) {y : G} (hy : y ∈ orb4A a z a) {t t' : G}
    (ht : t ∈ InvIn (Gxy a y)) (ht' : t' ∈ InvIn (Gxy a y)) :
    (F.app t y = F.app t' y ∨ F.app t y = F.app t' (a * y * a⁻¹)) ∧
      (ConjIn (Gxy a y) t' t → F.app t y = F.app t' y) := by
  obtain ⟨d, hd⟩ := cp_exists_perp_4A h hy
  have hR := cp_isInvReps_4A hC h hy hd
  have ha2 : orderOf a = 2 := h.typ.orderOf_a
  have hagree : ∀ r ∈ InvIn (Gxyz a d y), ∀ r' ∈ InvIn (Gxyz a d y),
      F.app r y = F.app r' y ∨ F.app r y = F.app r' (a * y * a⁻¹) := fun r hr r' hr' =>
    cp_agree_trans F ha2 (hR.subset hr) (hR.subset hr') (cp_compat_perp_4A h h' hα F hy hd hr)
      (cp_compat_perp_4A h h' hα F hy hd hr')
  exact (bookkeep_one F ha2 ⟨1, (Gx a).one_mem, by simp⟩ hR hagree).2 t ht t' ht'

end CFSG.EvenSporadicStandard.HNRecog.Section4
