module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Const4A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpGen5E

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem cp_ne_self_of_orb2B (h : F5Std a z) {b : G} (hb : b ∈ orb2B a z a) : b ≠ a := by
  intro hba
  have h1 : IsConj z 1 := by
    have h2 := hb.2
    rwa [hba, cp_mul_self_eq_one h (Or.inl (IsConj.refl a))] at h2
  have h3 : z = 1 := isConj_one_left.1 h1
  have h4 := h.typ.orderOf_z
  rw [h3, orderOf_one] at h4
  exact absurd h4 (by norm_num)

theorem cp_eq_2B_pair (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) (hF : Arranged a F) {s s' : G} (hs : s ∈ orb2B a z a) (hs' : s' ∈ orb2B a z a)
    (hss : s * s' ∈ orb2B a z a) (hne : s ≠ s') (hcomm : s * s' = s' * s) :
    ∀ w ∈ Gxy s s', F.app s w = F.app s' w := by
  obtain ⟨y, hy3A, hyG⟩ := config_BBB h hs hs' hss
  have hsG : s ∈ Gx a := h.mem_Gx_of_orb2B (IsConj.refl a) hs
  have hs'G : s' ∈ Gx a := h.mem_Gx_of_orb2B (IsConj.refl a) hs'
  have hsInv : s ∈ InvIn (Gx a) := ⟨hsG, h.orderOf_eq_two (Or.inl hs.1)⟩
  have hs'Inv : s' ∈ InvIn (Gxy a s) :=
    ⟨mem_Gxy.2 ⟨hs'G, mem_Gx.2 hcomm⟩, h.orderOf_eq_two (Or.inl hs'.1)⟩
  have hsInvY : s ∈ InvIn (Gxy a y) :=
    ⟨mem_Gxy.2 ⟨hsG, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hyG).1).symm⟩, hsInv.2⟩
  have hs'InvY : s' ∈ InvIn (Gxy a y) :=
    ⟨mem_Gxy.2 ⟨hs'G, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hyG).2).symm⟩, hs'Inv.2⟩
  have hxe : F.app s' y = F.app s y := hF y (Or.inl hy3A) s' hs'InvY s hsInvY
  have hne_a : s' ≠ s ∧ s' ≠ a ∧ s' ≠ a * s := by
    refine ⟨hne.symm, cp_ne_self_of_orb2B h hs', ?_⟩
    intro hsa
    have h2 : IsConj z (a * s') := hs'.2
    have haa : a * a = 1 := cp_mul_self_eq_one h (Or.inl (IsConj.refl a))
    rw [hsa, ← mul_assoc, haa, one_mul] at h2
    exact h.not_isConj (hs.1.trans h2.symm)
  have hy' : y ∉ Gxyz a s s' := fun hh => cp_not_comm_of_orb3A h hy3A (mem_Gx.1 (mem_Gxyz.1 hh).1)
  exact compat_three_eq h h' hα F hsInv hs.1 (cp_ne_self_of_orb2B h hs) (Or.inr ⟨hs'.1, hss.1⟩)
    hs'Inv hne_a.2.1 hne_a.1 hne_a.2.2 hyG hy' hxe

theorem cp_isInvReps_5A (h : F5Std a z) {x s s' : G} (hx : x ∈ orb5A a a)
    (hs : s ∈ InvIn (Gxy a x)) (hs' : s' ∈ InvIn (Gxy a x))
    (hgen : Subgroup.closure ((Gxyz a s x : Set G) ∪ (Gxyz a s' x : Set G)) = Gxy a x) :
    IsInvReps a x {s, s'} := by
  refine ⟨?_, fun u hu => ⟨s, Set.mem_insert _ _,
    (h.loc.lines.self.five_A x hx).1.transitive s hs u hu⟩, ?_⟩
  · rintro u (rfl | rfl)
    exacts [hs, hs']
  · rw [Set.biUnion_insert, Set.biUnion_singleton]
    exact hgen

theorem cp_isInvReps_5E (h : F5Std a z) {x t t' : G} (hx : x ∈ orb5E a a) (ht : IsConj a t)
    (ht' : IsConj z t') (htt : IsConj z (t * t')) (htx : t ∈ Gxy a x) (ht'x : t' ∈ Gxy a x)
    (hcomm : t * t' = t' * t) : IsInvReps a x {t, t', t * t'} := by
  have htInv : t ∈ InvIn (Gxy a x) := ⟨htx, h.orderOf_eq_two (Or.inl ht)⟩
  have ht'Inv : t' ∈ InvIn (Gxy a x) := ⟨ht'x, h.orderOf_eq_two (Or.inr ht')⟩
  have httInv : t * t' ∈ InvIn (Gxy a x) :=
    ⟨(Gxy a x).mul_mem htx ht'x, h.orderOf_eq_two (Or.inr htt)⟩
  have hne : t ≠ t' := fun he => h.not_isConj ((he ▸ ht).trans ht'.symm)
  have hcov := cp_five_E_cover h hx htInv ht'Inv hcomm hne
  have hgen := cp_five_E_gen h hx htInv ht'Inv hcomm hne
  refine ⟨?_, ?_, ?_⟩
  · rintro u (rfl | rfl | rfl)
    exacts [htInv, ht'Inv, httInv]
  · intro u hu
    rcases hcov u hu with h1 | h1 | h1
    · exact ⟨t, by simp, h1⟩
    · exact ⟨t', by simp, h1⟩
    · exact ⟨t * t', by simp, h1⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨r, -, hgr⟩ := Set.mem_iUnion₂.mp hg
      exact mem_Gxy.mpr ⟨(mem_Gxyz.mp hgr).1, (mem_Gxyz.mp hgr).2.2⟩
    · refine hgen.trans (Subgroup.closure_mono ?_)
      intro g hg
      rcases hg with (hg | hg) | hg
      · exact Set.mem_iUnion₂_of_mem (by simp : t ∈ ({t, t', t * t'} : Set G)) hg
      · exact Set.mem_iUnion₂_of_mem (by simp : t' ∈ ({t, t', t * t'} : Set G)) hg
      · exact Set.mem_iUnion₂_of_mem (by simp : t * t' ∈ ({t, t', t * t'} : Set G)) hg

theorem cp_isConj_of_five_A (h : F5Std a z) {y : G} (hy : y ∈ orb5A a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) : IsConj a t := by
  have h1 : t ∈ {u | u ∈ Gxy a y ∧ orderOf u = 2} := ht
  rw [(h.loc.lines.self.five_A y hy).2] at h1
  exact h1.1.1

theorem cp_const_vertex (hC : Cover4A) (hW4 : Wit4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (hF : Arranged a F) {y : G} (hy : IsConj a y)
    (h5A : y ∉ orb5A a a) (h5E : y ∉ orb5E a a) {t t' : G} (ht : t ∈ InvIn (Gxy a y))
    (ht' : t' ∈ InvIn (Gxy a y)) : F.app t y = F.app t' y := by
  have hmem : y ∈ gammaSet a z a := h.loc.gamma.self.eq_gamma a y (IsConj.refl a) hy
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hmem
  rcases hmem with
    (((((((hya | hy2A) | hy2B) | hy3A) | hy4A) | hy4B) | hy5A) | hy5E) | hy6A
  · rw [hya] at ht ht' ⊢
    exact const_self F ht ht'
  · exact const_2A_2B h F (Or.inl hy2A) ht ht'
  · exact const_2A_2B h F (Or.inr hy2B) ht ht'
  · exact hF y (Or.inl hy3A) t ht t' ht'
  · exact const_4A hC hW4 h h' hα F hF hy4A ht ht'
  · exact hF y (Or.inr hy4B) t ht t' ht'
  · exact (h5A hy5A).elim
  · exact (h5E hy5E).elim
  · exact const_6A h F hF hy6A ht ht'

theorem cp_5E_pair (hC : Cover4A) (hW4 : Wit4A) (hW : Wit5E) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (hF : Arranged a F) {x : G}
    (hx : x ∈ orb5E a a) {t t' : G} (ht : IsConj a t) (ht' : IsConj z t') (htt : IsConj z (t * t'))
    (htx : t ∈ Gxy a x) (ht'x : t' ∈ Gxy a x) (hcomm : t * t' = t' * t) :
    F.app t x = F.app t' x := by
  have hclos := hW h x hx t t' ht ht' htt htx ht'x hcomm
  have htInv : t ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 htx).1, h.orderOf_eq_two (Or.inl ht)⟩
  have ht'Inv : t' ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht'x).1, h.orderOf_eq_two (Or.inr ht')⟩
  have htt' : t' ∈ Gx t := mem_Gx.2 hcomm
  have ht't : t ∈ Gx t' := mem_Gx.2 hcomm.symm
  have hf : IsIsoOn (Gxy t t') (Gx (α t) ⊓ Gx (F.app t t')) (F.app t) := by
    have := (F.iso t htInv).restrict_cent htt'
    rwa [Gxy_eq_inf]
  have hg : IsIsoOn (Gxy t t') (Gx (α t') ⊓ Gx (F.app t' t)) (F.app t') := by
    have := (F.iso t' ht'Inv).restrict_cent ht't
    have e : Gxy t t' = Gx t' ⊓ Gx t := by rw [Gxy_eq_inf, inf_comm]
    rwa [e]
  refine IsIsoOn.agree_on_closure hf hg (fun y hy => hy.1) (fun y hy => ?_) x hclos
  obtain ⟨hyK, hya, hy5E⟩ := hy
  have hytt : y ∈ Gx t ∧ y ∈ Gx t' := mem_Gxy.1 hyK
  have htY : t ∈ InvIn (Gxy a y) :=
    ⟨mem_Gxy.2 ⟨htInv.1, mem_Gx.2 (mem_Gx.1 hytt.1).symm⟩, htInv.2⟩
  have ht'Y : t' ∈ InvIn (Gxy a y) :=
    ⟨mem_Gxy.2 ⟨ht'Inv.1, mem_Gx.2 (mem_Gx.1 hytt.2).symm⟩, ht'Inv.2⟩
  have h5A : y ∉ orb5A a a := fun hy5A =>
    h.not_isConj ((cp_isConj_of_five_A h hy5A ht'Y).trans ht'.symm)
  exact cp_const_vertex hC hW4 h h' hα F hF hya h5A hy5E htY ht'Y

end CFSG.EvenSporadicStandard.HNRecog.Section4
