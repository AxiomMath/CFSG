module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Configs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpArr3A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFourA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

@[expose] def Arranged4B (a : G) (F : Fam a α) : Prop :=
  ∀ x ∈ orb4B a a, ∀ t ∈ InvIn (Gxy a x), ∀ t' ∈ InvIn (Gxy a x), F.app t x = F.app t' x

theorem cp_eq_of_compat (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) {b t c : G} (hb : b ∈ orb2A a a) (ht : t ∈ InvIn (Gxy a b))
    (hne : t ≠ a ∧ t ≠ b ∧ t ≠ a * b) (hc : c ∈ Gxy b t) (hca : a * c ≠ c * a)
    (hec : F.app t c = F.app b c) : ∀ y ∈ Gxy b t, F.app b y = F.app t y := by
  have hbInv : b ∈ InvIn (Gx a) :=
    ⟨h.mem_Gx_of_orb2A (IsConj.refl a) hb, h.orderOf_eq_two (Or.inl hb.1)⟩
  refine compat_three_eq h h' hα F hbInv hb.1 (cp_ne_self_of_orb2A h hb) (Or.inl hb) ht hne.1
    hne.2.1 hne.2.2 hc ?_ hec
  intro hcz
  exact hca (mem_Gx.1 (mem_Gxyz.1 hcz).1)

theorem cp_4B_mem (h : F5Std a z) {y t : G} (hy : y ∈ orb4B a a) (ht : t ∈ Gxy a y) :
    t ∈ Gxy a ((a * y) ^ 2) ∧ y ∈ Gxy ((a * y) ^ 2) t := by
  have hbGy : (a * y) ^ 2 ∈ Gx y :=
    (mem_Gxy.1 (cp_central_inv h hy.1 (k := 2) (Or.inl hy.2)).1.1).2
  refine ⟨mem_Gxy.2 ⟨(mem_Gxy.1 ht).1, mem_Gx.2 (cp_commute_sq_of_mem_Gxy ht).eq.symm⟩,
    mem_Gxy.2 ⟨mem_Gx.2 (mem_Gx.1 hbGy).symm, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 ht).2).symm⟩⟩

theorem cp_4B_two_A (hC : Cover4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) {y : G} (hy : y ∈ orb4B a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) (ht2A : t ∈ orb2A a a) (htb : t ≠ (a * y) ^ 2)
    (hbt : (a * y) ^ 2 * t ∈ orb2AB a z a) : F.app t y = F.app ((a * y) ^ 2) y := by
  have hb : (a * y) ^ 2 ∈ orb2A a a := cp_sq_mem_orb2A h hy
  obtain ⟨c, hc4A, hcbt, hbc, htc, -⟩ := (config_AAAB h hb ht2A hbt).2
  obtain ⟨htGab, hyG⟩ := cp_4B_mem h hy ht.1
  have hbG : (a * y) ^ 2 ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb
  have htG : t ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) ht2A
  have hbc' : (a * y) ^ 2 ∈ InvIn (Gxy a c) :=
    ⟨mem_Gxy.2 ⟨hbG, h.mem_Gx_of_orb2A hc4A.1 hbc⟩, h.orderOf_eq_two (Or.inl hb.1)⟩
  have htc' : t ∈ InvIn (Gxy a c) := ⟨mem_Gxy.2 ⟨htG, h.mem_Gx_of_orb2A hc4A.1 htc⟩, ht.2⟩
  have hconj : ConjIn (Gxy a c) ((a * y) ^ 2) t :=
    (cp_class_perp_4A h hc4A).transitive _ ⟨hb, hbc⟩ t ⟨ht2A, htc⟩
  have hct : F.app t c = F.app ((a * y) ^ 2) c :=
    (cp_fam_4A_base hC h h' hα F hc4A htc' hbc').2 hconj
  have hbb : (a * y) ^ 2 * (a * y) ^ 2 = 1 := cp_mul_self_eq_one h (Or.inl hb.1)
  have hne : t ≠ a * (a * y) ^ 2 := by
    intro hta
    have h1 : (a * y) ^ 2 * (a * (a * y) ^ 2) = a := by
      calc (a * y) ^ 2 * (a * (a * y) ^ 2) = ((a * y) ^ 2 * a) * (a * y) ^ 2 := by
            rw [← mul_assoc]
        _ = (a * (a * y) ^ 2) * (a * y) ^ 2 := by rw [← mem_Gx.1 hbG]
        _ = a * ((a * y) ^ 2 * (a * y) ^ 2) := by rw [mul_assoc]
        _ = a := by rw [hbb, mul_one]
    have h2 : IsConj z ((a * y) ^ 2 * t) := hbt.1
    rw [hta, h1] at h2
    exact h.not_isConj h2.symm
  exact (cp_eq_of_compat h h' hα F hb ⟨htGab, ht.2⟩ ⟨cp_ne_self_of_orb2A h ht2A, htb, hne⟩ hcbt
    (cp_not_comm_of_orb4A h hc4A) hct y hyG).symm

theorem cp_4B_via_3A (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) (h3 : Arranged3A a F) {y : G} (hy : y ∈ orb4B a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) (hne : t ≠ a ∧ t ≠ (a * y) ^ 2 ∧ t ≠ a * (a * y) ^ 2) {c : G}
    (hc3A : c ∈ orb3A a a) (hcbt : c ∈ Gxy ((a * y) ^ 2) t) :
    F.app t y = F.app ((a * y) ^ 2) y := by
  have hb : (a * y) ^ 2 ∈ orb2A a a := cp_sq_mem_orb2A h hy
  obtain ⟨htGab, hyG⟩ := cp_4B_mem h hy ht.1
  have hbc' : (a * y) ^ 2 ∈ InvIn (Gxy a c) :=
    ⟨mem_Gxy.2 ⟨h.mem_Gx_of_orb2A (IsConj.refl a) hb,
      mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hcbt).1).symm⟩, h.orderOf_eq_two (Or.inl hb.1)⟩
  have htc' : t ∈ InvIn (Gxy a c) :=
    ⟨mem_Gxy.2 ⟨(mem_Gxy.1 ht.1).1, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hcbt).2).symm⟩, ht.2⟩
  exact (cp_eq_of_compat h h' hα F hb ⟨htGab, ht.2⟩ hne hcbt (cp_not_comm_of_orb3A h hc3A)
    (h3 c hc3A t htc' _ hbc') y hyG).symm

theorem cp_4B_two_B (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) (h3 : Arranged3A a F) {y : G} (hy : y ∈ orb4B a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) (ht2B : t ∈ orb2B a z a)
    (hbt : (a * y) ^ 2 * t ∈ orb2BB a z a) : F.app t y = F.app ((a * y) ^ 2) y := by
  have hb : (a * y) ^ 2 ∈ orb2A a a := cp_sq_mem_orb2A h hy
  obtain ⟨c, hc3A, hcbt⟩ := config_ABBB h hb ht2B hbt
  exact cp_4B_via_3A h h' hα F h3 hy ht (cp_ne_three h hb (Or.inr ⟨ht2B.1, ht2B.2⟩)) hc3A hcbt

theorem cp_4B_two_BB (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) (h3 : Arranged3A a F) {y : G} (hy : y ∈ orb4B a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) (ht2BB : t ∈ orb2BB a z a)
    (hbt : (a * y) ^ 2 * t ∈ orb2B a z a) : F.app t y = F.app ((a * y) ^ 2) y := by
  have hb : (a * y) ^ 2 ∈ orb2A a a := cp_sq_mem_orb2A h hy
  have hbb : (a * y) ^ 2 * (a * y) ^ 2 = 1 := cp_mul_self_eq_one h (Or.inl hb.1)
  have hprod : (a * y) ^ 2 * ((a * y) ^ 2 * t) = t := by rw [← mul_assoc, hbb, one_mul]
  have hbt' : (a * y) ^ 2 * ((a * y) ^ 2 * t) ∈ orb2BB a z a := by rw [hprod]; exact ht2BB
  obtain ⟨c, hc3A, hcbt⟩ := config_ABBB h hb hbt hbt'
  have c1 : Commute ((a * y) ^ 2) c := mem_Gx.1 (mem_Gxy.1 hcbt).1
  have c2 : Commute ((a * y) ^ 2 * t) c := mem_Gx.1 (mem_Gxy.1 hcbt).2
  have c3 : Commute ((a * y) ^ 2 * ((a * y) ^ 2 * t)) c := c1.mul_left c2
  rw [hprod] at c3
  exact cp_4B_via_3A h h' hα F h3 hy ht (cp_ne_three h hb (Or.inl ht2BB.1)) hc3A
    (mem_Gxy.2 ⟨(mem_Gxy.1 hcbt).1, mem_Gx.2 c3⟩)

theorem cp_4B_const_nonAB (hC : Cover4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (h3 : Arranged3A a F) {y : G}
    (hy : y ∈ orb4B a a) {t : G} (ht : t ∈ InvIn (Gxy a y)) (htAB : t ∉ orb2AB a z a) :
    F.app t y = F.app ((a * y) ^ 2) y := by
  rcases cp_4B_cases h hy ht with h1 | ⟨h1, h2, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · rw [h1]
  · exact cp_4B_two_A hC h h' hα F hy ht h1 h2 h4
  · exact cp_4B_two_B h h' hα F h3 hy ht h1 h2
  · exact cp_4B_two_BB h h' hα F h3 hy ht h1 h2
  · exact absurd h1.1 htAB

theorem cp_4B_AB_mem (h : F5Std a z) {y : G} (hy : y ∈ orb4B a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) (htAB : t ∈ orb2AB a z a) : t ∈ orb2AB a z a ∩ orb2BB a z y := by
  rcases cp_4B_cases h hy ht with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | h1
  · exfalso
    rw [h1] at htAB
    exact h.not_isConj ((cp_sq_mem_orb2A h hy).1.trans htAB.1.symm)
  · exact absurd (h.not_isConj (h1.1.trans htAB.1.symm)) id
  · exact absurd (h.not_isConj (h1.1.trans htAB.1.symm)) id
  · exact absurd (h.not_isConj (htAB.2.trans h1.2.symm)) id
  · exact h1

theorem cp_isInvReps_4B (h : F5Std a z) {y : G} (hy : y ∈ orb4B a a) :
    IsInvReps a y (InvIn (Gxy a y)) := by
  refine ⟨fun t ht => ht, fun t ht => ⟨t, ht, ⟨1, Subgroup.one_mem _, by simp [ConjIn]⟩⟩, ?_⟩
  obtain ⟨hcinv, hceq⟩ := cp_central_inv h hy.1 (k := 2) (Or.inl hy.2)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨r, -, hgr⟩ := Set.mem_iUnion₂.mp hg
    exact mem_Gxy.mpr ⟨(mem_Gxyz.mp hgr).1, (mem_Gxyz.mp hgr).2.2⟩
  · intro g hg
    have hg' : g ∈ Gxyz a ((a * y) ^ 2) y := by rw [hceq]; exact hg
    exact Subgroup.subset_closure (Set.mem_iUnion₂_of_mem hcinv hg')

theorem cp_twist_AB (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) {y : G} (hy : y ∈ orb4B a a) :
    ∃ F' : Fam a α, (∀ t ∉ orb2AB a z a, ∀ u, F'.app t u = F.app t u) ∧
      ∀ t ∈ InvIn (Gxy a y), t ∈ orb2AB a z a → F'.app t y = F'.app ((a * y) ^ 2) y := by
  have hb : (a * y) ^ 2 ∈ orb2A a a := cp_sq_mem_orb2A h hy
  have hbInv : (a * y) ^ 2 ∈ InvIn (Gx a) :=
    ⟨h.mem_Gx_of_orb2A (IsConj.refl a) hb, h.orderOf_eq_two (Or.inl hb.1)⟩
  have hcl := h.loc.fourB.self.classes y hy
  obtain ⟨t₀, ht₀⟩ := (hcl.orbit 4).nonempty
  have ht₀' : t₀ ∈ orb2AB a z a ∩ orb2BB a z y := ht₀
  have ht₀Inv : t₀ ∈ InvIn (Gxy a y) := hcl.subset 4 ht₀
  obtain ⟨ht₀ab, hyG⟩ := cp_4B_mem h hy ht₀Inv.1
  have hpair := cp_compat_pt h h' hα F hb ⟨ht₀ab, ht₀Inv.2⟩ (Or.inl ht₀'.1.1) hyG
  have hbC : (a * y) ^ 2 ∉ orb2AB a z a := fun hh => h.not_isConj (hb.1.trans hh.1.symm)
  obtain ⟨F', hF'eq, hF'off⟩ := cp_twist_class F (C := orb2AB a z a)
    (fun g hg t ht => cp_orb2AB_conj hg ht) hbC ht₀'.1 hpair
  refine ⟨F', fun t ht u => hF'off t ht u, fun t ht htAB => ?_⟩
  obtain ⟨k, hk, hkeq⟩ := (hcl.orbit 4).transitive t₀ ht₀' t (cp_4B_AB_mem h hy ht htAB)
  have hle : ∀ g ∈ Gxy a y, α g ∈ Gx (F'.app t₀ y) := by
    intro g hg
    rw [← hF'eq]
    have hgb : g ∈ Gxy a ((a * y) ^ 2) := (cp_4B_mem h hy hg).1
    rw [← F'.restrict _ hbInv g hgb]
    have hyb : y ∈ Gx ((a * y) ^ 2) := (mem_Gxy.1 hyG).1
    have hgb' : g ∈ Gx ((a * y) ^ 2) := (mem_Gxy.1 hgb).2
    have hmul1 := (F'.iso _ hbInv).map_mul g hgb' y hyb
    have hmul2 := (F'.iso _ hbInv).map_mul y hyb g hgb'
    rw [mem_Gx.1 (mem_Gxy.1 hg).2] at hmul2
    exact mem_Gx.2 (hmul2.symm.trans hmul1)
  exact (F'.conj_vals_eq ht ht₀Inv ⟨k, hk, hkeq⟩ hle).trans hF'eq.symm

theorem cp_arrange_4B (hC : Cover4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (h3 : Arranged3A a F) :
    ∃ F' : Fam a α, Arranged3A a F' ∧ Arranged4B a F' := by
  have horb : IsConjOrbit (Gx a) (orb4B a a) := h.loc.tableV.self.partition.orbit 3
  obtain ⟨y₀, hy₀⟩ := horb.nonempty
  obtain ⟨F', hoff, hAB⟩ := cp_twist_AB h h' hα F hy₀
  have hb : (a * y₀) ^ 2 ∈ orb2A a a := cp_sq_mem_orb2A h hy₀
  have hbC : (a * y₀) ^ 2 ∉ orb2AB a z a := fun hh => h.not_isConj (hb.1.trans hh.1.symm)
  have hall : ∀ t ∈ InvIn (Gxy a y₀), F'.app t y₀ = F'.app ((a * y₀) ^ 2) y₀ := by
    intro t ht
    by_cases htAB : t ∈ orb2AB a z a
    · exact hAB t ht htAB
    · rw [hoff t htAB y₀, hoff _ hbC y₀]
      exact cp_4B_const_nonAB hC h h' hα F h3 hy₀ ht htAB
  refine ⟨F', fun x hx t ht t' ht' => ?_, fun x hx t ht t' ht' => ?_⟩
  · rw [hoff t (cp_3A_not_AB h hx ht) x, hoff t' (cp_3A_not_AB h hx ht') x]
    exact h3 x hx t ht t' ht'
  · obtain ⟨k, hk, hkx⟩ := horb.transitive y₀ hy₀ x hx
    exact bookkeep_two F' h.typ.orderOf_a ⟨k, hk, hkx⟩ (cp_isInvReps_4B h hy₀)
      (fun r hr r' hr' => (hall r hr).trans (hall r' hr').symm) t ht t' ht'

end CFSG.EvenSporadicStandard.HNRecog.Section4
