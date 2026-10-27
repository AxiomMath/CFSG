module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpConst5

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem const_5A (hG : Gen5A) (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) (hF : Arranged a F) {x : G} (hx : x ∈ orb5A a a) {t t' : G}
    (ht : t ∈ InvIn (Gxy a x)) (ht' : t' ∈ InvIn (Gxy a x)) : F.app t x = F.app t' x := by
  obtain ⟨s, s', hs, hs', hne, hcomm, hgen⟩ := hG h x hx
  have hfive := h.loc.lines.self.five_A x hx
  have hB : ∀ u ∈ InvIn (Gxy a x), u ∈ orb2B a z a := fun u hu => by
    have h1 : u ∈ {v | v ∈ Gxy a x ∧ orderOf v = 2} := hu
    rw [hfive.2] at h1
    exact h1.1
  have hss : s * s' ∈ InvIn (Gxy a x) := by
    refine ⟨(Gxy a x).mul_mem hs.1 hs'.1, ?_⟩
    have hs2 : s ^ 2 = 1 := by simpa [hs.2] using pow_orderOf_eq_one s
    have hs'2 : s' ^ 2 = 1 := by simpa [hs'.2] using pow_orderOf_eq_one s'
    have hc : Commute s s' := hcomm
    refine orderOf_eq_prime (by rw [hc.mul_pow, hs2, hs'2, one_mul]) ?_
    intro h1
    apply hne
    have e : s * s = 1 := by rw [← pow_two]; exact hs2
    exact (mul_left_cancel (h1.trans e.symm)).symm
  have hxss : x ∈ Gxy s s' :=
    mem_Gxy.2 ⟨mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hs.1).2).symm,
      mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hs'.1).2).symm⟩
  have e := cp_eq_2B_pair h h' hα F hF (hB s hs) (hB s' hs') (hB _ hss) hne hcomm x hxss
  exact bookkeep_two F h.typ.orderOf_a ⟨1, (Gx a).one_mem, by simp⟩
    (cp_isInvReps_5A h hx hs hs' hgen)
    (by rintro r (rfl | rfl) r' (rfl | rfl); exacts [rfl, e, e.symm, rfl]) t ht t' ht'

theorem const_5E (hC : Cover4A) (hW4 : Wit4A) (hW : Wit5E) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (hF : Arranged a F) {x : G}
    (hx : x ∈ orb5E a a) {t t' : G} (ht : t ∈ InvIn (Gxy a x)) (ht' : t' ∈ InvIn (Gxy a x)) :
    F.app t x = F.app t' x := by
  obtain ⟨t₀, t₀', h0, h0', h00', h0x, h0'x, hcomm⟩ := h.loc.five.self.klein_E x hx
  have hb0 : t₀ * t₀ = 1 := cp_mul_self_eq_one h (Or.inl h0)
  have c12 : Commute t₀ t₀' := hcomm
  have e1 : F.app t₀ x = F.app t₀' x :=
    cp_5E_pair hC hW4 hW h h' hα F hF hx h0 h0' h00' h0x h0'x hcomm
  have hprod : t₀ * (t₀ * t₀') = t₀' := by rw [← mul_assoc, hb0, one_mul]
  have e2 : F.app t₀ x = F.app (t₀ * t₀') x :=
    cp_5E_pair hC hW4 hW h h' hα F hF hx h0 (t' := t₀ * t₀') h00' (by rw [hprod]; exact h0')
      h0x ((Gxy a x).mul_mem h0x h0'x) ((Commute.refl t₀).mul_right c12).eq
  exact bookkeep_two F h.typ.orderOf_a ⟨1, (Gx a).one_mem, by simp⟩
    (cp_isInvReps_5E h hx h0 h0' h00' h0x h0'x hcomm)
    (by
      rintro r (rfl | rfl | rfl) r' (rfl | rfl | rfl)
      exacts [rfl, e1, e2, e1.symm, rfl, e1.symm.trans e2, e2.symm, e2.symm.trans e1, rfl])
    t ht t' ht'

end CFSG.EvenSporadicStandard.HNRecog.Section4
