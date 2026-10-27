module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Bookkeep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Compat3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpArrCls
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCfgS7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpTwist

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

@[expose] def Arranged3A (a : G) (F : Fam a α) : Prop :=
  ∀ x ∈ orb3A a a, ∀ t ∈ InvIn (Gxy a x), ∀ t' ∈ InvIn (Gxy a x), F.app t x = F.app t' x

theorem cp_compat_pt (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) {b t x : G} (hb : b ∈ orb2A a a) (ht : t ∈ InvIn (Gxy a b))
    (htc : IsConj z t ∨ (IsConj a t ∧ IsConj z (a * t))) (hx : x ∈ Gxy b t) :
    F.app b x = F.app t x ∨ F.app b x = F.app t (a * x * a⁻¹) := by
  have hbInv : b ∈ InvIn (Gx a) :=
    ⟨h.mem_Gx_of_orb2A (IsConj.refl a) hb, h.orderOf_eq_two (Or.inl hb.1)⟩
  obtain ⟨hta, htb, htab⟩ := cp_ne_three h hb htc
  rcases compat_three h h' hα F hbInv hb.1 (cp_ne_self_of_orb2A h hb) (Or.inl hb) ht hta htb
      htab with h1 | h1
  · exact Or.inl (h1 x hx)
  · exact Or.inr (h1 x hx)

theorem cp_arrange_3A (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F₀ : Fam a α) : ∃ F : Fam a α, Arranged3A a F := by
  obtain ⟨t₁, t₂, x, ht₁, ht₂, ht₃, hx, hxt⟩ := cp_s7_pair_ABBB h
  have hR := isInvReps_config h ht₁ ht₂ ht₃ hx hxt
  have ht₁G : t₁ ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) ht₁
  have ht₂G : t₂ ∈ Gx a := h.mem_Gx_of_orb2B (IsConj.refl a) ht₂
  have c12 : Commute t₁ t₂ := h.mul_comm (Or.inl ht₁.1) (Or.inl ht₂.1) (Or.inr ht₃.1)
  have ht₂Inv : t₂ ∈ InvIn (Gxy a t₁) :=
    ⟨mem_Gxy.2 ⟨ht₂G, mem_Gx.2 c12⟩, h.orderOf_eq_two (Or.inl ht₂.1)⟩
  have ht₃Inv : t₁ * t₂ ∈ InvIn (Gxy a t₁) :=
    ⟨mem_Gxy.2 ⟨(Gx a).mul_mem ht₁G ht₂G, mem_Gx.2 ((Commute.refl t₁).mul_right c12)⟩,
      h.orderOf_eq_two (Or.inr ht₃.1)⟩
  have hx₂ : x ∈ Gxy t₁ t₂ := hxt
  have cx₁ : Commute t₁ x := mem_Gx.1 (mem_Gxy.1 hxt).1
  have cx₂ : Commute t₂ x := mem_Gx.1 (mem_Gxy.1 hxt).2
  have hx₃ : x ∈ Gxy t₁ (t₁ * t₂) :=
    mem_Gxy.2 ⟨(mem_Gxy.1 hxt).1, mem_Gx.2 (cx₁.mul_left cx₂)⟩
  have ht₁nB : t₁ ∉ orb2B a z a := fun hh => h.not_isConj (ht₁.2.trans hh.2.symm)
  obtain ⟨F₁, hF₁x, hF₁off⟩ := cp_twist_class F₀ (C := orb2B a z a)
    (fun g hg t ht => cp_orb2B_conj hg ht) ht₁nB ht₂
    (cp_compat_pt h h' hα F₀ ht₁ ht₂Inv (Or.inr ⟨ht₂.1, ht₂.2⟩) hx₂)
  have ht₁nBB : t₁ ∉ orb2BB a z a := fun hh => h.not_isConj (ht₁.1.trans hh.1.symm)
  have ht₂nBB : t₂ ∉ orb2BB a z a := fun hh => h.not_isConj (ht₂.1.trans hh.1.symm)
  obtain ⟨F₂, hF₂x, hF₂off⟩ := cp_twist_class F₁ (C := orb2BB a z a)
    (fun g hg t ht => cp_orb2BB_conj hg ht) ht₁nBB ht₃
    (cp_compat_pt h h' hα F₁ ht₁ ht₃Inv (Or.inl ht₃.1) hx₃)
  have e12 : F₂.app t₁ x = F₂.app t₂ x := by
    rw [hF₂off t₁ ht₁nBB x, hF₂off t₂ ht₂nBB x]
    exact hF₁x
  refine ⟨F₂, fun x' hx' t ht t' ht' => ?_⟩
  obtain ⟨k, hk, hkx⟩ := h.loc.s7.self.orbit.transitive x hx x' hx'
  refine bookkeep_two F₂ h.typ.orderOf_a ⟨k, hk, hkx⟩ hR ?_ t ht t' ht'
  rintro r (rfl | rfl | rfl) r' (rfl | rfl | rfl)
  · rfl
  · exact e12
  · exact hF₂x
  · exact e12.symm
  · rfl
  · exact e12.symm.trans hF₂x
  · exact hF₂x.symm
  · exact hF₂x.symm.trans e12
  · rfl

end CFSG.EvenSporadicStandard.HNRecog.Section4
