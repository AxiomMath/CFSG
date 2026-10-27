module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.ConstLow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem cp_vertex_346 (h : F5Std a z) {y : G} (hy : IsConj a y) (hyG : y ∉ Gx a)
    (h4 : y ∉ orb4A a z a) (h5A : y ∉ orb5A a a) (h5E : y ∉ orb5E a a) :
    y ∈ orb3A a a ∨ y ∈ orb4B a a ∨ y ∈ orb6A a a := by
  have hmem : y ∈ gammaSet a z a := h.loc.gamma.self.eq_gamma a y (IsConj.refl a) hy
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hmem
  rcases hmem with
    (((((((hya | hy2A) | hy2B) | hy3A) | hy4A) | hy4B) | hy5A) | hy5E) | hy6A
  · exact (hyG (by rw [hya]; exact self_mem_Gx a)).elim
  · exact (hyG (h.mem_Gx_of_orb2A (IsConj.refl a) hy2A)).elim
  · exact (hyG (h.mem_Gx_of_orb2B (IsConj.refl a) hy2B)).elim
  · exact Or.inl hy3A
  · exact (h4 hy4A).elim
  · exact Or.inr (Or.inl hy4B)
  · exact (h5A hy5A).elim
  · exact (h5E hy5E).elim
  · exact Or.inr (Or.inr hy6A)

theorem cp_const_346 (h : F5Std a z) (F : Fam a α) (hF : Arranged a F) {y : G}
    (hy : y ∈ orb3A a a ∨ y ∈ orb4B a a ∨ y ∈ orb6A a a) {t t' : G} (ht : t ∈ InvIn (Gxy a y))
    (ht' : t' ∈ InvIn (Gxy a y)) : F.app t y = F.app t' y := by
  rcases hy with hy | hy | hy
  · exact hF y (Or.inl hy) t ht t' ht'
  · exact hF y (Or.inr hy) t ht t' ht'
  · exact const_6A h F hF hy ht ht'

theorem cp_4A_step (hW : Wit4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (hF : Arranged a F) {x : G}
    (hx : x ∈ orb4A a z a) {d : G} (hd : d ∈ orb2A a a ∩ orb2A a x) {r : G}
    (hr : r ∈ InvIn (Gxyz a d x)) : F.app r x = F.app d x := by
  by_cases hrd : r = d
  · rw [hrd]
  obtain ⟨y, hyG, hya, hyna, hy4A, hy5A, hy5E⟩ := hW h x hx d hd r hr hrd
  have hy346 := cp_vertex_346 h hya hyna hy4A hy5A hy5E
  obtain ⟨hra, hrd', hrx⟩ := mem_Gxyz.1 hr.1
  have hdA : d ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hd.1
  have hdx : d ∈ Gx x := h.mem_Gx_of_orb2A hx.1 hd.2
  obtain ⟨hyr, hyd⟩ := mem_Gxy.1 hyG
  have hrInvY : r ∈ InvIn (Gxy a y) :=
    ⟨mem_Gxy.2 ⟨hra, mem_Gx.2 (mem_Gx.1 hyr).symm⟩, hr.2⟩
  have hdInvY : d ∈ InvIn (Gxy a y) :=
    ⟨mem_Gxy.2 ⟨hdA, mem_Gx.2 (mem_Gx.1 hyd).symm⟩, h.orderOf_eq_two (Or.inl hd.1.1)⟩
  have hconst : F.app r y = F.app d y := cp_const_346 h F hF hy346 hrInvY hdInvY
  have hax : a * x ≠ x * a := cp_not_comm_of_orb4A h hx
  have hne_a : r ≠ a := by
    intro hra'
    rw [hra'] at hrx
    exact hax (mem_Gx.1 hrx).symm
  have hne_ad : r ≠ a * d := by
    intro hrad
    rw [hrad] at hrx
    apply hax
    have e1 : x * (a * d) = (a * d) * x := mem_Gx.1 hrx
    have e2 : x * d = d * x := mem_Gx.1 hdx
    have e3 : x * a * d = a * x * d := by
      calc x * a * d = x * (a * d) := mul_assoc _ _ _
        _ = (a * d) * x := e1
        _ = a * (d * x) := mul_assoc _ _ _
        _ = a * (x * d) := by rw [e2]
        _ = a * x * d := (mul_assoc _ _ _).symm
    exact (mul_right_cancel e3).symm
  have hdInv : d ∈ InvIn (Gx a) := ⟨hdA, h.orderOf_eq_two (Or.inl hd.1.1)⟩
  have hrInv : r ∈ InvIn (Gxy a d) := ⟨mem_Gxy.2 ⟨hra, hrd'⟩, hr.2⟩
  have hyGdr : y ∈ Gxy d r := mem_Gxy.2 ⟨hyd, hyr⟩
  have hxGdr : x ∈ Gxy d r :=
    mem_Gxy.2 ⟨mem_Gx.2 (mem_Gx.1 hdx).symm, mem_Gx.2 (mem_Gx.1 hrx).symm⟩
  have hyna' : y ∉ Gxyz a d r := fun hh => hyna (mem_Gxyz.1 hh).1
  exact (compat_three_eq h h' hα F hdInv hd.1.1 (cp_ne_self_of_orb2A h hd.1) (Or.inl hd.1) hrInv
    hne_a hrd hne_ad hyGdr hyna' hconst x hxGdr).symm

end CFSG.EvenSporadicStandard.HNRecog.Section4
