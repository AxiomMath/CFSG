module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Inv48
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpArrCls
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpClique3

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

theorem cp_orb4A_symm {b y : G} (hbA : IsConj a b) (hy : y ∈ orb4A a z b) : b ∈ orb4A a z y := by
  refine ⟨hbA, ?_⟩
  have e : (y * b) ^ 2 = y * (b * y) ^ 2 * y⁻¹ := by simp only [pow_two]; group
  rw [e]
  exact cp_isConj_conj hy.2 y

theorem cp_alpha_eq (hW : Wit20) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {b t : G} (hb : b ∈ orb2A a a)
    (ht : t ∈ InvIn (Gxy a b)) (htb : t ≠ b) : ∀ w ∈ Gxy b t, F.app b w = F.app t w := by
  have hbG : b ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb
  have hbInv : b ∈ InvIn (Gx a) := ⟨hbG, h.orderOf_eq_two (Or.inl hb.1)⟩
  have htInv : t ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht.1).1, ht.2⟩
  have haInv : a ∈ InvIn (Gx a) := ⟨self_mem_Gx a, h.typ.orderOf_a⟩
  by_cases hta : t = a
  · intro w hw
    obtain ⟨hwb, hwt⟩ := mem_Gxy.1 hw
    rw [hta] at hwt ⊢
    rw [F.restrict b hbInv w (mem_Gxy.2 ⟨hwt, hwb⟩), F.restrict a haInv w (mem_Gxy.2 ⟨hwt, hwt⟩)]
  by_cases htab : t = a * b
  · intro w hw
    obtain ⟨hwb, hwt⟩ := mem_Gxy.1 hw
    have hab : Commute a b := mem_Gx.1 hbG
    have hwa : w ∈ Gx a := by
      have e : a = (a * b) * b⁻¹ := by group
      have c1 : Commute w (a * b) := by rw [htab] at hwt; exact (mem_Gx.1 hwt).symm
      have c2 : Commute w b := (mem_Gx.1 hwb).symm
      rw [mem_Gx]
      have := (c1.mul_right c2.inv_right).eq
      rw [← e] at this
      exact this.symm
    have hab2 : a * b ∈ InvIn (Gx a) :=
      ⟨mem_Gx.2 ((Commute.refl a).mul_right hab).eq, h.orderOf_eq_two (Or.inl hb.2)⟩
    rw [F.restrict b hbInv w (mem_Gxy.2 ⟨hwa, hwb⟩), htab,
      F.restrict (a * b) hab2 w (mem_Gxy.2 ⟨hwa, by rw [htab] at hwt; exact hwt⟩)]
  obtain ⟨w₀, hw₀A, hw₀, hw₀a⟩ := hW h b hb t ht hta htb htab
  have hw₀t : t ∈ Gx w₀ := mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hw₀).2).symm
  have hw₀b : b ∈ Gx w₀ := mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hw₀).1).symm
  have e1 : θ w₀ = F.app t w₀ :=
    hθ.eq_app w₀ hw₀A t ⟨mem_Gxy.2 ⟨htInv.1, hw₀t⟩, ht.2⟩
  have e2 : θ w₀ = F.app b w₀ :=
    hθ.eq_app w₀ hw₀A b ⟨mem_Gxy.2 ⟨hbG, hw₀b⟩, hbInv.2⟩
  have hnot : w₀ ∉ Gxyz a b t := fun hh => hw₀a (mem_Gxyz.1 hh).1
  exact compat_three_eq h h' hα F hbInv hb.1 (cp_ne_self_of_orb2A h hb) (Or.inl hb) ht hta htb htab
    hw₀ hnot (e1.symm.trans e2)

theorem cp_beta_b (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {b : G} (hb : b ∈ orb2A a a) :
    IsConj a' (F.app b b) ∧ IsIsoOn (Gx b) (Gx (F.app b b)) (F.app b) := by
  have hbA : IsConj a b := hb.1
  have hbG : b ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb
  have hb2 : orderOf b = 2 := h.orderOf_eq_two (Or.inl hbA)
  have hbInv : b ∈ InvIn (Gx a) := ⟨hbG, hb2⟩
  have hbb : b ∈ Gxy a b := mem_Gxy.2 ⟨hbG, self_mem_Gx b⟩
  refine ⟨?_, ?_⟩
  · rw [← hθ.eq_app b hbA b ⟨hbb, hb2⟩]
    exact hθ.typed h h' hα hbA
  · rw [F.restrict b hbInv b hbb]
    exact F.iso b hbInv

theorem cp_fig20_family (hC : Cover4A) (hW : Wit20) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {b x y : G} (hb : b ∈ orb2A a a)
    (hx : IsConj a x) (hbx : b ∈ orb2A a x) (hy : y ∈ orb2A a x) (hyb : y ∈ orb4A a z b) :
    ∃ ℬ : Fam b (F.app b), θ y = ℬ.app x y ∨ θ y = ℬ.app x (b * y * b⁻¹) := by
  have hbA : IsConj a b := hb.1
  have hyA : IsConj a y := hy.1
  have hbG : b ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb
  have hb2 : orderOf b = 2 := h.orderOf_eq_two (Or.inl hbA)
  have hbInv : b ∈ InvIn (Gx a) := ⟨hbG, hb2⟩
  have hbb : b ∈ Gxy a b := mem_Gxy.2 ⟨hbG, self_mem_Gx b⟩
  have hab : a ∈ orb2A a b := ⟨IsConj.refl a, (cp_isConj_mul_comm a a b).1 hb.2⟩
  obtain ⟨t, ht2, htG⟩ := h.loc.gamma.self.inv_one y b a hyA hbA
    (h.loc.gamma.self.eq_gamma y b hyA hbA) hab
    (Or.inl (Or.inl (Or.inr (cp_orb4A_symm hbA hyb))))
  obtain ⟨hty, htb, hta⟩ := mem_Gxyz.1 htG
  have hbF : F5Std b z := h.of_isConj hbA (IsConj.refl z)
  have hyb' : y ∈ orb4A b z b := ⟨hbA.symm.trans hyA, hyb.2⟩
  have hncomm : b * y ≠ y * b := cp_not_comm_of_orb4A hbF hyb'
  have htne : t ≠ b := by
    intro hh
    rw [hh] at hty
    exact hncomm (mem_Gx.1 hty).symm
  have htInv : t ∈ InvIn (Gx a) := ⟨hta, ht2⟩
  have htab : t ∈ InvIn (Gxy a b) := ⟨mem_Gxy.2 ⟨hta, htb⟩, ht2⟩
  have hbt := cp_alpha_eq hW h h' hα hθ hb htab htne
  obtain ⟨hb', hβ⟩ := cp_beta_b h h' hα hθ hb
  have hψ : IsIsoOn (Gx t) (Gx (F.app b t)) (F.app t) := by
    rw [F.restrict b hbInv t htab.1]
    exact F.iso t htInv
  obtain ⟨ℬ, hℬ⟩ := exists_fam_extending h h' hbA hb' hβ ⟨htb, ht2⟩ hψ
    (fun w hw => (hbt w hw).symm)
  refine ⟨ℬ, ?_⟩
  have hyt : y ∈ Gx t := mem_Gx.2 (mem_Gx.1 hty).symm
  have hθy : θ y = ℬ.app t y := by
    rw [hℬ y hyt]
    exact hθ.eq_app y hyA t ⟨mem_Gxy.2 ⟨hta, hty⟩, ht2⟩
  have hxb : x ∈ Gx b := mem_Gx.2 (mem_Gx.1 (h.mem_Gx_of_orb2A hx hbx)).symm
  have hxy : x ∈ Gx y := mem_Gx.2 (mem_Gx.1 (h.mem_Gx_of_orb2A hx hy)).symm
  have hx2 : orderOf x = 2 := h.orderOf_eq_two (Or.inl hx)
  have h48 := (fam_4A hC h h' hbA hb' hβ ℬ hyb ⟨mem_Gxy.2 ⟨htb, hty⟩, ht2⟩
    ⟨mem_Gxy.2 ⟨hxb, hxy⟩, hx2⟩).1
  rwa [← hθy] at h48

end CFSG.EvenSporadicStandard.HNRecog.Section4
