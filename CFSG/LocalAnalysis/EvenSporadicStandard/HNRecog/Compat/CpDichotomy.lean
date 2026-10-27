module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.AutXCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.AutA8Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.AutYCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.InvCover

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G}

private theorem Gx_inf_mul_self {H : Type} [Group H] {x t : H} (hx2 : x * x = 1) :
    Gx x ⊓ Gx (x * t) = Gx x ⊓ Gx t := by
  have ht_eq : x * (x * t) = t := by rw [← mul_assoc, hx2, one_mul]
  ext g
  simp only [Subgroup.mem_inf, mem_Gx]
  constructor
  · rintro ⟨hgx, hgxt⟩
    refine ⟨hgx, ?_⟩
    calc t * g = x * (x * t) * g := by rw [ht_eq]
      _ = x * ((x * t) * g) := by rw [mul_assoc]
      _ = x * (g * (x * t)) := by rw [hgxt]
      _ = (x * g) * (x * t) := by rw [← mul_assoc]
      _ = (g * x) * (x * t) := by rw [hgx]
      _ = g * (x * (x * t)) := by rw [mul_assoc]
      _ = g * t := by rw [ht_eq]
  · rintro ⟨hgx, hgt⟩
    refine ⟨hgx, ?_⟩
    calc (x * t) * g = x * (t * g) := by rw [mul_assoc]
      _ = x * (g * t) := by rw [hgt]
      _ = (x * g) * t := by rw [← mul_assoc]
      _ = (g * x) * t := by rw [hgx]
      _ = g * (x * t) := by rw [mul_assoc]

private theorem Gxy_mul_self {H : Type} [Group H] {x t : H} (hx2 : x * x = 1) :
    Gxy x (x * t) = Gxy x t := by
  rw [Gxy_eq_inf x (x * t), Gxy_eq_inf x t, Gx_inf_mul_self hx2]

private theorem Gxyz_mul_self {H : Type} [Group H] {x t a : H} (hx2 : x * x = 1) :
    Gxyz x (x * t) a = Gxyz a x t := by
  rw [Gxyz_eq_inf x (x * t) a, Gxyz_eq_inf a x t, Gxy_eq_inf x (x * t), Gxy_eq_inf a x,
    Gx_inf_mul_self hx2]
  ac_rfl

theorem cp_dichotomy (h : F5Std a z) {b t : G} (hb : b ∈ InvIn (Gx a)) (hbA : IsConj a b)
    (hba : b ≠ a) (hcase : b ∈ orb2A a a ∨ t ∈ orb2A a b) (ht : t ∈ InvIn (Gxy a b))
    (hta : t ≠ a) (htb : t ≠ b) (htab : t ≠ a * b) {K' : Subgroup G'} {φ₁ φ₂ : G → G'}
    (h₁ : IsIsoOn (Gxy b t) K' φ₁) (h₂ : IsIsoOn (Gxy b t) K' φ₂)
    (hS : ∀ x ∈ Gxyz a b t, φ₁ x = φ₂ x) :
    (∀ x ∈ Gxy b t, φ₁ x = φ₂ x) ∨ ∀ x ∈ Gxy b t, φ₁ x = φ₂ (a * x * a⁻¹) := by
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rw [hb.2] at h
    simpa [pow_two] using h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht.2] at h
    simpa [pow_two] using h
  have ha2 : a * a = 1 := by
    have hp := pow_orderOf_eq_one a
    rw [h.typ.orderOf_a] at hp
    simpa [pow_two] using hp
  have hba_comm : b * a = a * b := (mem_Gx.1 hb.1).symm
  have hbt : t ∈ Gx b := (mem_Gxy.1 ht.1).2
  have htb_comm : t * b = b * t := (mem_Gx.1 hbt).symm
  have hta_comm : t * a = a * t := (mem_Gx.1 (mem_Gxy.1 ht.1).1).symm
  have haGxb : a ∈ Gx b := mem_Gx.2 hba_comm
  have haGxt : a ∈ Gx t := mem_Gx.2 hta_comm
  have haGxy : a ∈ Gxy b t := mem_Gxy.2 ⟨haGxb, haGxt⟩
  have hS' : ∀ x ∈ Gxyz b t a, φ₁ x = φ₂ x := by
    intro x hx
    obtain ⟨hxb, hxt, hxa⟩ := mem_Gxyz.1 hx
    exact hS x (mem_Gxyz.2 ⟨hxa, hxb, hxt⟩)
  have hB : F5Std b z := h.of_isConj hbA (IsConj.refl z)
  have htb' : t ∈ InvIn (Gx b) := ⟨hbt, ht.2⟩
  rcases inv_cover hB htb' with htb_eq | ht2A | ht2B | ht2AB | ht2BB
  · exact (htb htb_eq).elim
  ·
    have hc : t ∈ orb2A a b := ⟨hbA.trans ht2A.1, hbA.trans ht2A.2⟩
    have ht_a : a ∈ InvIn (Gxy b t) := ⟨haGxy, h.typ.orderOf_a⟩
    have hane : a ≠ b * t := by
      intro heq
      exact htab (by
        have h1 : t = b * a := by
          calc t = b * (b * t) := by rw [← mul_assoc, hb2, one_mul]
            _ = b * a := by rw [← heq]
        rwa [hba_comm] at h1)
    exact aut_A8_cent_iso (h := h) (b := b) (c := t) (t := a) hbA hc ht_a hba.symm hta.symm
      hane h₁ h₂ hS'
  ·
    have hcaseA : b ∈ orb2A a a := by
      rcases hcase with hbA' | htA'
      · exact hbA'
      · exact (h.not_isConj (htA'.2.trans ht2B.2.symm)).elim
    have ha2A : a ∈ orb2A b b := by
      refine ⟨hbA.symm, ?_⟩
      rw [hba_comm]
      exact hbA.symm.trans hcaseA.2
    have hdisj : a ∈ orb2A b t ∨ a ∈ orb2B b z t := by
      have hta2 : orderOf (t * a) = 2 := by
        apply orderOf_eq_prime
        · rw [pow_two]
          calc (t * a) * (t * a) = t * (a * t) * a := by group
            _ = t * (t * a) * a := by rw [← hta_comm]
            _ = (t * t) * (a * a) := by group
            _ = 1 := by rw [ht2, ha2, mul_one]
        · intro h1
          exact hta (by
            have h2 : t = a⁻¹ := eq_inv_of_mul_eq_one_left h1
            rwa [inv_eq_of_mul_eq_one_right ha2] at h2)
      rcases h.isConj_or_of_orderOf hta2 with hconj | hconj
      · exact Or.inl ⟨hbA.symm, hbA.symm.trans hconj⟩
      · exact Or.inr ⟨hbA.symm, hconj⟩
    exact aut_X_cent_iso (h := hB) (b := t) (t := a) ht2B ⟨ha2A, hdisj⟩ h₁ h₂ hS'
  ·
    have hcaseA : b ∈ orb2A a a := by
      rcases hcase with hbA' | htA'
      · exact hbA'
      · exact (h.not_isConj (htA'.1.trans ht2AB.1.symm)).elim
    have ha2A : a ∈ orb2A b b := by
      refine ⟨hbA.symm, ?_⟩
      rw [hba_comm]
      exact hbA.symm.trans hcaseA.2
    have hb'2B : b * t ∈ orb2B b z b := by
      refine ⟨ht2AB.2, ?_⟩
      have hbt_t : b * (b * t) = t := by rw [← mul_assoc, hb2, one_mul]
      rw [hbt_t]
      exact ht2AB.1
    have hbt2 : (b * t) * (b * t) = 1 := by
      calc (b * t) * (b * t) = b * (t * b) * t := by group
        _ = b * (b * t) * t := by rw [htb_comm]
        _ = (b * b) * (t * t) := by group
        _ = 1 := by rw [hb2, ht2, mul_one]
    have hbt_a_comm : (b * t) * a = a * (b * t) := by
      calc (b * t) * a = b * (t * a) := by group
        _ = b * (a * t) := by rw [hta_comm]
        _ = (b * a) * t := by group
        _ = (a * b) * t := by rw [hba_comm]
        _ = a * (b * t) := by group
    have hbta_ne : (b * t) * a ≠ 1 := by
      intro h1
      apply htab
      have ha_eq : a = b * t := by
        have h2 : a = (b * t)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hb2,
          htb_comm] at h2
        exact h2
      have h3 : t = b * a := by
        calc t = b * (b * t) := by rw [← mul_assoc, hb2, one_mul]
          _ = b * a := by rw [← ha_eq]
      rwa [hba_comm] at h3
    have hbta2 : orderOf ((b * t) * a) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two]
        calc ((b * t) * a) * ((b * t) * a) = (b * t) * (a * (b * t)) * a := by group
          _ = (b * t) * ((b * t) * a) * a := by rw [← hbt_a_comm]
          _ = ((b * t) * (b * t)) * (a * a) := by group
          _ = 1 := by rw [hbt2, ha2, mul_one]
      · exact hbta_ne
    have hdisj : a ∈ orb2A b (b * t) ∨ a ∈ orb2B b z (b * t) := by
      rcases h.isConj_or_of_orderOf hbta2 with hconj | hconj
      · exact Or.inl ⟨hbA.symm, hbA.symm.trans hconj⟩
      · exact Or.inr ⟨hbA.symm, hconj⟩
    have hGxy : Gxy b (b * t) = Gxy b t := Gxy_mul_self hb2
    have hGxyz : Gxyz b (b * t) a = Gxyz a b t := Gxyz_mul_self hb2
    have h₁' : IsIsoOn (Gxy b (b * t)) K' φ₁ := hGxy.symm ▸ h₁
    have h₂' : IsIsoOn (Gxy b (b * t)) K' φ₂ := hGxy.symm ▸ h₂
    have hS'' : ∀ x ∈ Gxyz b (b * t) a, φ₁ x = φ₂ x := by
      intro x hx
      exact hS x (hGxyz ▸ hx)
    rcases aut_X_cent_iso (h := hB) (b := b * t) (t := a) hb'2B ⟨ha2A, hdisj⟩ h₁' h₂' hS''
      with hres | hres
    · left
      intro x hx
      exact hres x (hGxy.symm ▸ hx)
    · right
      intro x hx
      exact hres x (hGxy.symm ▸ hx)
  ·
    have hcaseA : b ∈ orb2A a a := by
      rcases hcase with hbA' | htA'
      · exact hbA'
      · exact (h.not_isConj (htA'.1.trans ht2BB.1.symm)).elim
    have hw : t ∈ orb2BB a z b := ht2BB
    have ha2A' : a ∈ orb2A a b := by
      refine ⟨IsConj.refl a, ?_⟩
      rw [hba_comm]
      exact hcaseA.2
    exact aut_Y_cent_iso (h := h) (b := b) (w := t) (t := a) hbA hw ⟨haGxy, ha2A'⟩ h₁ h₂ hS'

end CFSG.EvenSporadicStandard.HNRecog.Section4
