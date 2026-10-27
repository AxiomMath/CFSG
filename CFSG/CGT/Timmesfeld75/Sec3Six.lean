module

public import CFSG.CGT.Timmesfeld75.Sec3Conj

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem mul_comm_of_mem_inf_normalizer {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {x y : G}
    (hxB : x ∈ B) (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hyA : y ∈ A)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) : x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ A :=
    A.mul_mem (conj_mem_of_mem_normalizer hxA hyA) (A.inv_mem hyA)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ B := by
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact B.mul_mem hxB (conj_mem_of_mem_normalizer hyB (B.inv_mem hxB))
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ A ⊓ B := ⟨h1, h2⟩
  rw [hAB, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem Cfg.mem_cfgM_of_mul_self_eq_one_of_mem_sup (c : Cfg T T₁) {t : G} (htt : t * t = 1)
    (ht : t ∈ normIn T₁ T ⊔ T) (htT : t ∉ T) : t ∈ cfgM T T₁ := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T) T inf_le_right
  have ht' : t ∈ ((normIn T₁ T : Set G) * (T : Set G)) := by
    rw [← hmul]
    exact ht
  obtain ⟨b, hb, s, hs, rfl⟩ := ht'
  by_cases hsM : s ∈ cfgM T T₁
  · exact (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_right T T₁ hb) hsM
  · exfalso
    have hbb : b * b = 1 := elemAbelian_mul_self c.wc₁.1 (normIn_le _ _ hb)
    have hss : s * s = 1 := elemAbelian_mul_self c.wc.1 hs
    have hcomm : s * b = b * s := by
      have h1 : (b * s)⁻¹ = b * s := inv_eq_of_mul_eq_one_right htt
      rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hss, inv_eq_of_mul_eq_one_right hbb] at h1
    have hbL : b ∈ normIn T T₁ := by
      rw [← c.cfgM_inf_centralizer hs hsM]
      exact ⟨Cfg.normIn_le_cfgM_right T T₁ hb, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
    exact htT (T.mul_mem (normIn_le _ _ hbL) hs)

theorem Cfg.commute_conj_L₁ (c : Cfg T T₁) {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G))
    (hne : conjSubgroup h (normIn T₁ T) ⊓ (normIn T₁ T ⊔ T) ≠ ⊥) :
    (∀ x ∈ conjSubgroup h (normIn T₁ T), ∀ y ∈ normIn T₁ T, x * y = y * x) ∧
      (∀ x ∈ conjSubgroup h (normIn T₁ T), ∀ y ∈ normIn T T₁, x * y = y * x) := by
  have hhT : conjSubgroup h T = T := mem_normalizer_iff_conjSubgroup_eq.1 hh
  have hL₂ : conjSubgroup h (normIn T₁ T) = normIn (conjSubgroup h T₁) T := by
    rw [← normIn_conj, hhT]
  have hwc₂ : IsWC (conjSubgroup h T₁) := c.wc₁.conj h
  have hTT₂ : T ⊓ conjSubgroup h T₁ = ⊥ := by
    have h1 := conjSubgroup_inf h T T₁
    rw [hhT, c.inf] at h1
    exact h1.symm.trans (Subgroup.map_bot _)
  by_cases hT₂ : conjSubgroup h T₁ = T₁
  · have hL : conjSubgroup h (normIn T₁ T) = normIn T₁ T := by rw [hL₂, hT₂]
    rw [hL]
    exact ⟨fun x hx y hy => elemAbelian_mul_comm c.wc₁.1 (normIn_le _ _ hx) (normIn_le _ _ hy),
      fun x hx y hy => (c.comm_L_L₁ hy hx).symm⟩
  · have hT₁T₂ : T₁ ⊓ conjSubgroup h T₁ = ⊥ := c.wc₁.inf_conj_eq_bot hT₂
    obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
    have htL₂ : t ∈ normIn (conjSubgroup h T₁) T := by
      rw [← hL₂]
      exact ht.1
    have htT₂ : t ∈ conjSubgroup h T₁ := normIn_le _ _ htL₂
    have htT : t ∉ T := fun htT => ht1' (by
      have h1 : t ∈ T ⊓ conjSubgroup h T₁ := ⟨htT, htT₂⟩
      rwa [hTT₂, Subgroup.mem_bot] at h1)
    have htt : t * t = 1 :=
      elemAbelian_mul_self (isElemAbelian_conjSubgroup c.wc₁.1 h) htT₂
    have htM : t ∈ cfgM T T₁ := c.mem_cfgM_of_mul_self_eq_one_of_mem_sup htt ht.2 htT
    obtain ⟨a, ha, b, hb, hab⟩ := c.mem_cfgM_iff.1 htM
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact htT (by rw [hab, mul_one]; exact normIn_le _ _ ha)
    have hMN : ∀ m ∈ cfgM T T₁, m ∈ Subgroup.normalizer (conjSubgroup h T₁ : Set G) :=
      fun m hm => hwc₂.centralizer_le_normalizer htT₂ ht1' (Subgroup.mem_centralizer_singleton_iff.2
        (elemAbelian_mul_comm c.isElemAbelian_cfgM hm htM))
    have hL₂T₂ : ∀ x ∈ conjSubgroup h (normIn T₁ T), x ∈ conjSubgroup h T₁ := fun x hx => by
      rw [hL₂] at hx
      exact normIn_le _ _ hx
    have hL₂N : ∀ x ∈ conjSubgroup h (normIn T₁ T), x ∈ Subgroup.normalizer (T : Set G) :=
      fun x hx => by
        rw [hL₂] at hx
        exact (mem_normIn.1 hx).2
    have hcommL : ∀ x ∈ conjSubgroup h (normIn T₁ T), ∀ y ∈ normIn T T₁, x * y = y * x :=
      fun x hx y hy => mul_comm_of_mem_inf_normalizer hTT₂ (hL₂T₂ x hx) (hL₂N x hx)
        (normIn_le _ _ hy) (hMN y (Cfg.normIn_le_cfgM_left T T₁ hy))
    have haa : a * a = 1 := elemAbelian_mul_self c.wc.1 (normIn_le _ _ ha)
    have hbat : b = a * t := by rw [hab, ← mul_assoc, haa, one_mul]
    have hxb : ∀ x ∈ conjSubgroup h (normIn T₁ T), x * b = b * x := by
      intro x hx
      have hxt : x * t = t * x :=
        elemAbelian_mul_comm (isElemAbelian_conjSubgroup c.wc₁.1 h) (hL₂T₂ x hx) htT₂
      calc x * b = x * (a * t) := by rw [← hbat]
        _ = (x * a) * t := by rw [mul_assoc]
        _ = (a * x) * t := by rw [hcommL x hx a ha]
        _ = a * (x * t) := by rw [mul_assoc]
        _ = a * (t * x) := by rw [hxt]
        _ = (a * t) * x := by rw [mul_assoc]
        _ = b * x := by rw [← hbat]
    have hL₂N₁ : ∀ x ∈ conjSubgroup h (normIn T₁ T), x ∈ Subgroup.normalizer (T₁ : Set G) :=
      fun x hx => c.wc₁.centralizer_le_normalizer (normIn_le _ _ hb) hb1
        (Subgroup.mem_centralizer_singleton_iff.2 (hxb x hx))
    exact ⟨fun x hx y hy => mul_comm_of_mem_inf_normalizer hT₁T₂ (hL₂T₂ x hx) (hL₂N₁ x hx)
      (normIn_le _ _ hy) (hMN y (Cfg.normIn_le_cfgM_right T T₁ hy)), hcommL⟩

end CFSG.CGT.Timmesfeld75
