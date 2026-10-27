module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L513B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem false_of_inner_L513 (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hT2 : Nat.card T = 2 * Nat.card S)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s)
    (hRsQ : conjugate (S ⊓ L) s ≤ Q) {y : G} (hyS : y ∈ S) (hzy : IsConj z y)
    (hyinn : actG L ε y ∈ innAut5 𝕊) (hyR : y ∉ S ⊓ L) (hyRs : y ∉ conjugate (S ⊓ L) s) :
    False := by
  classical
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have ht2 := h.t_mul_self
  have hz2 := h.z_mul_self
  have hy2 : y * y = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hzy
    rw [show c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ by group, hz2]
    group
  have hQL : ∀ w : G, w ∈ Q → w ∈ L → w = 1 := fun w hw hwL => by
    have h1 : w ∈ Q ⊓ L := mem_inf.mpr ⟨hw, hwL⟩
    rwa [h.Q_inf_L, mem_bot] at h1
  obtain ⟨q, hq, r, hr, rfl⟩ := h.exists_mul_of_inner ε hyS hyinn
  have hqr := h.commute_Q_R hq hr
  have hqq : q * q = 1 := by
    have h1 : (q * q) * (r * r) = 1 := by
      rw [← hy2, show q * r * (q * r) = q * (r * q) * r by group, ← hqr]
      group
    exact hQL _ (mul_mem hq hq) (by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (mul_mem (mem_inf.mp hr).2 (mem_inf.mp hr).2))
  have hrr : r * r = 1 := by
    have h1 : (q * q) * (r * r) = 1 := by
      rw [← hy2, show q * r * (q * r) = q * (r * q) * r by group, ← hqr]
      group
    rwa [hqq, one_mul] at h1
  have hq1 : q ≠ 1 := fun h1 => hyR (by rw [h1, one_mul]; exact hr)
  have hqtR : q * t ∉ S ⊓ L := fun h1 => hq1 (hQL q hq (by
    have h2 := mul_mem (mem_inf.mp h1).2 (inv_mem h.tL)
    rwa [mul_inv_cancel_right] at h2))
  have hqtRs : q * t ∉ conjugate (S ⊓ L) s := fun h1 => h.t_not_mem_Q (by
    have h2 := mul_mem (inv_mem hq) (hRsQ h1)
    rwa [inv_mul_cancel_left] at h2)
  obtain ⟨y₁, r₁, hr₁, hy₁, hzy₁, hy₁R, hy₁Rs, hy₁c⟩ : ∃ y₁ r₁ : G, r₁ ∈ S ⊓ L ∧ y₁ = q * r₁ ∧
      IsConj z y₁ ∧ y₁ ∉ S ⊓ L ∧ y₁ ∉ conjugate (S ⊓ L) s ∧
      ∀ ρ ∈ S ⊓ L, y₁ * ρ = ρ * y₁ := by
    have hqc : ∀ ρ ∈ S ⊓ L, q * ρ = ρ * q := fun ρ hρ => h.commute_Q_R hq hρ
    have hqtc : ∀ ρ ∈ S ⊓ L, q * t * ρ = ρ * (q * t) := fun ρ hρ => by
      rw [mul_assoc, ← h.tZ ρ (mem_inf.mp hρ).1, ← mul_assoc, hqc ρ hρ, mul_assoc]
    by_cases hr1 : r = 1
    · exact ⟨q * r, r, hr, rfl, hzy, hyR, hyRs, fun ρ hρ => by rw [hr1, mul_one]; exact hqc ρ hρ⟩
    by_cases hrt : r = t
    · exact ⟨q * r, r, hr, rfl, hzy, hyR, hyRs, fun ρ hρ => by rw [hrt]; exact hqtc ρ hρ⟩
    obtain ⟨g', hg'q, hg'r⟩ := h.exists_conj_mul_of_mem_Q hr
      (orderOf_eq_prime (by rw [sq]; exact hrr) hr1) hq hqq hqr
    refine ⟨q * t, t, h.tR, rfl, hzy.trans (isConj_iff.mpr ⟨g'⁻¹, ?_⟩), hqtR, hqtRs, hqtc⟩
    calc g'⁻¹ * (q * r) * g'⁻¹⁻¹ = (g'⁻¹ * q * g') * (g'⁻¹ * r * g') := by group
      _ = q * t := by
          rw [hg'r, show g'⁻¹ * q * g' = q by rw [mul_assoc, ← hg'q]; group]
  have hy₁t : y₁ ≠ t := fun h1 => hy₁R (by rw [h1]; exact h.tR)
  have hinn := h.inner_conj_s_L513 ε hD hna hT2 hsT hsS hz hzy₁ hy₁c hy₁t
  have hy₁S : y₁ ∈ S := by rw [hy₁]; exact mul_mem (h.QS hq) (mem_inf.mp hr₁).1
  have hsy₁S : s * y₁ * s⁻¹ ∈ S := (mem_normalizer_iff.mp hsN y₁).mp hy₁S
  obtain ⟨q', hq', r', hr', hqr'⟩ := h.exists_mul_of_inner ε hsy₁S hinn
  have hQ's : s⁻¹ * q' * s ∈ conjugate Q s⁻¹ := by
    rw [mem_conjugate_iff, inv_inv, show s⁻¹ * (s⁻¹ * q' * s) * s = (s * s)⁻¹ * q' * (s * s) by
      group]
    have h1 := h.conj_mem_Q (inv_mem hss) hq'
    rwa [inv_inv] at h1
  have hr's : s⁻¹ * r' * s ∈ conjugate (S ⊓ L) s := by
    rw [mem_conjugate_iff, show s * (s⁻¹ * r' * s) * s⁻¹ = r' by group]
    exact hr'
  have hRQ' : ∀ ρ ∈ S ⊓ L, ρ ∈ conjugate Q s⁻¹ := fun ρ hρ => by
    rw [mem_conjugate_iff, inv_inv]
    exact hRsQ (by rw [mem_conjugate_iff, show s * (s⁻¹ * ρ * s) * s⁻¹ = ρ by group]; exact hρ)
  obtain ⟨-, hQQ'⟩ := h.conjugate_Q_inv_facts_L513 hsN hsT hz
  have hQ'bot := h.inf_conjugate_Q_inv_L513 hsT hz
  have hy₁eq : y₁ = (s⁻¹ * q' * s) * (s⁻¹ * r' * s) := by
    calc y₁ = s⁻¹ * (s * y₁ * s⁻¹) * s := by group
      _ = (s⁻¹ * q' * s) * (s⁻¹ * r' * s) := by rw [hqr']; group
  have hr'Q := hRsQ hr's
  have hkey : (s⁻¹ * r' * s)⁻¹ * q ∈ Q ⊓ conjugate Q s⁻¹ := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hr'Q) hq, ?_⟩
    have h1 : (s⁻¹ * r' * s)⁻¹ * q = (s⁻¹ * q' * s) * r₁⁻¹ := by
      have h2 : q * r₁ = (s⁻¹ * r' * s) * (s⁻¹ * q' * s) := by
        rw [← hy₁, hy₁eq, hQQ' _ hr'Q _ hQ's]
      calc (s⁻¹ * r' * s)⁻¹ * q = (s⁻¹ * r' * s)⁻¹ * (q * r₁) * r₁⁻¹ := by group
        _ = (s⁻¹ * q' * s) * r₁⁻¹ := by rw [h2]; group
    rw [h1]
    exact mul_mem hQ's (inv_mem (hRQ' r₁ hr₁))
  rw [hQ'bot, mem_bot, inv_mul_eq_one] at hkey
  have hdiag : y₁ ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s := by
    rw [hy₁, ← hkey]
    rw [hQQ' _ hr'Q _ (hRQ' r₁ hr₁)]
    exact mul_mem (mem_sup_left hr₁) (mem_sup_right hr's)
  obtain ⟨c, hc⟩ := isConj_iff.mp hzy₁
  have h1 : c⁻¹⁻¹ * z * c⁻¹ = y₁ := by rw [inv_inv, hc]
  rw [← h1] at hdiag hy₁R hy₁Rs
  rcases h.mem_R_or_mem_Rs_of_conj hna hT2 hsT hsS hz hRsQ hdiag with h2 | h2
  · exact hy₁R h2
  · exact hy₁Rs h2

include ε in
theorem false_of_field_L513 (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hT2 : Nat.card T = 2 * Nat.card S)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s)
    (hRsQ : conjugate (S ⊓ L) s ≤ Q) {x : G} (hxS : x ∈ S) (hzx : IsConj z x)
    (hxlin : actG L ε x ∉ Lin) : False := by
  classical
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hx2 : x * x = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hzx
    rw [show c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ by group, h.z_mul_self]
    group
  obtain ⟨u, hxu, huR, hulin⟩ := h.exists_conj_centralizer_R ε hD hxS hx2 hxlin
  have huN : u ∈ normalizer (L : Set G) := by
    by_contra hn
    apply hulin
    have h1 : actG L ε u = 1 := by
      unfold actG
      simp only [hn, ↓reduceDIte]
    rw [h1]
    exact one_mem _
  have hu2 : u * u = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxu
    rw [show c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ by group, hx2]
    group
  obtain ⟨c, hcN, hcR, hcS⟩ := h.exists_conj_mem_S_of_centralizes_R_L513 huN huR hu2
  obtain ⟨u', hu'⟩ : ∃ w, w = c⁻¹ * u * c := ⟨_, rfl⟩
  rw [← hu'] at hcS
  have hu'R : ∀ ρ ∈ S ⊓ L, u' * ρ = ρ * u' := fun ρ hρ => by
    have hc' : c⁻¹ * ρ = ρ * c⁻¹ := (Commute.inv_left (hcR ρ hρ)).eq
    calc u' * ρ = c⁻¹ * u * (c * ρ) := by rw [hu']; group
      _ = c⁻¹ * (u * ρ) * c := by rw [hcR ρ hρ]; group
      _ = c⁻¹ * ρ * u * c := by rw [huR ρ hρ]; group
      _ = ρ * u' := by rw [hc', hu']; group
  have hu'lin : actG L ε u' ∉ Lin := fun h1 => hulin (by
    have h2 : actG L ε u = actG L ε c * actG L ε u' * (actG L ε c)⁻¹ := by
      rw [hu', actG_mul ε (mul_mem (inv_mem hcN) huN) hcN, actG_mul ε (inv_mem hcN) huN,
        actG_inv ε hcN]
      group
    rw [h2]
    exact hD.normal.conj_mem _ h1 _)
  have hzu' : IsConj z u' := (hzx.trans hxu).trans (isConj_iff.mpr ⟨c⁻¹, by rw [hu', inv_inv]⟩)
  have hu't : u' ≠ t := fun h1 => hu'lin (by
    rw [h1, actG_of_mem_self ε h.tL]
    exact hD.inn_le ⟨_, rfl⟩)
  have hinn := h.inner_conj_s_L513 ε hD hna hT2 hsT hsS hz hzu' hu'R hu't
  have hyS : s * u' * s⁻¹ ∈ S := (mem_normalizer_iff.mp hsN u').mp hcS
  have hzy : IsConj z (s * u' * s⁻¹) := hzu'.trans (isConj_iff.mpr ⟨s, rfl⟩)
  have hyR : s * u' * s⁻¹ ∉ S ⊓ L := fun h1 => hu'lin (by
    have h2 : u' ∈ Q := hRsQ (by rw [mem_conjugate_iff]; exact h1)
    rw [(h.actG_eq_one_iff_mem_Q ε hcS).mpr h2]
    exact one_mem _)
  have hyRs : s * u' * s⁻¹ ∉ conjugate (S ⊓ L) s := fun h1 => hu'lin (by
    rw [mem_conjugate_iff] at h1
    have h2 : u' ∈ S ⊓ L := by
      have h3 := mem_inf.mp h1
      refine mem_inf.mpr ⟨hcS, ?_⟩
      have h4 := (mem_normalizer_iff.mp (inv_mem (h.S_le hss)) _).mp h3.2
      rwa [show (s * s)⁻¹ * (s * (s * u' * s⁻¹) * s⁻¹) * (s * s)⁻¹⁻¹ = u' by group] at h4
    rw [actG_of_mem_self ε (mem_inf.mp h2).2]
    exact hD.inn_le ⟨_, rfl⟩)
  exact h.false_of_inner_L513 ε hD hna hT2 hsT hsS hz hRsQ hyS hzy hinn hyR hyRs

include ε in
theorem lemma513_of_lemmas (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hT2 : Nat.card T = 2 * Nat.card S)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s)
    (hRsQ : conjugate (S ⊓ L) s ≤ Q) (h512 : ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ S)
    (g : G) (hgT : g⁻¹ * z * g ∈ T) :
    g⁻¹ * z * g ∈ S ⊓ L ∨ g⁻¹ * z * g ∈ conjugate (S ⊓ L) s ∨
      (actG L ε (g⁻¹ * z * g) ∈ Lin ∧ actG L ε (g⁻¹ * z * g) ∉ innAut5 𝕊) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, hRs, hpgl⟩ := hcon
  have hxS := h512 g hgT
  have hzx : IsConj z (g⁻¹ * z * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
  by_cases hinn : actG L ε (g⁻¹ * z * g) ∈ innAut5 𝕊
  · exact h.false_of_inner_L513 ε hD hna hT2 hsT hsS hz hRsQ hxS hzx hinn hR hRs
  · exact h.false_of_field_L513 ε hD hna hT2 hsT hsS hz hRsQ hxS hzx
      (fun h1 => hinn (hpgl h1))

end Sec5

end CFSG.ComponentClassification.Foote5
