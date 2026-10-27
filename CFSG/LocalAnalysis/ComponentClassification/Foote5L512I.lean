module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512H
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter CFSG.GH74.GLS.IVK.Lifted

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem exists_involution_ne_t_L512 : ∃ a ∈ S ⊓ L, a * a = 1 ∧ a ≠ 1 ∧ a ≠ t := by
  obtain ⟨m, hm, ⟨e⟩⟩ := h.exists_dihedral_R
  have : Fact (1 < 2 ^ m) := ⟨Nat.one_lt_two_pow (by omega)⟩
  have hinv : ∀ i : ZMod (2 ^ m), ((e.symm (DihedralGroup.sr i) : ↥(S ⊓ L)) : G) *
      (e.symm (DihedralGroup.sr i) : ↥(S ⊓ L)) = 1 := fun i => by
    rw [← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one, Subgroup.coe_one]
  have hne1 : ∀ i : ZMod (2 ^ m), ((e.symm (DihedralGroup.sr i) : ↥(S ⊓ L)) : G) ≠ 1 := by
    intro i h1
    have h2 : e.symm (DihedralGroup.sr i) = 1 := Subtype.ext h1
    have h3 : DihedralGroup.sr i = 1 := by rw [← e.apply_symm_apply (DihedralGroup.sr i), h2,
      map_one]
    rw [DihedralGroup.one_def] at h3
    cases h3
  have hne01 : ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : G) ≠
      (e.symm (DihedralGroup.sr 1) : ↥(S ⊓ L)) := by
    intro h1
    have h2 := e.symm.injective (Subtype.ext h1)
    exact zero_ne_one (DihedralGroup.sr.inj h2)
  by_cases h0 : ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : G) = t
  · refine ⟨_, (e.symm (DihedralGroup.sr 1)).2, hinv 1, hne1 1, fun h1 => hne01 (h0.trans h1.symm)⟩
  · exact ⟨_, (e.symm (DihedralGroup.sr 0)).2, hinv 0, hne1 0, h0⟩

theorem exists_conj_z_of_mem_L_L512 {s : G} (hz : z = s⁻¹ * t * s) {v : G} (hvL : v ∈ L)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) : ∃ g' : G, v = g'⁻¹ * z * g' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcL, hc⟩ := exists_conj_le_of_isSylowOf h.R_sylow (zpowers_le.mpr hvL)
    (isPGroup_zpowers_of_pow_two (k := 1) (by rw [pow_one, sq]; exact hv2))
  have hr := hc v (mem_zpowers v)
  have hr2 : c⁻¹ * v * c * (c⁻¹ * v * c) = 1 := by
    rw [show c⁻¹ * v * c * (c⁻¹ * v * c) = c⁻¹ * (v * v) * c by group, hv2]
    group
  have hr1 : c⁻¹ * v * c ≠ 1 := fun h1 => hv1 (by
    calc v = c * (c⁻¹ * v * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨k, -, hk⟩ := h.exists_conj_t hr (orderOf_eq_prime (by rw [sq]; exact hr2) hr1)
  refine ⟨s⁻¹ * k⁻¹ * c⁻¹, ?_⟩
  calc v = (c * k) * (k⁻¹ * (c⁻¹ * v * c) * k) * (c * k)⁻¹ := by group
    _ = (c * k) * t * (c * k)⁻¹ := by rw [hk]
    _ = (s⁻¹ * k⁻¹ * c⁻¹)⁻¹ * (s⁻¹ * t * s) * (s⁻¹ * k⁻¹ * c⁻¹) := by group
    _ = (s⁻¹ * k⁻¹ * c⁻¹)⁻¹ * z * (s⁻¹ * k⁻¹ * c⁻¹) := by rw [← hz]

theorem conj_z_ne_diag_L512 (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S)
    (hz : z = s⁻¹ * t * s) (hRsQ : conjugate (S ⊓ L) s ≤ Q) {r r' : G} (hr : r ∈ S ⊓ L)
    (hr' : r' ∈ conjugate (S ⊓ L) s) (hr1 : r ≠ 1) (hr'1 : r' ≠ 1) (g' : G) :
    g'⁻¹ * z * g' ≠ r * r' := by
  intro hg
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hst : s * t * s⁻¹ ≠ t := by rw [h.conj_t_eq_z hss hz]; exact h.z_ne_t
  have hRs := h.inf_conjugate_R_eq_bot hna hsN hst
  have hmem : g'⁻¹ * z * g' ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s := by
    rw [hg]
    exact mul_mem (mem_sup_left hr) (mem_sup_right hr')
  rcases h.mem_R_or_mem_Rs_of_conj hna hT2 hsT hsS hz hRsQ hmem with h1 | h1
  · rw [hg] at h1
    have h2 : r' ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr
      ⟨by simpa using mul_mem (inv_mem hr) h1, hr'⟩
    rw [hRs, mem_bot] at h2
    exact hr'1 h2
  · rw [hg] at h1
    have h2 : r ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr
      ⟨hr, by simpa using mul_mem h1 (inv_mem hr')⟩
    rw [hRs, mem_bot] at h2
    exact hr1 h2

include ε in
theorem conj_z_mem_S_of_lemmas (hD : Foote5AutData 𝕊 Lin) (hL24 : Foote5Lemma24iiV)
    (h𝕊 : FooteSimpleType 𝕊) (hQd : DSDData ↥Q)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hT2 : Nat.card T = 2 * Nat.card S)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s)
    (hRsQ : conjugate (S ⊓ L) s ≤ Q) {g : G} (hgT : g⁻¹ * z * g ∈ T) : g⁻¹ * z * g ∈ S := by
  classical
  by_contra hgS
  have ht2 := h.t_mul_self
  have hz2 := h.z_mul_self
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨x, hx⟩ : ∃ w, w = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hx] at hgT hgS
  have hgx : g * x * g⁻¹ = z := by rw [hx]; group
  have hx2 : x * x = 1 := by
    rw [hx, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hz2]
    group
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hs'S : s⁻¹ ∉ S := fun h1 => hsS (by simpa using inv_mem h1)
  have hσ : s⁻¹ * x ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 (inv_mem hsT) hgT hs'S hgS
  have hsx : s * x ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hgT hsS hgS
  have hxt : x * t * x⁻¹ = z := by
    calc x * t * x⁻¹ = s * ((s⁻¹ * x) * t * (s⁻¹ * x)⁻¹) * s⁻¹ := by group
      _ = s * t * s⁻¹ := by rw [h.tZ _ hσ, mul_inv_cancel_right]
      _ = z := h.conj_t_eq_z hss hz
  have hxR : ∀ r ∈ S ⊓ L, x * r * x⁻¹ ∈ conjugate (S ⊓ L) s := by
    intro r hr
    rw [mem_conjugate_iff, show s * (x * r * x⁻¹) * s⁻¹ = (s * x) * r * (s * x)⁻¹ by group]
    exact mem_inf.mpr ⟨mul_mem (mul_mem hsx (mem_inf.mp hr).1) (inv_mem hsx),
      (mem_normalizer_iff.mp (h.S_le hsx) r).mp (mem_inf.mp hr).2⟩
  have hzRs : z ∈ conjugate (S ⊓ L) s := by
    rw [mem_conjugate_iff, hz, show s * (s⁻¹ * t * s) * s⁻¹ = t by group]
    exact h.tR
  obtain ⟨a, ha, ha2, ha1, hat⟩ := h.exists_involution_ne_t_L512
  have hbRs := hxR a ha
  have hbQ := hRsQ hbRs
  obtain ⟨y, hyx, hyt, hya, hyz, hyb⟩ :=
    h.exists_y_L512 ε hL24 h𝕊 hQd hna ha ha2 ha1 hat hx2 hxt hbQ
  obtain ⟨b, hb⟩ : ∃ w, w = x * a * x⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hbRs hbQ hyz hyb
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  have hxz : x * z * x⁻¹ = t := by
    calc x * z * x⁻¹ = (x * x) * t * (x * x)⁻¹ := by rw [← hxt]; group
      _ = t := by rw [hx2]; group
  have hxb : x * b * x⁻¹ = a := by
    calc x * b * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by rw [hb]; group
      _ = a := by rw [hx2]; group
  have hb2 : b * b = 1 := by
    rw [hb, show x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ by group, ha2]
    group
  have hb1 : b ≠ 1 := fun h1 => ha1 (by rw [← hxb, h1]; group)
  have hbz : b ≠ z := fun h1 => hat (by rw [← hxb, h1, hxz])
  have hab : a * b = b * a := (h.commute_Q_R hbQ ha).symm
  have htb : t * b = b * t := (h.commute_Q_R hbQ h.tR).symm
  have hatc : a * t = t * a := h.tZ a (mem_inf.mp ha).1
  have haz : a * z = z * a := h.zS a (mem_inf.mp ha).1
  have htz : t * z = z * t := h.zS t h.tS
  have hbzc : b * z = z * b := h.zS b (h.QS hbQ)
  have hc₁2 : a * b * (a * b) = 1 := by
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab,
      show a * (a * b) * b = (a * a) * (b * b) by group, ha2, hb2, one_mul]
  have hc₂2 : t * z * (t * z) = 1 := by
    rw [show t * z * (t * z) = t * (z * t) * z by group, ← htz,
      show t * (t * z) * z = (t * t) * (z * z) by group, ht2, hz2, one_mul]
  have hc₁₂ : a * b * (t * z) = t * z * (a * b) := by
    calc a * b * (t * z) = a * (b * t) * z := by group
      _ = a * t * (b * z) := by rw [← htb]; group
      _ = t * (a * z) * b := by rw [hatc, hbzc]; group
      _ = t * z * (a * b) := by rw [haz]; group
  have hdiag : a * b * (t * z) = a * t * (b * z) := by
    calc a * b * (t * z) = a * (b * t) * z := by group
      _ = a * t * (b * z) := by rw [← htb]; group
  have hc₁1 : a * b ≠ 1 := fun h1 => ha1 (by
    have h2 : a ∈ Q ⊓ L := mem_inf.mpr ⟨by rw [eq_inv_of_mul_eq_one_left h1]; exact inv_mem hbQ,
      (mem_inf.mp ha).2⟩
    rwa [h.Q_inf_L, mem_bot] at h2)
  have hc₂1 : t * z ≠ 1 := fun h1 => h.t_ne_one (by
    have h2 : t ∈ Q ⊓ L := mem_inf.mpr ⟨by rw [eq_inv_of_mul_eq_one_left h1]; exact inv_mem h.zQ,
      h.tL⟩
    rwa [h.Q_inf_L, mem_bot] at h2)
  have hc₁c₂ : a * b ≠ t * z := fun h1 => hat (by
    have h2 : t⁻¹ * a = z * b⁻¹ := by
      calc t⁻¹ * a = t⁻¹ * (a * b) * b⁻¹ := by group
        _ = z * b⁻¹ := by rw [h1]; group
    have h3 : t⁻¹ * a ∈ Q ⊓ L := mem_inf.mpr ⟨by rw [h2]; exact mul_mem h.zQ (inv_mem hbQ),
      mul_mem (inv_mem h.tL) (mem_inf.mp ha).2⟩
    rw [h.Q_inf_L, mem_bot, inv_mul_eq_one] at h3
    exact h3.symm)
  have hxc : ∀ c : G, x * c * x⁻¹ = c → (g * c * g⁻¹) * z = z * (g * c * g⁻¹) := by
    intro c hc
    have h1 : x * c = c * x := by
      calc x * c = x * c * x⁻¹ * x := by group
        _ = c * x := by rw [hc]
    calc g * c * g⁻¹ * z = g * c * g⁻¹ * (g * x * g⁻¹) := by rw [hgx]
      _ = g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
      _ = z * (g * c * g⁻¹) := by rw [hgx]
  have hxc₁ : x * (a * b) * x⁻¹ = a * b := by
    rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, ← hb, hxb, hab]
  have hxc₂ : x * (t * z) * x⁻¹ = t * z := by
    rw [show x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) by group, hxt, hxz, htz]
  have hyc₁ : y * (a * b) * y⁻¹ = a * b * (t * z) := by
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group, hya, hyb, hdiag]
  have hyc₂ : y * (t * z) * y⁻¹ = a * b := by
    rw [show y * (t * z) * y⁻¹ = (y * t * y⁻¹) * (y * z * y⁻¹) by group, hyt, hyz]
  obtain ⟨v₁, hv₁⟩ : ∃ w, w = g * (a * b) * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ w, w = g * (t * z) * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ w, w = g * y * g⁻¹ := ⟨_, rfl⟩
  have hconj2 : ∀ c : G, c * c = 1 → g * c * g⁻¹ * (g * c * g⁻¹) = 1 := fun c hc => by
    rw [show g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ by group, hc]
    group
  have hconj1 : ∀ c : G, c ≠ 1 → g * c * g⁻¹ ≠ 1 := fun c hc h1 => hc (by
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hv₁2 : v₁ * v₁ = 1 := by rw [hv₁]; exact hconj2 _ hc₁2
  have hv₂2 : v₂ * v₂ = 1 := by rw [hv₂]; exact hconj2 _ hc₂2
  have hv₁1 : v₁ ≠ 1 := by rw [hv₁]; exact hconj1 _ hc₁1
  have hv₂1 : v₂ ≠ 1 := by rw [hv₂]; exact hconj1 _ hc₂1
  have hv₁₂ne : v₁ ≠ v₂ := fun h1 => hc₁c₂ (by
    rw [hv₁, hv₂] at h1
    rwa [mul_left_inj, mul_right_inj] at h1)
  have hv₁₂ : v₁ * v₂ = v₂ * v₁ := by
    rw [hv₁, hv₂, show g * (a * b) * g⁻¹ * (g * (t * z) * g⁻¹) = g * (a * b * (t * z)) * g⁻¹ by
      group, hc₁₂]
    group
  have hv₁v₂ : v₁ * v₂ = g * (a * b * (t * z)) * g⁻¹ := by rw [hv₁, hv₂]; group
  set V := kleinFourOfCommutingInvolutions v₁ v₂ hv₁2 hv₂2 hv₁₂ with hVdef
  have hVmem : ∀ v ∈ V, v = v₁ * v₂ ∨ v = v₁ ∨ v = v₂ ∨ v = 1 := fun v hv =>
    (mem_kleinFour_iff hv₁2 hv₂2 hv₁₂).mp hv
  have hV4 : Nat.card V = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions v₁ v₂ hv₁2 hv₂2 hv₁1 hv₂1 hv₁₂ne hv₁₂).card_four
  have hVz : V ≤ centralizer ({z} : Set G) := fun v hv => by
    rw [mem_centralizer_singleton_iff]
    rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [hv₁v₂]
      exact hxc _ (by rw [show x * (a * b * (t * z)) * x⁻¹ =
        (x * (a * b) * x⁻¹) * (x * (t * z) * x⁻¹) by group, hxc₁, hxc₂])
    · rw [hv₁]; exact hxc _ hxc₁
    · rw [hv₂]; exact hxc _ hxc₂
    · rw [one_mul, mul_one]
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show v₁ * v₂ * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ by group, ← hv₁₂,
        show v₁ * (v₁ * v₂) * v₂ = (v₁ * v₁) * (v₂ * v₂) by group, hv₁2, hv₂2, one_mul]
    · exact hv₁2
    · exact hv₂2
    · exact one_mul 1
  have hVL : V ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [mem_bot]
    obtain ⟨hvV, hvL⟩ := mem_inf.mp hv
    by_contra hv1
    obtain ⟨g', hg'⟩ := h.exists_conj_z_of_mem_L_L512 hz hvL (hVsq v hvV) hv1
    have hcz : ∀ c : G, v = g * c * g⁻¹ → (g' * g)⁻¹ * z * (g' * g) = c := fun c hc => by
      calc (g' * g)⁻¹ * z * (g' * g) = g⁻¹ * (g'⁻¹ * z * g') * g := by group
        _ = c := by rw [← hg', hc]; group
    have hat1 : a * t ≠ 1 := fun h1 => hat (by
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left ht2])
    have hbz1 : b * z ≠ 1 := fun h1 => hbz (by
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left hz2])
    rcases hVmem v hvV with h1 | h1 | h1 | h1
    · rw [hv₁v₂] at h1
      have h2 := hcz _ h1
      rw [hdiag] at h2
      exact h.conj_z_ne_diag_L512 hna hT2 hsT hsS hz hRsQ (mul_mem ha h.tR) (mul_mem hbRs hzRs)
        hat1 hbz1 _ h2
    · rw [hv₁] at h1
      exact h.conj_z_ne_diag_L512 hna hT2 hsT hsS hz hRsQ ha hbRs ha1 hb1 _ (hcz _ h1)
    · rw [hv₂] at h1
      exact h.conj_z_ne_diag_L512 hna hT2 hsT hsS hz hRsQ h.tR hzRs h.t_ne_one hz1 _ (hcz _ h1)
    · exact hv1 h1
  have hy'c : ∀ c d : G, y * c * y⁻¹ = d → y' * (g * c * g⁻¹) * y'⁻¹ = g * d * g⁻¹ := by
    intro c d hcd
    rw [hy', show g * y * g⁻¹ * (g * c * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * c * y⁻¹) * g⁻¹ by
      group, hcd]
  have hy'z : y' * z = z * y' := by
    rw [hy', ← hgx]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hyx]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  have hy'₁ : y' * v₁ * y'⁻¹ = v₁ * v₂ := by rw [hv₁v₂, hv₁, hy'c _ _ hyc₁]
  have hy'₂ : y' * v₂ * y'⁻¹ = v₁ := by rw [hv₂, hy'c _ _ hyc₂, hv₁]
  have hy'₁₂ : y' * (v₁ * v₂) * y'⁻¹ = v₂ := by
    rw [show y' * (v₁ * v₂) * y'⁻¹ = (y' * v₁ * y'⁻¹) * (y' * v₂ * y'⁻¹) by group, hy'₁, hy'₂,
      show v₁ * v₂ * v₁ = v₁ * (v₂ * v₁) by group, ← hv₁₂, ← mul_assoc, hv₁2, one_mul]
  have hv₁V : v₁ ∈ V := (mem_kleinFour_iff hv₁2 hv₂2 hv₁₂).mpr (Or.inr (Or.inl rfl))
  have hv₂V : v₂ ∈ V := (mem_kleinFour_iff hv₁2 hv₂2 hv₁₂).mpr (Or.inr (Or.inr (Or.inl rfl)))
  refine h.false_of_fourgroup_cent_z ε hD hVz hVsq hV4 hVL hy'z (fun v hv => ?_)
    (fun v hv hfix => ?_)
  · rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [hy'₁₂]; exact hv₂V
    · rw [hy'₁]; exact mul_mem hv₁V hv₂V
    · rw [hy'₂]; exact hv₁V
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
  · rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1] at hfix ⊢
    · rw [hy'₁₂] at hfix
      exact absurd (by simpa using hfix.symm) hv₁1
    · rw [hy'₁] at hfix
      exact absurd (by simpa using hfix) hv₂1
    · rw [hy'₂] at hfix
      exact absurd hfix hv₁₂ne

end Sec5

end CFSG.ComponentClassification.Foote5
