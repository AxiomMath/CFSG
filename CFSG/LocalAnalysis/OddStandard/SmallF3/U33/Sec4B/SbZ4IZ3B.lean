module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

private abbrev z4iD (K : Subgroup H) (t τ l : H) : Subgroup H :=
  ⁅z4iVc K t τ l, z4iVc K t τ l⁆

private lemma z4iD_comm_le_self (K : Subgroup H) (t τ l : H) :
    ⁅z4iD K t τ l, z4iD K t τ l⁆ ≤ z4iD K t τ l := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact (z4iD K t τ l).mul_mem
    ((z4iD K t τ l).mul_mem ((z4iD K t τ l).mul_mem hx hy) ((z4iD K t τ l).inv_mem hx))
    ((z4iD K t τ l).inv_mem hy)

private lemma commutator_mem_K_of_Vc (h : ZEData Q Y V V' B K ρ t τ l) {x y : H}
    (hx : x ∈ z4iVc K t τ l) (hy : y ∈ z4iVc K t τ l) : ⁅x, y⁆ ∈ K := by
  obtain ⟨k, hk, s, hs, rfl⟩ := (mem_Vc_iff h).mp hx
  obtain ⟨k', hk', s', hs', rfl⟩ := (mem_Vc_iff h).mp hy
  have ha : s * k' * s⁻¹ ∈ K := h.T3_norm_K s hs k' hk'
  have hb : s' * k * s'⁻¹ ∈ K := h.T3_norm_K s' hs' k hk
  have hmain : (k * (s * k' * s⁻¹)) * (k' * (s' * k * s'⁻¹))⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem hk ha) (K.inv_mem (K.mul_mem hk' hb))
  have heq : ⁅k * s, k' * s'⁆ =
      ((k * s) * (k' * s')) * ((k' * s') * (k * s))⁻¹ := by
    rw [commutatorElement_def, mul_inv_rev]; group
  have hxy : (k * s) * (k' * s') = (k * (s * k' * s⁻¹)) * (s * s') := by group
  have hyx : (k' * s') * (k * s) = (k' * (s' * k * s'⁻¹)) * (s * s') := by
    calc (k' * s') * (k * s) = (k' * (s' * k * s'⁻¹)) * (s' * s) := by group
      _ = (k' * (s' * k * s'⁻¹)) * (s * s') := by rw [h.T3_comm s' hs' s hs]
  have htarget : ((k * (s * k' * s⁻¹)) * (s * s')) *
      ((k' * (s' * k * s'⁻¹)) * (s * s'))⁻¹ =
      (k * (s * k' * s⁻¹)) * (k' * (s' * k * s'⁻¹))⁻¹ := by group
  rw [heq, hxy, hyx, htarget]
  exact hmain

theorem D_le_K (h : ZEData Q Y V V' B K ρ t τ l) :
    ⁅z4iVc K t τ l, z4iVc K t τ l⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun _ hx _ hy => commutator_mem_K_of_Vc h hx hy

theorem F_comm_le_D (h : ZEData Q Y V V' B K ρ t τ l) :
    ⁅z4iF K t τ, z4iF K t τ⁆ ≤ ⁅z4iVc K t τ l, z4iVc K t τ l⁆ :=
  Subgroup.commutator_mono h.F_le_Vc h.F_le_Vc

theorem exists_D_not_Q (h : ZEData Q Y V V' B K ρ t τ l) :
    ∃ x ∈ ⁅z4iVc K t τ l, z4iVc K t τ l⁆, x ∉ Q := by
  have hnotle : ¬ (K : Set H) ⊆ (Q : Set H) := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [h.card_K, h.card_Q] at hc
    omega
  obtain ⟨m₀, hm₀K, hm₀Q⟩ := Set.not_subset.mp hnotle
  obtain ⟨m, hmK, hmQ⟩ := z4i_lam_nontriv (N := Q) (M := K) h.rho_pow_three h.l_rho
    h.rho_norm_Q h.rho_norm_K h.rho_fpf_KQ hm₀K hm₀Q
  exact ⟨⁅l, m⁆, Subgroup.commutator_mem_commutator
    (T3_le_Vc K t τ l (l_mem_T3 t τ l)) (K_le_Vc K t τ l hmK), hmQ⟩

theorem exists_D_Y_not_V (h : ZEData Q Y V V' B K ρ t τ l) :
    ∃ y ∈ ⁅z4iVc K t τ l, z4iVc K t τ l⁆, y ∈ Y ∧ y ∉ V := by
  have hnotle : ¬ (Y : Set H) ⊆ (V : Set H) := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [h.card_Y, h.card_V] at hc
    omega
  obtain ⟨m₀, hm₀Y, hm₀V⟩ := Set.not_subset.mp hnotle
  obtain ⟨m, hmY, hmV⟩ := z4i_lam_nontriv (N := V) (M := Y) h.rho_pow_three h.l_rho
    h.rho_norm_V h.rho_norm_Y h.fpf_YV hm₀Y hm₀V
  refine ⟨⁅l, m⁆, ?_, ?_, hmV⟩
  · exact Subgroup.commutator_mem_commutator (T3_le_Vc K t τ l (l_mem_T3 t τ l))
      (K_le_Vc K t τ l (h.Q_le_K (h.Y_le_Q hmY)))
  · rw [commutatorElement_def]
    exact Y.mul_mem (h.normal_Y l m hmY) (Y.inv_mem hmY)

theorem D_comm_eq_V (h : ZEData Q Y V V' B K ρ t τ l) :
    ⁅⁅z4iVc K t τ l, z4iVc K t τ l⁆, ⁅z4iVc K t τ l, z4iVc K t τ l⁆⁆ = V := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact h.comm_mem_V x (D_le_K h hx) y (D_le_K h hy)
  · intro v hv
    obtain ⟨x, hxD, hxQ⟩ := exists_D_not_Q h
    have hxK : x ∈ K := D_le_K h hxD
    obtain ⟨q, hqQ, hqv⟩ := h.comm_surj hxK hxQ hv
    obtain ⟨f, hfF, y, hyY, rfl⟩ := mem_F_comm_mul_Y h hqQ
    have hcomm := h.comm_mul_right hxK (F_comm_le_Q h hfF) (h.Y_le_Q hyY)
    have hone := h.comm_eq_one_of_mem_Y hxK hyY
    rw [hcomm, hone, mul_one] at hqv
    rw [← hqv]
    exact Subgroup.commutator_mem_commutator hxD (F_comm_le_D h hfF)

private lemma cent_D_le_F (h : ZEData Q Y V V' B K ρ t τ l) {z : H}
    (hzVc : z ∈ z4iVc K t τ l)
    (hzD : ∀ d ∈ z4iD K t τ l, d * z = z * d) : z ∈ z4iF K t τ := by
  have hVle : V ≤ z4iD K t τ l := by
    rw [← D_comm_eq_V h]
    exact z4iD_comm_le_self K t τ l
  have hcentV : z ∈ centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hzD v (hVle hv)
  have hmem : z ∈ z4iVc K t τ l ⊓ centralizer (V : Set H) := ⟨hzVc, hcentV⟩
  rwa [Vc_inf_cent_V h] at hmem

private lemma cent_D_cent_t (h : ZEData Q Y V V' B K ρ t τ l) {z : H}
    (hzD : ∀ d ∈ z4iD K t τ l, d * z = z * d)
    {k : H} (hk : k ∈ K) {a b : Fin 2}
    (hz : z = k * t ^ (a : ℕ) * τ ^ (b : ℕ)) : a = 0 := by
  obtain ⟨y₁, hy₁D, hy₁Y, hy₁V⟩ := exists_D_Y_not_V h
  have hzy : z * y₁ = y₁ * z := (hzD y₁ hy₁D).symm
  have hky : k * y₁ = y₁ * k := h.K_cent_Y k hk y₁ hy₁Y
  have hτy : τ ^ (b : ℕ) * y₁ = y₁ * τ ^ (b : ℕ) :=
    ((show Commute τ y₁ from tau_cent_Y h y₁ hy₁Y).pow_left b).eq
  have hty : t ^ (a : ℕ) * y₁ = y₁ * t ^ (a : ℕ) := by
    have hL : z * y₁ = k * (t ^ (a : ℕ) * y₁) * τ ^ (b : ℕ) := by
      rw [hz]
      calc k * t ^ (a : ℕ) * τ ^ (b : ℕ) * y₁
          = k * t ^ (a : ℕ) * (τ ^ (b : ℕ) * y₁) := by group
        _ = k * t ^ (a : ℕ) * (y₁ * τ ^ (b : ℕ)) := by rw [hτy]
        _ = k * (t ^ (a : ℕ) * y₁) * τ ^ (b : ℕ) := by group
    have hR : y₁ * z = k * (y₁ * t ^ (a : ℕ)) * τ ^ (b : ℕ) := by
      rw [hz]
      calc y₁ * (k * t ^ (a : ℕ) * τ ^ (b : ℕ))
          = (y₁ * k) * t ^ (a : ℕ) * τ ^ (b : ℕ) := by group
        _ = (k * y₁) * t ^ (a : ℕ) * τ ^ (b : ℕ) := by rw [hky]
        _ = k * (y₁ * t ^ (a : ℕ)) * τ ^ (b : ℕ) := by group
    have heq : k * (t ^ (a : ℕ) * y₁) * τ ^ (b : ℕ) =
        k * (y₁ * t ^ (a : ℕ)) * τ ^ (b : ℕ) := by rw [← hL, hzy, hR]
    exact mul_left_cancel (mul_right_cancel heq)
  fin_cases a
  · rfl
  · exfalso
    exact hy₁V (h.Y_cent_t y₁ hy₁Y (by simpa using hty))

private lemma cent_D_cent_τ (h : ZEData Q Y V V' B K ρ t τ l) {z : H}
    (hzD : ∀ d ∈ z4iD K t τ l, d * z = z * d)
    {k : H} (hk : k ∈ K) {b : Fin 2}
    (hz : z = k * τ ^ (b : ℕ)) : b = 0 := by
  fin_cases b
  · rfl
  · exfalso
    have hzτ : z = k * τ := by simpa using hz
    have hkey' : ∀ g ∈ ⁅z4iF K t τ, z4iF K t τ⁆, k * g⁻¹ * k⁻¹ = g := by
      intro g hg
      have hgD : g ∈ z4iD K t τ l := F_comm_le_D h hg
      have hgQ : g ∈ Q := F_comm_le_Q h hg
      have hzg : z * g * z⁻¹ = g := by
        have h1 : g * z = z * g := hzD g hgD
        calc z * g * z⁻¹ = (g * z) * z⁻¹ := by rw [← h1]
          _ = g := by group
      have h1 : (k * τ) * g * (k * τ)⁻¹ = g := by rw [← hzτ]; exact hzg
      have h2 : (k * τ) * g * (k * τ)⁻¹ = k * (τ * g * τ⁻¹) * k⁻¹ := by group
      rw [h2, h.tau_inv g hgQ] at h1
      exact h1
    have hkey : ∀ g ∈ ⁅z4iF K t τ, z4iF K t τ⁆, k * g * k⁻¹ = g⁻¹ := by
      intro g hg
      have hh := hkey' g⁻¹ ((⁅z4iF K t τ, z4iF K t τ⁆).inv_mem hg)
      simpa using hh
    have hconj : ∀ q ∈ Q, k * q * k⁻¹ = q⁻¹ := by
      intro q hq
      obtain ⟨f, hfF, y, hyY, rfl⟩ := mem_F_comm_mul_Y h hq
      have hfQ : f ∈ Q := F_comm_le_Q h hfF
      have hf := hkey f hfF
      have hy : k * y * k⁻¹ = y⁻¹ := by
        have h1 : k * y = y * k := h.K_cent_Y k hk y hyY
        have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.Y_sq y hyY)
        rw [h1, h2]
        group
      rw [show k * (f * y) * k⁻¹ = (k * f * k⁻¹) * (k * y * k⁻¹) by group, hf, hy]
      rw [mul_inv_rev]
      exact (h.Q_comm y⁻¹ (Q.inv_mem (h.Y_le_Q hyY)) f⁻¹ (Q.inv_mem hfQ)).symm
    have hτk_cent : ∀ q ∈ Q, (τ * k) * q = q * (τ * k) := by
      intro q hq
      have h1 : (τ * k) * q * (τ * k)⁻¹ = q := by
        calc (τ * k) * q * (τ * k)⁻¹ = τ * (k * q * k⁻¹) * τ⁻¹ := by group
          _ = τ * q⁻¹ * τ⁻¹ := by rw [hconj q hq]
          _ = (τ * q * τ⁻¹)⁻¹ := by group
          _ = (q⁻¹)⁻¹ := by rw [h.tau_inv q hq]
          _ = q := inv_inv q
      calc (τ * k) * q = ((τ * k) * q * (τ * k)⁻¹) * (τ * k) := by group
        _ = q * (τ * k) := by rw [h1]
    have hτkK : τ * k ∈ K := h.Q_le_K (h.cent_Q (τ * k) hτk_cent)
    have hτK : τ ∈ K := by
      have h1 : (τ * k) * k⁻¹ ∈ K := K.mul_mem hτkK (K.inv_mem hk)
      rwa [show (τ * k) * k⁻¹ = τ from by group] at h1
    have hmem : t ^ ((0 : Fin 2) : ℕ) * τ ^ ((1 : Fin 2) : ℕ) *
        l ^ ((0 : Fin 2) : ℕ) ∈ K := by simpa using hτK
    obtain ⟨-, hb1, -⟩ := word_mem_K h hmem
    exact (by decide : ¬ ((1 : Fin 2) = 0)) hb1

private lemma cent_D_mem_Y (h : ZEData Q Y V V' B K ρ t τ l) {z k : H}
    (hzD : ∀ d ∈ z4iD K t τ l, d * z = z * d)
    (hk : k ∈ K) (hzk : z = k) : k ∈ Y := by
  have hkcentQ : ∀ q ∈ Q, k * q = q * k := by
    intro q hq
    obtain ⟨f, hfF, y, hyY, rfl⟩ := mem_F_comm_mul_Y h hq
    have hfD : f ∈ z4iD K t τ l := F_comm_le_D h hfF
    have hkf : k * f = f * k := by
      have h1 : f * z = z * f := hzD f hfD
      rw [hzk] at h1
      exact h1.symm
    have hky : k * y = y * k := h.K_cent_Y k hk y hyY
    calc k * (f * y) = (k * f) * y := by group
      _ = (f * k) * y := by rw [hkf]
      _ = f * (k * y) := by group
      _ = f * (y * k) := by rw [hky]
      _ = (f * y) * k := by group
  have hkQ : k ∈ Q := h.cent_Q k hkcentQ
  obtain ⟨x, hxD, hxQ⟩ := exists_D_not_Q h
  have hxK : x ∈ K := D_le_K h hxD
  have hxk : x * k = k * x := by
    have h1 : x * z = z * x := hzD x hxD
    rw [hzk] at h1
    exact h1
  exact h.nondeg hxK hxQ hkQ hxk

theorem Vc_inf_cent_D (h : ZEData Q Y V V' B K ρ t τ l) :
    z4iVc K t τ l ⊓ centralizer ((⁅z4iVc K t τ l, z4iVc K t τ l⁆ : Subgroup H) : Set H) = Y := by
  apply le_antisymm
  · intro z hz
    have hzVc : z ∈ z4iVc K t τ l := hz.1
    have hzcent : z ∈ centralizer ((z4iD K t τ l : Subgroup H) : Set H) := hz.2
    have hzD : ∀ d ∈ z4iD K t τ l, d * z = z * d :=
      fun d hd => Subgroup.mem_centralizer_iff.mp hzcent d hd
    have hF : z ∈ z4iF K t τ := cent_D_le_F h hzVc hzD
    obtain ⟨k, hk, a, b, hz'⟩ := (mem_F_iff h).mp hF
    have ha0 : a = 0 := cent_D_cent_t h hzD hk hz'
    have hb0 : b = 0 := cent_D_cent_τ h hzD hk (by rw [hz', ha0]; simp)
    have hzk : z = k := by rw [hz', ha0, hb0]; simp
    rw [hzk]
    exact cent_D_mem_Y h hzD hk hzk
  · intro y hy
    refine ⟨(h.Y_le_Q.trans h.Q_le_K).trans (K_le_Vc K t τ l) hy, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun d hd => h.K_cent_Y d (D_le_K h hd) y hy)

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
