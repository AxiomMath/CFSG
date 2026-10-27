module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Facts
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bL34Tools

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem b_mem_B : d.b ∈ h.B := d.B_eq ▸ mem_zpowers d.b

theorem b_mem_P : d.b ∈ h.P := h.B_le d.b_mem_B

theorem b_mem_S : d.b ∈ h.S := (mem_inf.mp d.b_mem_P).1

theorem b_mem_Q : d.b ∈ h.Q := mem_inf.mpr ⟨d.b_mem_S, le_normalizer d.b_mem_B⟩

theorem b_mul_self : d.b * d.b = 1 := by rw [← pow_two, ← d.b_ord, pow_orderOf_eq_one]

theorem a_comm_b : h.a * d.b = d.b * h.a := (h.toHyp52.comm_a d.b_mem_S).symm

theorem comm_b_of_mem_Q {q : H} (hq : q ∈ h.Q) : q * d.b = d.b * q :=
  comm_of_mem_normalizer_zpowers d.b_ord (d.B_eq ▸ (mem_inf.mp hq).2)

theorem b_not_mem_M3 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.b ∉ h.M3 := by
  intro hbM
  have L := H₁.kloc
  have hker := L.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hbK : d.b ∈ coreActionKernel h.K := by
    have := L.B_sylow_kernel.1 d.b_mem_B
    rwa [L.V_eq_K] at this
  have hbQ1 : d.b ∈ h.Q ⊓ h.M3 := ⟨d.b_mem_Q, hbM⟩
  have hR2 : IsPGroup 2 ((h.Q ⊓ h.M3).subgroupOf h.M3) := isPGroup_Q1.comap_subtype
  have h1 : (⟨d.b, hbM⟩ : ↥h.M3) = 1 := by
    refine Eight.injOn_of_isPGroup hker hR2
      (show (⟨d.b, hbM⟩ : ↥h.M3) ∈ (h.Q ⊓ h.M3).subgroupOf h.M3 from hbQ1) (one_mem _) ?_
    have h2 : (⟨d.b, L.normalizer_le_normalizer_K (le_normalizer d.b_mem_B)⟩ :
        normalizer (h.K : Set H)) ∈ (Eight.oddBarAction h.K).ker :=
      Eight.mem_ker_oddBarAction.mpr hbK
    rw [MonoidHom.mem_ker] at h2
    show _ = L.rho 1
    rw [map_one]
    exact h2
  have h3 : d.b = 1 := congrArg Subtype.val h1
  have := d.b_ord
  rw [h3, orderOf_one] at this
  exact absurd this (by norm_num)

theorem a_ne_one' : h.a ≠ 1 := by
  intro h1
  have := h.orderOf_a
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem tau_mem_Q : d.tau ∈ h.Q := d.tau_mem.1

theorem tau_mem_S : d.tau ∈ h.S := (mem_inf.mp d.tau_mem_Q).1

theorem tau_comm_a : d.tau * h.a = h.a * d.tau := h.toHyp52.comm_a d.tau_mem_S

theorem tau_comm_b : d.tau * d.b = d.b * d.tau := d.comm_b_of_mem_Q d.tau_mem_Q

theorem T_le_centralizer_tau : h.T ≤ centralizer ({d.tau} : Set H) := by
  rw [d.T_eq]
  refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
  · exact mem_centralizer_singleton_iff.mpr d.tau_comm_a.symm
  · exact mem_centralizer_singleton_iff.mpr d.tau_comm_b.symm

theorem tau_not_mem_P (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    d.tau ∉ h.P := by
  intro hτP
  have hτT : d.tau ∈ h.T := mem_inf.mpr ⟨d.tau_mem_Q, hτP⟩
  have hτa : d.tau ∈ zpowers h.a := by
    rcases h.mem_T_cases d.b_ord d.T_eq d.a_comm_b hτT with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers _
    · exact absurd (h1 ▸ d.tau_mem.2) (d.b_not_mem_M3 hCF1 hCF2)
    · exfalso
      apply d.b_not_mem_M3 hCF1 hCF2
      have := mul_mem (inv_mem h.toHyp52.a_mem_M3) (h1 ▸ d.tau_mem.2)
      rwa [inv_mul_cancel_left] at this
  have hle : h.Q ⊓ h.M3 ≤ h.D ⊔ zpowers h.a := by
    rw [F.Q1_eq]
    exact sup_le (sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hτa))) le_sup_right
  have hc : ∀ u ∈ h.D, ∀ v ∈ zpowers h.a, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (h.toHyp52.comm_a (h.toHyp52.D_le_S hu)) k).eq
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.D (zpowers h.a) hc).1
  rw [Nat.card_zpowers, h.orderOf_a] at h1
  have h2 := card_le_of_le hle
  rw [F.card_Q1] at h2
  have h3 : Nat.card ↥(h.D ⊔ zpowers h.a) ≤ Nat.card h.D * 2 := by
    rw [← h1]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have h4 := F.eight_le
  omega

theorem x_not_mem_Q : h.x ∉ h.Q := by
  intro hxQ
  have hxN : h.x ∈ normalizer (h.B : Set H) := (mem_inf.mp hxQ).2
  apply h.B_ne_bot
  rw [← h.inf_conjugate_x]
  symm
  rw [inf_eq_left]
  intro y hy
  rw [mem_conjugate_iff]
  exact (mem_normalizer_iff.mp hxN y).mp hy

theorem x_sq_comm_tau : h.x * h.x * d.tau = d.tau * (h.x * h.x) := by
  have hx2 : h.x * h.x ∈ h.T := by
    have h0 := h.x_sq_mem
    rw [pow_two] at h0
    obtain ⟨⟨hS, hC⟩, hN⟩ := h0
    exact ⟨⟨hS, hN⟩, ⟨hS, hC⟩⟩
  exact (mem_centralizer_singleton_iff.mp (d.T_le_centralizer_tau hx2))

theorem tau_x (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    h.x⁻¹ * d.tau * h.x = h.a * d.tau := by
  have hxPN := H₁.x_mem_P
  have hxP : h.x ∈ h.P := (mem_inf.mp hxPN).1
  have hxN : h.x ∈ normalizer (h.Q : Set H) := (mem_inf.mp hxPN).2
  have hxb := h.conj_x_b d.B_eq d.b_ord d.T_eq
  set w := h.x⁻¹ * d.tau * h.x with hw
  have hwQ : w ∈ h.Q := by
    have := (mem_normalizer_iff.mp (inv_mem hxN) d.tau).mp d.tau_mem_Q
    rwa [inv_inv] at this
  have hwT : w * d.tau⁻¹ ∈ h.T := by
    refine mem_inf.mpr ⟨mul_mem hwQ (inv_mem d.tau_mem_Q), mem_inf.mpr
      ⟨mul_mem (mem_inf.mp hwQ).1 (inv_mem d.tau_mem_S), ?_⟩⟩
    have hxC : h.x ∈ coreActionKernel h.J := (mem_inf.mp hxP).2
    have hτN : d.tau ∈ normalizer (h.J : Set H) := h.toHyp52.S_le_normalizer d.tau_mem_S
    have h1 := conj_mem_coreActionKernel (inv_mem hτN) hxC
    rw [inv_inv] at h1
    have h2 : w * d.tau⁻¹ = h.x⁻¹ * (d.tau * h.x * d.tau⁻¹) := by rw [hw]; group
    rw [h2]
    exact mul_mem (inv_mem hxC) h1
  have hx2 := d.x_sq_comm_tau
  have hww : h.x⁻¹ * w * h.x = d.tau := by
    rw [hw, show h.x⁻¹ * (h.x⁻¹ * d.tau * h.x) * h.x = (h.x * h.x)⁻¹ * d.tau * (h.x * h.x) by
      group, mul_assoc, ← hx2, inv_mul_cancel_left]
  have hxa : h.x⁻¹ * h.a * h.x = h.a := by
    rw [mul_assoc, ← h.toHyp52.comm_a h.x_mem, inv_mul_cancel_left]
  have hxab : h.x⁻¹ * (h.a * d.b) * h.x = d.b := by
    rw [show h.x⁻¹ * (h.a * d.b) * h.x = (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * d.b * h.x) by group,
      hxa, hxb, ← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]
  have hτ1 : d.tau ≠ 1 := fun h1 => d.tau_not_mem_P hCF1 hCF2 F (h1 ▸ one_mem _)
  rcases h.mem_T_cases d.b_ord d.T_eq d.a_comm_b hwT with h1 | h1 | h1 | h1
  ·
    exfalso
    have hwτ : w = d.tau := by rw [← mul_inv_eq_one, h1]
    have hxτ : h.x * d.tau = d.tau * h.x := by
      calc h.x * d.tau = h.x * w := by rw [hwτ]
        _ = d.tau * h.x := by rw [hw]; group
    have hgW : d.g ∈ h.W := h.isPComponent_K.1 d.g_K
    have hgS : d.g⁻¹ * h.a * d.g ∈ h.S := (mem_inf.mp d.conj_a_mem.1).1
    have hgP : d.g⁻¹ * h.a * d.g ∉ h.P := by
      rw [d.a_g]
      intro h2
      apply d.tau_not_mem_P hCF1 hCF2 F
      have := mul_mem (inv_mem h.toHyp52.a_mem_P) h2
      rwa [inv_mul_cancel_left] at this
    have hle := h.toHyp52.centralizer_conj_le_Q hB1 hB6 hCF23 hCF24 hCFc hgW hgS hgP
    apply x_not_mem_Q (h := h)
    refine hle (mem_inf.mpr ⟨h.x_mem, ?_⟩)
    rw [mem_centralizer_singleton_iff, d.a_g]
    calc h.x * (h.a * d.tau) = (h.x * h.a) * d.tau := by group
      _ = (h.a * h.x) * d.tau := by rw [h.toHyp52.comm_a h.x_mem]
      _ = h.a * (h.x * d.tau) := by group
      _ = h.a * (d.tau * h.x) := by rw [hxτ]
      _ = h.a * d.tau * h.x := by group
  ·
    calc w = w * d.tau⁻¹ * d.tau := by group
      _ = h.a * d.tau := by rw [h1]
  ·
    exfalso
    have hw' : w = d.b * d.tau := by
      calc w = w * d.tau⁻¹ * d.tau := by group
        _ = d.b * d.tau := by rw [h1]
    have h2 : h.x⁻¹ * w * h.x = h.a * d.b * (d.b * d.tau) := by
      rw [hw', show h.x⁻¹ * (d.b * d.tau) * h.x = (h.x⁻¹ * d.b * h.x) * (h.x⁻¹ * d.tau * h.x) by
        group, hxb, ← hw, hw']
    rw [hww, show h.a * d.b * (d.b * d.tau) = h.a * (d.b * d.b) * d.tau by group,
      d.b_mul_self, mul_one] at h2
    apply a_ne_one' (h := h)
    calc h.a = h.a * d.tau * d.tau⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]
  ·
    exfalso
    have hw' : w = h.a * d.b * d.tau := by
      calc w = w * d.tau⁻¹ * d.tau := by group
        _ = h.a * d.b * d.tau := by rw [h1]
    have h2 : h.x⁻¹ * w * h.x = d.b * (h.a * d.b * d.tau) := by
      rw [hw', show h.x⁻¹ * (h.a * d.b * d.tau) * h.x =
        (h.x⁻¹ * (h.a * d.b) * h.x) * (h.x⁻¹ * d.tau * h.x) by group, hxab, ← hw, hw']
    rw [hww, show d.b * (h.a * d.b * d.tau) = (d.b * h.a) * d.b * d.tau by group,
      ← d.a_comm_b, show h.a * d.b * d.b * d.tau = h.a * (d.b * d.b) * d.tau by group,
      d.b_mul_self, mul_one] at h2
    apply a_ne_one' (h := h)
    calc h.a = h.a * d.tau * d.tau⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]

theorem x_conj_a : h.x⁻¹ * h.a * h.x = h.a := by
  rw [mul_assoc, ← h.toHyp52.comm_a h.x_mem, inv_mul_cancel_left]

theorem conj_a_tau (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    (d.g * h.x)⁻¹ * h.a * (d.g * h.x) = d.tau := by
  rw [show (d.g * h.x)⁻¹ * h.a * (d.g * h.x) = h.x⁻¹ * (d.g⁻¹ * h.a * d.g) * h.x by group,
    d.a_g, show h.x⁻¹ * (h.a * d.tau) * h.x = (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * d.tau * h.x) by
      group, x_conj_a, d.tau_x hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F, ← mul_assoc,
    Six.a_mul_a_self h.toHyp52, one_mul]

theorem exists_conj_a_z (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) : ∃ c : H, c⁻¹ * h.a * c = d.z := by
  obtain ⟨k, -, hk⟩ := F.z_tau
  refine ⟨d.g * h.x * k⁻¹, ?_⟩
  rw [show (d.g * h.x * k⁻¹)⁻¹ * h.a * (d.g * h.x * k⁻¹) =
      k * ((d.g * h.x)⁻¹ * h.a * (d.g * h.x)) * k⁻¹ by group,
    d.conj_a_tau hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F, ← hk]
  group

theorem x_b_x_inv : h.x * d.b * h.x⁻¹ = h.a * d.b := by
  have hx2 : h.x * h.x ∈ h.Q := by
    have h0 := h.x_sq_mem
    rw [pow_two] at h0
    obtain ⟨⟨hS, -⟩, hN⟩ := h0
    exact ⟨hS, hN⟩
  have hc := d.comm_b_of_mem_Q hx2
  rw [← h.conj_x_b d.B_eq d.b_ord d.T_eq]
  calc h.x * d.b * h.x⁻¹ = h.x⁻¹ * ((h.x * h.x) * d.b) * h.x⁻¹ := by group
    _ = h.x⁻¹ * (d.b * (h.x * h.x)) * h.x⁻¹ := by rw [hc]
    _ = h.x⁻¹ * d.b * h.x := by group

include d in
theorem a_mem_commutator : h.a ∈ ⁅h.S, h.S⁆ := by
  have h1 : ⁅h.x, d.b⁆ = h.a := by
    rw [commutatorElement_def, d.x_b_x_inv, inv_eq_of_mul_eq_one_right d.b_mul_self,
      mul_assoc, d.b_mul_self, mul_one]
  rw [← h1]
  exact commutator_mem_commutator h.x_mem d.b_mem_S

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
