module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Conf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Q
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Data

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

abbrev tau : H := h.a * (d.g⁻¹ * h.a * d.g)

theorem a_mem_Q : h.a ∈ h.Q := mem_inf.mpr ⟨h.toHyp52.a_mem_S, h.a_mem_normalizer⟩

theorem conj_a_mem : d.g⁻¹ * h.a * d.g ∈ h.Q ⊓ h.M3 := by
  have h1 := (mem_normalizer_iff.mp (inv_mem d.g_N) h.a).mp ⟨a_mem_Q, h.toHyp52.a_mem_M3⟩
  rwa [inv_inv] at h1

theorem tau_mem : d.tau ∈ h.Q ⊓ h.M3 :=
  mul_mem ⟨a_mem_Q, h.toHyp52.a_mem_M3⟩ d.conj_a_mem

theorem a_g : d.g⁻¹ * h.a * d.g = h.a * d.tau := by
  rw [tau, ← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]

theorem tau_sq : d.tau * d.tau = 1 := by
  have hc := h.toHyp52.comm_a d.conj_a_mem.1.1
  have haa := Six.a_mul_a_self h.toHyp52
  calc d.tau * d.tau = h.a * h.a * ((d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * h.a * d.g)) := by
        rw [tau, show h.a * (d.g⁻¹ * h.a * d.g) * (h.a * (d.g⁻¹ * h.a * d.g)) =
          h.a * ((d.g⁻¹ * h.a * d.g) * h.a) * (d.g⁻¹ * h.a * d.g) by group, hc]
        group
    _ = 1 := by
        rw [haa, one_mul, show d.g⁻¹ * h.a * d.g * (d.g⁻¹ * h.a * d.g) =
          d.g⁻¹ * (h.a * h.a) * d.g by group, haa]
        group

theorem tau_g : d.g⁻¹ * d.tau * d.g = d.tau := by
  have hg2 := h.toHyp52.comm_a d.g_sq.1
  have h1 : (d.g * d.g)⁻¹ * h.a * (d.g * d.g) = h.a := by
    rw [mul_assoc, ← hg2, inv_mul_cancel_left]
  have key : ∀ u v w : H, w⁻¹ * (u * v) * w = (w⁻¹ * u * w) * (w⁻¹ * v * w) := fun u v w => by
    group
  have h2 : (d.g * d.g)⁻¹ * h.a * (d.g * d.g) =
      (h.a * d.tau) * (d.g⁻¹ * d.tau * d.g) := by
    rw [show (d.g * d.g)⁻¹ * h.a * (d.g * d.g) = d.g⁻¹ * (d.g⁻¹ * h.a * d.g) * d.g by group,
      d.a_g, key, d.a_g]
  rw [h1] at h2
  have h3 : d.g⁻¹ * d.tau * d.g = (h.a * d.tau)⁻¹ * h.a := by
    rw [eq_inv_mul_iff_mul_eq]
    exact h2.symm
  rw [h3, mul_inv_rev, inv_mul_cancel_right]
  exact inv_eq_of_mul_eq_one_right d.tau_sq

theorem isPGroup_Q1 : IsPGroup 2 ↥(h.Q ⊓ h.M3) := h.toHyp52.sec8_isPGroup_Q.to_le inf_le_left

structure Facts : Prop where
  Q1_eq : h.Q ⊓ h.M3 = h.D ⊔ zpowers d.tau ⊔ zpowers h.a
  card_Q1 : Nat.card ↥(h.Q ⊓ h.M3) = 4 * Nat.card h.D
  eight_le : 8 ≤ Nat.card h.D
  tau_comm : ∀ q ∈ h.Q ⊓ h.M3, d.tau * q = q * d.tau
  z_g : d.g⁻¹ * d.z * d.g = d.z
  z_tau : ∃ k ∈ h.M3, k⁻¹ * d.z * k = d.tau

theorem facts (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hJo : CFSec8JOrder)
    (hL0 : CF81L0) (hConf : CF81Conf) : d.Facts := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have L := H₁.kloc
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 L.case8
  have hker := L.not_two_dvd_card_ker_modelHom hCF1 hCF2
  set Q1 : Subgroup ↥h.M3 := h.Q.subgroupOf h.M3 with hQ1
  have hQ1₂ : IsPGroup 2 Q1 := h.toHyp52.sec8_isPGroup_Q.comap_subtype
  set gM : ↥h.M3 := ⟨d.g, d.g_M⟩ with hgM
  have hgN : gM ∈ normalizer (Q1 : Set ↥h.M3) := mem_normalizer_subgroupOf_of_inf d.g_M d.g_N
  have hgsq : gM * gM ∈ Q1 := d.g_sq
  have hT₂ : IsPGroup 2 ↥(Q1 ⊔ zpowers gM) := isPGroup_sup_zpowers hQ1₂ hgN hgsq
  obtain ⟨hQle, hQS⟩ := L.Q1hat_sylow_gen hCF1 hCF2
  have hzM : d.z ∈ h.M3 := L.D_le_M3 d.z_D
  set zM : ↥h.M3 := ⟨d.z, hzM⟩ with hzM'
  have hmapD := L.map_D_eq hCF1 hCF2 hJo hL0
  have hzQ : L.rho zM ∈ Q1.map L.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) L.rhoA := by
    rw [← hmapD]
    exact mem_map_of_mem _ d.z_D
  have hz2 : d.z * d.z = 1 := by rw [← pow_two, ← d.z_ord, pow_orderOf_eq_one]
  have hD2 : IsPGroup 2 (h.D.subgroupOf h.M3) :=
    ((Six.isPGroup_S h.toHyp52).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  have hR2 : IsPGroup 2 ((h.Q ⊓ h.M3).subgroupOf h.M3) := isPGroup_Q1.comap_subtype
  let c : Cat8.QConf (h.K ⧸ pPrimeCore 2 h.K) (p ^ f) := {
    a := L.rhoA
    Q := Q1.map L.rho
    g := L.rho gM
    z := L.rho zM
    adm := L.rhoA_admQ hCF1 hCF2 hJo hp hp2 hf hJ
    Q_le := hQle
    Q_sylow := hQS
    g_inn := L.rho_mem_inn_of_mem_K d.g_K
    g_norm := le_normalizer_map L.rho (mem_map_of_mem _ hgN)
    g_not_mem := fun hg => d.g_Q (Eight.mem_of_map_mem hker hT₂ le_sup_left
      (mem_sup_right (mem_zpowers gM)) hg)
    g_sq := by rw [← map_mul]; exact mem_map_of_mem _ hgsq
    tau_inn := by
      rw [← L.rho_aM, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact L.rho_mem_inn_of_mem_K d.tau_K
    z_mem := hzQ
    z_comm := by
      intro w hw
      rw [← hmapD] at hw
      obtain ⟨e, he, rfl⟩ := mem_map.mp hw
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp d.z_S _ (h.toHyp52.D_le_S he)).symm
    z_sq := by rw [← map_mul, show zM * zM = 1 from Subtype.ext hz2, map_one]
    z_ne := by
      intro h1
      have hzz : zM ∈ h.D.subgroupOf h.M3 := d.z_D
      have h2 := Eight.injOn_of_isPGroup hker hD2 hzz (one_mem _) (h1.trans (map_one _).symm)
      have hz1 : d.z = 1 := congrArg Subtype.val h2
      have := d.z_ord
      rw [hz1, orderOf_one] at this
      exact absurd this (by norm_num) }
  have hc : c.Props := hConf _ p f hp hp2 hf hK c
  have hrho_tau : L.rho ⟨d.tau, d.tau_mem.2⟩ = c.tau := by
    show _ = L.rhoA * ((L.rho gM)⁻¹ * L.rhoA * L.rho gM)
    rw [← L.rho_aM, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hle : h.D ⊔ zpowers d.tau ⊔ zpowers h.a ≤ h.Q ⊓ h.M3 :=
    sup_le (sup_le (le_inf h.toHyp52.sec8_D_le_Q L.D_le_M3) (zpowers_le.mpr d.tau_mem))
      (zpowers_le.mpr ⟨a_mem_Q, h.toHyp52.a_mem_M3⟩)
  have hmapR : ((h.Q ⊓ h.M3).subgroupOf h.M3).map L.rho = c.Q := by
    show _ = Q1.map L.rho
    rw [inf_subgroupOf_right]
  have hmapA : ((h.D ⊔ zpowers d.tau ⊔ zpowers h.a).subgroupOf h.M3).map L.rho = c.Q := by
    rw [subgroupOf_sup_of_le (sup_le L.D_le_M3 (zpowers_le.mpr d.tau_mem.2))
        (zpowers_le.mpr h.toHyp52.a_mem_M3),
      subgroupOf_sup_of_le L.D_le_M3 (zpowers_le.mpr d.tau_mem.2),
      zpowers_subgroupOf d.tau_mem.2, zpowers_subgroupOf h.toHyp52.a_mem_M3, Subgroup.map_sup,
      Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hrho_tau, L.rho_aM, hmapD]
    exact hc.Q_eq.symm
  have hQ1eq : h.Q ⊓ h.M3 = h.D ⊔ zpowers d.tau ⊔ zpowers h.a := by
    have heq := Eight.eq_of_map_eq hker hR2 (fun x hx => hle hx) le_rfl
      (hmapA.trans hmapR.symm)
    have := congrArg (Subgroup.map h.M3.subtype) heq
    rw [map_subgroupOf_eq_of_le (hle.trans inf_le_right),
      map_subgroupOf_eq_of_le inf_le_right] at this
    exact this.symm
  have hcD : Nat.card c.D = Nat.card h.D := by
    show Nat.card ↥(Q1.map L.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) L.rhoA) = _
    rw [← hmapD, Eight.card_map_of_isPGroup hker hD2, Six.card_subgroupOf_eq,
      inf_eq_left.mpr L.D_le_M3]
  have hcQ : Nat.card c.Q = Nat.card ↥(h.Q ⊓ h.M3) := by
    show Nat.card ↥(Q1.map L.rho) = _
    rw [Eight.card_map_of_isPGroup hker hQ1₂, hQ1, Six.card_subgroupOf_eq]
  have hinj : ∀ u v : H, ∀ hu : u ∈ h.Q ⊓ h.M3, ∀ hv : v ∈ h.Q ⊓ h.M3,
      L.rho ⟨u, hu.2⟩ = L.rho ⟨v, hv.2⟩ → u = v := fun u v hu hv huv =>
    congrArg Subtype.val (Eight.injOn_of_isPGroup hker hR2
      (show (⟨u, hu.2⟩ : ↥h.M3) ∈ (h.Q ⊓ h.M3).subgroupOf h.M3 from hu)
      (show (⟨v, hv.2⟩ : ↥h.M3) ∈ (h.Q ⊓ h.M3).subgroupOf h.M3 from hv) huv)
  have hzQ1 : d.z ∈ h.Q ⊓ h.M3 := ⟨h.toHyp52.sec8_D_le_Q d.z_D, hzM⟩
  refine ⟨hQ1eq, by rw [← hcQ, hc.card_Q, hcD], hcD ▸ hc.eight_le, ?_, ?_, ?_⟩
  ·
    intro q hq
    refine hinj _ _ (mul_mem d.tau_mem hq) (mul_mem hq d.tau_mem) ?_
    have h1 := hc.tau_comm (L.rho ⟨q, hq.2⟩) (mem_map_of_mem _ hq.1)
    rw [← hrho_tau] at h1
    rw [show (⟨d.tau * q, (mul_mem d.tau_mem hq).2⟩ : ↥h.M3) = ⟨d.tau, d.tau_mem.2⟩ * ⟨q, hq.2⟩
      from rfl, show (⟨q * d.tau, (mul_mem hq d.tau_mem).2⟩ : ↥h.M3) =
        ⟨q, hq.2⟩ * ⟨d.tau, d.tau_mem.2⟩ from rfl, map_mul, map_mul]
    exact h1
  ·
    have hw : d.g⁻¹ * d.z * d.g ∈ h.Q ⊓ h.M3 := by
      have h1 := (mem_normalizer_iff.mp (inv_mem d.g_N) d.z).mp hzQ1
      rwa [inv_inv] at h1
    refine hinj _ _ hw hzQ1 ?_
    have h1 := hc.g_z
    rw [show (⟨d.g⁻¹ * d.z * d.g, hw.2⟩ : ↥h.M3) = gM⁻¹ * zM * gM from rfl, map_mul, map_mul,
      map_inv]
    exact h1
  ·
    obtain ⟨k, hk, hkz⟩ := hc.z_tau
    have hkR : k ∈ L.rho.range := by
      rw [L.rho_range_eq]
      exact mem_sup_left hk
    obtain ⟨kM, rfl⟩ := hkR
    have hτ2 : (⟨d.tau, d.tau_mem.2⟩ : ↥h.M3) * ⟨d.tau, d.tau_mem.2⟩ = 1 :=
      Subtype.ext d.tau_sq
    have hz2' : zM * zM = 1 := Subtype.ext hz2
    obtain ⟨c', -, hc'⟩ := Eight.exists_conj_eq_of_map hker (isPGroup_zpowers_of_mul_self hz2')
      (isPGroup_zpowers_of_mul_self hτ2) kM (by rw [hrho_tau]; exact hkz.symm)
    exact ⟨(c' : H), c'.2, (congrArg Subtype.val hc').symm⟩

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
