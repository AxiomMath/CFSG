module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Orb
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace E6

theorem mul_mul_self_of_comm {G : Type*} [Group G] {x y w : G} (hx : x * x = 1) (hy : y * y = 1)
    (hw : w * w = 1) (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y) :
    x * y * w * (x * y * w) = 1 := by
  calc x * y * w * (x * y * w) = x * y * (w * x) * y * w := by group
    _ = x * y * (x * w) * y * w := by rw [← hxw]
    _ = x * (y * x) * w * y * w := by group
    _ = x * (x * y) * w * y * w := by rw [← hxy]
    _ = x * x * y * (w * y) * w := by group
    _ = x * x * y * (y * w) * w := by rw [← hyw]
    _ = (x * x) * (y * y) * (w * w) := by group
    _ = 1 := by rw [hx, hy, hw]; group

theorem mul_mul_self_of_comm₂ {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [← hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

end E6

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem exists_e6Conf (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) (hL0 : CF81L0) :
    ∃ (p f : ℕ) (c : Cat8.QConf (h.K ⧸ pPrimeCore 2 h.K) (p ^ f)), p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      IsSec8Socle (h.K ⧸ pPrimeCore 2 h.K) p f ∧ c.a = H₁.kloc.rhoA ∧
      c.z = H₁.kloc.rho ⟨d.z, H₁.kloc.D_le_M3 d.z_D⟩ ∧
      c.tau = H₁.kloc.rho ⟨d.tau, d.tau_mem.2⟩ ∧ Nat.card c.D = Nat.card h.D := by
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
  refine ⟨p, f, c, hp, hp2, hf, hK, rfl, rfl, ?_, ?_⟩
  · show L.rhoA * ((L.rho gM)⁻¹ * L.rhoA * L.rho gM) = _
    rw [← L.rho_aM, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  · show Nat.card ↥(Q1.map L.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) L.rhoA) = _
    rw [← hmapD, Eight.card_map_of_isPGroup hker hD2, Six.card_subgroupOf_eq,
      inf_eq_left.mpr fun e he => L.D_le_M3 he]

theorem e6_inv_cases (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) (hL0 : CF81L0) (hCls : CF81E6Cls) (F : d.Facts) {w : H}
    (hwM : w ∈ h.M3) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    ∃ m ∈ h.M3, m⁻¹ * w * m = h.a ∨ m⁻¹ * w * m = d.z ∨
      m⁻¹ * w * m = h.a * d.z * d.tau ∨ m⁻¹ * w * m = d.z * d.tau := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H₁.kloc.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨p, f, c, hp, hp2, hf, hK, hca, hcz, hct, -⟩ := d.exists_e6Conf hCF1 hCF2 hJo hL0
  set wM : ↥h.M3 := ⟨w, hwM⟩ with hwM'
  have hwM2 : wM * wM = 1 := Subtype.ext hw2
  have hρw : H₁.kloc.rho wM ∈ Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) c.a := by
    have h1 : H₁.kloc.rho wM ∈ H₁.kloc.rho.range := ⟨wM, rfl⟩
    rw [H₁.kloc.rho_range_eq] at h1
    rw [hca]
    exact h1
  have hρw2 : H₁.kloc.rho wM * H₁.kloc.rho wM = 1 := by rw [← map_mul, hwM2, map_one]
  have hρw1 : H₁.kloc.rho wM ≠ 1 := by
    intro h1
    have h2 := Eight.injOn_of_isPGroup hker (isPGroup_zpowers_of_mul_self hwM2)
      (mem_zpowers wM) (one_mem _) (h1.trans (map_one _).symm)
    exact hw1 (congrArg Subtype.val h2)
  obtain ⟨n, hn, hcase⟩ := hCls _ p f hp hp2 hf hK c (H₁.kloc.rho wM) hρw hρw2 hρw1
  have hnR : n ∈ H₁.kloc.rho.range := by
    rw [H₁.kloc.rho_range_eq]
    rw [hca] at hn
    exact hn
  obtain ⟨mM, rfl⟩ := hnR
  have haM : h.a ∈ h.M3 := h.toHyp52.a_mem_M3
  have hzM : d.z ∈ h.M3 := H₁.kloc.D_le_M3 d.z_D
  have htM : d.tau ∈ h.M3 := d.tau_mem.2
  have hz2 : d.z * d.z = 1 := by rw [← pow_two, ← d.z_ord, pow_orderOf_eq_one]
  have haz : h.a * d.z = d.z * h.a := (d.z_comm_a).symm
  have hat : h.a * d.tau = d.tau * h.a := (d.tau_comm_a).symm
  have hzt : d.z * d.tau = d.tau * d.z :=
    (F.tau_comm d.z ⟨h.toHyp52.sec8_D_le_Q d.z_D, hzM⟩).symm
  have haa : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
  have htt : d.tau * d.tau = 1 := d.tau_sq
  have lift : ∀ r : H, ∀ hr : r ∈ h.M3, r * r = 1 →
      H₁.kloc.rho ⟨r, hr⟩ = (H₁.kloc.rho mM)⁻¹ * H₁.kloc.rho wM * H₁.kloc.rho mM →
      ∃ m ∈ h.M3, m⁻¹ * w * m = r := by
    intro r hr hr2 hrr
    have hrM2 : (⟨r, hr⟩ : ↥h.M3) * ⟨r, hr⟩ = 1 := Subtype.ext hr2
    obtain ⟨c', -, hc'⟩ := Eight.exists_conj_eq_of_map hker (isPGroup_zpowers_of_mul_self hwM2)
      (isPGroup_zpowers_of_mul_self hrM2) mM hrr
    exact ⟨c', c'.2, (congrArg Subtype.val hc').symm⟩
  rcases hcase with h1 | h1 | h1 | h1
  · obtain ⟨m, hm, hmw⟩ := lift h.a haM haa (by rw [h1, hca])
    exact ⟨m, hm, Or.inl hmw⟩
  · obtain ⟨m, hm, hmw⟩ := lift d.z hzM hz2 (by rw [h1, hcz])
    exact ⟨m, hm, Or.inr (Or.inl hmw)⟩
  · have hr2 := E6.mul_mul_self_of_comm haa hz2 htt haz hat hzt
    obtain ⟨m, hm, hmw⟩ := lift (h.a * d.z * d.tau) (mul_mem (mul_mem haM hzM) htM) hr2 (by
      rw [h1, hca, hcz, hct, ← H₁.kloc.rho_aM, ← map_mul, ← map_mul]
      rfl)
    exact ⟨m, hm, Or.inr (Or.inr (Or.inl hmw))⟩
  · have hr2 := E6.mul_mul_self_of_comm₂ hz2 htt hzt
    obtain ⟨m, hm, hmw⟩ := lift (d.z * d.tau) (mul_mem hzM htM) hr2 (by
      rw [h1, hcz, hct, ← map_mul]
      rfl)
    exact ⟨m, hm, Or.inr (Or.inr (Or.inr hmw))⟩

theorem e6_conj_a_or_az (I : In81) (hJo : CFSec8JOrder) (hL0 : CF81L0) (hCls : CF81E6Cls)
    (F : d.Facts) {w : H} (hwM : w ∈ h.M3) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    (∃ c : H, c⁻¹ * w * c = h.a) ∨ ∃ c : H, c⁻¹ * w * c = h.a * d.z := by
  obtain ⟨m, -, hm⟩ := d.e6_inv_cases I.cf1 I.cf2 hJo hL0 hCls F hwM hw2 hw1
  obtain ⟨c₀, hc₀⟩ := d.exists_conj_a_z I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  have hτx := d.tau_x I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  have hzM : d.z ∈ h.M3 := H₁.kloc.D_le_M3 d.z_D
  have haz : h.a * d.z = d.z * h.a := (d.z_comm_a).symm
  have hzt : d.z * d.tau = d.tau * d.z :=
    (F.tau_comm d.z ⟨h.toHyp52.sec8_D_le_Q d.z_D, hzM⟩).symm
  have hg_az : d.g⁻¹ * (h.a * d.z) * d.g = h.a * d.z * d.tau := by
    rw [show d.g⁻¹ * (h.a * d.z) * d.g = (d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * d.z * d.g) by group,
      d.a_g, F.z_g, mul_assoc, ← hzt, ← mul_assoc]
  have hx_zt : h.x⁻¹ * (d.z * d.tau) * h.x = h.a * d.z * d.tau := by
    rw [show h.x⁻¹ * (d.z * d.tau) * h.x = (h.x⁻¹ * d.z * h.x) * (h.x⁻¹ * d.tau * h.x) by group,
      x_inv_z_x, hτx, ← mul_assoc, ← haz]
  rcases hm with h1 | h1 | h1 | h1
  · exact Or.inl ⟨m, h1⟩
  · refine Or.inl ⟨m * c₀⁻¹, ?_⟩
    calc (m * c₀⁻¹)⁻¹ * w * (m * c₀⁻¹) = c₀ * (m⁻¹ * w * m) * c₀⁻¹ := by group
      _ = c₀ * (c₀⁻¹ * h.a * c₀) * c₀⁻¹ := by rw [h1, ← hc₀]
      _ = h.a := by group
  · refine Or.inr ⟨m * d.g⁻¹, ?_⟩
    calc (m * d.g⁻¹)⁻¹ * w * (m * d.g⁻¹) = d.g * (m⁻¹ * w * m) * d.g⁻¹ := by group
      _ = d.g * (d.g⁻¹ * (h.a * d.z) * d.g) * d.g⁻¹ := by rw [h1, ← hg_az]
      _ = h.a * d.z := by group
  · refine Or.inr ⟨m * h.x * d.g⁻¹, ?_⟩
    calc (m * h.x * d.g⁻¹)⁻¹ * w * (m * h.x * d.g⁻¹) =
        d.g * (h.x⁻¹ * (m⁻¹ * w * m) * h.x) * d.g⁻¹ := by group
      _ = d.g * (d.g⁻¹ * (h.a * d.z) * d.g) * d.g⁻¹ := by rw [h1, hx_zt, ← hg_az]
      _ = h.a * d.z := by group

variable {d} in
theorem e6_not_conj_b_M3 {v : H} (hv : d.IsV v) (I : In81) (hJo : CFSec8JOrder)
    (hL0 : CF81L0) (hCls : CF81E6Cls) (F : d.Facts) (g : H) : g⁻¹ * d.b * g ∉ h.M3 := by
  intro hg
  have hb2 : g⁻¹ * d.b * g * (g⁻¹ * d.b * g) = 1 := by
    rw [show g⁻¹ * d.b * g * (g⁻¹ * d.b * g) = g⁻¹ * (d.b * d.b) * g by group, d.b_mul_self]
    group
  have hb1 : g⁻¹ * d.b * g ≠ 1 := by
    intro h1
    have : d.b = 1 := by
      calc d.b = g * (g⁻¹ * d.b * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h2 := d.b_ord
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  rcases d.e6_conj_a_or_az I hJo hL0 hCls F hg hb2 hb1 with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply not_conj_a_b hv I F (g * c)⁻¹
    calc (g * c)⁻¹⁻¹ * h.a * (g * c)⁻¹ = (g * c) * (c⁻¹ * (g⁻¹ * d.b * g) * c) * (g * c)⁻¹ := by
          rw [hc, inv_inv]
      _ = d.b := by group
  · apply not_conj_az_b hv I F (g * c)⁻¹
    calc (g * c)⁻¹⁻¹ * (h.a * d.z) * (g * c)⁻¹ =
        (g * c) * (c⁻¹ * (g⁻¹ * d.b * g) * c) * (g * c)⁻¹ := by rw [hc, inv_inv]
      _ = d.b := by group

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
