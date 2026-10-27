module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Data
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem subgroupOf_sup_of_le {G : Type*} [Group G] {A B M : Subgroup G} (hA : A ≤ M)
    (hB : B ≤ M) : (A ⊔ B).subgroupOf M = A.subgroupOf M ⊔ B.subgroupOf M := by
  apply map_injective M.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hA hB), map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le hB]

theorem zpowers_subgroupOf {G : Type*} [Group G] {M : Subgroup G} {x : G} (hx : x ∈ M) :
    (zpowers x).subgroupOf M = zpowers (⟨x, hx⟩ : M) := by
  apply map_injective M.subtype_injective
  rw [map_subgroupOf_eq_of_le (zpowers_le.mpr hx), MonoidHom.map_zpowers]
  rfl

theorem mem_zpowers_two {G : Type*} [Group G] {b y : G} (hb : orderOf b = 2)
    (hy : y ∈ zpowers b) : y = 1 ∨ y = b := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hb]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [Nat.cast_ofNat, h0, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h1, zpow_one]

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

theorem a_mem_Q (H : L83Hyp h) : h.a ∈ h.Q :=
  ⟨(Six.a_mem_P H.C_eq).1, h.a_mem_normalizer⟩

theorem isPGroup_Q1 : IsPGroup 2 ↥(h.Q ⊓ h.M3) := h.sec8_isPGroup_Q.to_le inf_le_left

theorem comm_a_of_mem_Q (H : L83Hyp h) {q : X} (hq : q ∈ h.Q) : q * h.a = h.a * q :=
  Six.comm_a H.C_eq hq.1

theorem Q_le_normalizer_K (H : L83Hyp h) : h.Q ≤ normalizer (h.K : Set X) :=
  inf_le_right.trans H.normalizer_le_normalizer_K

theorem Q_inf_kernel (H : L83Hyp h) : h.Q ⊓ coreActionKernel h.K = h.B := by
  obtain ⟨hBV, hBS⟩ := H.B_sylow_kernel
  rw [H.V_eq_K] at hBV hBS
  have hBQ : h.B ≤ h.Q := le_inf (h.B_le.trans inf_le_left) le_normalizer
  exact eq_of_sylow_of_le hBS (le_inf hBQ hBV) inf_le_right (h.sec8_isPGroup_Q.to_le inf_le_left)

theorem a_not_mem_K (H : L83Hyp h) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    h.a ∉ h.K := by
  intro haK
  exact H.rhoA_not_mem_inner hCF1 hCF2 ((H.mem_K_iff hCF1 hCF2 h.aM).mp haK)

namespace Q3Data

variable (d : Q3Data H)
include d

abbrev tau : X := h.a * (d.g⁻¹ * h.a * d.g)

theorem conj_a_mem : d.g⁻¹ * h.a * d.g ∈ h.Q ⊓ h.M3 := by
  have h1 := (mem_normalizer_iff.mp (inv_mem d.g_norm) h.a).mp ⟨H.a_mem_Q, h.a_mem_M3⟩
  rwa [inv_inv] at h1

theorem tau_mem : d.tau ∈ h.Q ⊓ h.M3 :=
  mul_mem ⟨H.a_mem_Q, h.a_mem_M3⟩ d.conj_a_mem

theorem a_g : d.g⁻¹ * h.a * d.g = h.a * d.tau := by
  rw [tau, ← mul_assoc, Six.a_mul_a_self h, one_mul]

theorem tau_comm_a : d.tau * h.a = h.a * d.tau := H.comm_a_of_mem_Q d.tau_mem.1

theorem tau_sq : d.tau * d.tau = 1 := by
  have hc := H.comm_a_of_mem_Q d.conj_a_mem.1
  have haa := Six.a_mul_a_self h
  calc d.tau * d.tau = h.a * h.a * ((d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * h.a * d.g)) := by
        rw [tau, show h.a * (d.g⁻¹ * h.a * d.g) * (h.a * (d.g⁻¹ * h.a * d.g)) =
          h.a * ((d.g⁻¹ * h.a * d.g) * h.a) * (d.g⁻¹ * h.a * d.g) by group, hc]
        group
    _ = 1 := by
        rw [haa, one_mul, show d.g⁻¹ * h.a * d.g * (d.g⁻¹ * h.a * d.g) =
          d.g⁻¹ * (h.a * h.a) * d.g by group, haa]
        group

theorem isPGroup_RM : IsPGroup 2 d.RM := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := d.RM_sylow
  have h1 := T.isPGroup'.map h.M3.subtype
  rwa [hT, subgroupOf_map_subtype, inf_eq_left.mpr d.RM_le] at h1

theorem Q1_le_RM : h.Q ⊓ h.M3 ≤ d.RM := le_sup_left.trans d.Q1g_le

theorem g_mem_RM : d.g ∈ d.RM := d.Q1g_le (mem_sup_right (mem_zpowers _))

theorem rho_inj (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {u v : X} (hu : u ∈ d.RM)
    (hv : v ∈ d.RM) (huv : H.rho ⟨u, d.RM_le hu⟩ = H.rho ⟨v, d.RM_le hv⟩) : u = v := by
  have h2 : IsPGroup 2 (d.RM.subgroupOf h.M3) := d.isPGroup_RM.comap_subtype
  have := Eight.injOn_of_isPGroup (H.not_two_dvd_card_ker_modelHom hCF1 hCF2) h2
    (show (⟨u, d.RM_le hu⟩ : ↥h.M3) ∈ d.RM.subgroupOf h.M3 from hu)
    (show (⟨v, d.RM_le hv⟩ : ↥h.M3) ∈ d.RM.subgroupOf h.M3 from hv) huv
  exact congrArg Subtype.val this

theorem rho_tau : H.rho ⟨d.tau, d.tau_mem.2⟩ = d.c.tau := by
  rw [Cat8.Q3Conf.tau, d.c_a, d.c_g, ← H.rho_aM]
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rfl

theorem z_g (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    d.g⁻¹ * d.z * d.g = d.z := by
  have hzRM : d.z ∈ d.RM := d.Q1_le_RM ⟨h.sec8_D_le_Q d.z_D, H.D_le_M3 d.z_D⟩
  have hgRM := d.g_mem_RM
  have hw : d.g⁻¹ * d.z * d.g ∈ d.RM := mul_mem (mul_mem (inv_mem hgRM) hzRM) hgRM
  refine d.rho_inj hCF1 hCF2 hw hzRM ?_
  have h1 := d.c_props.g_z
  rw [d.c_g, d.c_z] at h1
  rw [← h1, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem tau_g : d.g⁻¹ * d.tau * d.g = d.tau := by
  have haa := Six.a_mul_a_self h
  have hg2 := H.comm_a_of_mem_Q d.g_sq
  have h1 : (d.g * d.g)⁻¹ * h.a * (d.g * d.g) = h.a := by
    rw [mul_assoc, ← hg2, ← mul_assoc, inv_mul_cancel, one_mul]
  have key : ∀ u v w : X, w⁻¹ * (u * v) * w = (w⁻¹ * u * w) * (w⁻¹ * v * w) := fun u v w => by
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

theorem tau_comm_Q1 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {q : X}
    (hq : q ∈ h.Q ⊓ h.M3) : d.tau * q = q * d.tau := by
  have hqR := d.Q1_le_RM hq
  have htR := d.Q1_le_RM d.tau_mem
  refine d.rho_inj hCF1 hCF2 (mul_mem htR hqR) (mul_mem hqR htR) ?_
  have h1 := d.c_props.tau_comm (H.rho ⟨q, hq.2⟩) (by rw [d.c_Q]; exact mem_map_of_mem _ hq.1)
  rw [← d.rho_tau] at h1
  rw [show (⟨d.tau * q, _⟩ : ↥h.M3) = ⟨d.tau, d.tau_mem.2⟩ * ⟨q, hq.2⟩ from rfl,
    show (⟨q * d.tau, _⟩ : ↥h.M3) = ⟨q, hq.2⟩ * ⟨d.tau, d.tau_mem.2⟩ from rfl, map_mul, map_mul]
  exact h1

theorem Q1_eq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hq : h.IsQ3)
    (hL0 : CFQ3L0) : h.Q ⊓ h.M3 = h.D ⊔ zpowers d.tau ⊔ zpowers h.a := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hle : h.D ⊔ zpowers d.tau ⊔ zpowers h.a ≤ h.Q ⊓ h.M3 :=
    sup_le (sup_le (le_inf h.sec8_D_le_Q H.D_le_M3) (zpowers_le.mpr d.tau_mem))
      (zpowers_le.mpr ⟨H.a_mem_Q, h.a_mem_M3⟩)
  have hR2 : IsPGroup 2 ((h.Q ⊓ h.M3).subgroupOf h.M3) := isPGroup_Q1.comap_subtype
  have hmapR : ((h.Q ⊓ h.M3).subgroupOf h.M3).map H.rho = d.c.Q := by
    rw [d.c_Q, inf_subgroupOf_right]
  have hmapA : ((h.D ⊔ zpowers d.tau ⊔ zpowers h.a).subgroupOf h.M3).map H.rho = d.c.Q := by
    rw [subgroupOf_sup_of_le (sup_le H.D_le_M3 (zpowers_le.mpr d.tau_mem.2))
        (zpowers_le.mpr h.a_mem_M3),
      subgroupOf_sup_of_le H.D_le_M3 (zpowers_le.mpr d.tau_mem.2),
      zpowers_subgroupOf d.tau_mem.2, zpowers_subgroupOf h.a_mem_M3, Subgroup.map_sup,
      Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, d.rho_tau, H.rho_aM,
      H.map_D_eq hq hCF1 hCF2 hL0, ← d.c_Q, ← d.c_a]
    exact d.c_props.Q_eq.symm
  have heq := Eight.eq_of_map_eq hker hR2 (fun x hx => hle hx) le_rfl (hmapA.trans hmapR.symm)
  have := congrArg (Subgroup.map h.M3.subtype) heq
  rw [map_subgroupOf_eq_of_le (hle.trans inf_le_right),
    map_subgroupOf_eq_of_le inf_le_right] at this
  exact this.symm

theorem map_Q_eq :
    (h.Q.subgroupOf (normalizer (h.K : Set X))).map (Eight.oddBarAction h.K) = d.c.Q := by
  have hle : d.c.Q ≤ (h.Q.subgroupOf (normalizer (h.K : Set X))).map (Eight.oddBarAction h.K) := by
    rw [d.c_Q]
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨⟨(m : X), H.Q_le_normalizer_K hm⟩, hm, rfl⟩
  have hC : (h.Q.subgroupOf (normalizer (h.K : Set X))).map (Eight.oddBarAction h.K) ≤
      centralizer ({d.c.a} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff, d.c_a]
    have hqa := H.comm_a_of_mem_Q (show (q : X) ∈ h.Q from hq)
    have haN : h.a ∈ normalizer (h.K : Set X) := H.a_mem_normalizer_K
    have : H.rhoA = Eight.oddBarAction h.K ⟨h.a, haN⟩ := rfl
    rw [this, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hqa
  have h2 : IsPGroup 2 ((h.Q.subgroupOf (normalizer (h.K : Set X))).map
      (Eight.oddBarAction h.K)) := (h.sec8_isPGroup_Q.comap_subtype).map _
  exact eq_of_sylow_of_le d.c.Q_sylow hle hC h2

theorem Q_eq_sup : h.Q = (h.Q ⊓ h.M3) ⊔ h.B := by
  refine le_antisymm ?_ (sup_le inf_le_left (le_inf (h.B_le.trans inf_le_left) le_normalizer))
  intro q hq
  have hqN := H.Q_le_normalizer_K hq
  have h1 : Eight.oddBarAction h.K ⟨q, hqN⟩ ∈ d.c.Q := by
    rw [← d.map_Q_eq]
    exact ⟨⟨q, hqN⟩, hq, rfl⟩
  rw [d.c_Q] at h1
  obtain ⟨q₁, hq₁, hq₁q⟩ := mem_map.mp h1
  have hq₁N : (q₁ : X) ∈ normalizer (h.K : Set X) := H.Q_le_normalizer_K hq₁
  have h2 : (⟨(q₁ : X)⁻¹ * q, mul_mem (inv_mem hq₁N) hqN⟩ : normalizer (h.K : Set X)) ∈
      (Eight.oddBarAction h.K).ker := by
    rw [MonoidHom.mem_ker, show (⟨(q₁ : X)⁻¹ * q, _⟩ : normalizer (h.K : Set X)) =
      (⟨(q₁ : X), hq₁N⟩)⁻¹ * ⟨q, hqN⟩ from rfl, map_mul, map_inv, ← hq₁q]
    exact inv_mul_cancel _
  have h3 : (q₁ : X)⁻¹ * q ∈ h.B := by
    rw [← H.Q_inf_kernel]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (show (q₁ : X) ∈ h.Q from hq₁)) hq,
      Eight.mem_ker_oddBarAction.mp h2⟩
  rw [show q = (q₁ : X) * ((q₁ : X)⁻¹ * q) by group]
  exact mul_mem_sup ⟨hq₁, q₁.2⟩ h3

theorem b_not_mem_M3 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.b ∉ h.M3 := by
  intro hbM
  have hbB : d.b ∈ h.B := d.B_eq ▸ mem_zpowers d.b
  have hbQ : d.b ∈ h.Q := le_inf (h.B_le.trans inf_le_left) le_normalizer hbB
  have hbR := d.Q1_le_RM ⟨hbQ, hbM⟩
  have h1 : d.b = 1 := by
    refine d.rho_inj hCF1 hCF2 hbR (one_mem _) ?_
    have hbK : d.b ∈ coreActionKernel h.K := by
      rw [← H.Q_inf_kernel] at hbB
      exact hbB.2
    have h2 : (⟨d.b, H.Q_le_normalizer_K hbQ⟩ : normalizer (h.K : Set X)) ∈
        (Eight.oddBarAction h.K).ker := Eight.mem_ker_oddBarAction.mpr hbK
    rw [MonoidHom.mem_ker] at h2
    show _ = H.rho 1
    rw [map_one]
    exact h2
  have := d.b_ord
  rw [h1, orderOf_one] at this
  norm_num at this

theorem card_Q1 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    Nat.card ↥(h.Q ⊓ h.M3) = 32 := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have h2 : IsPGroup 2 ((h.Q ⊓ h.M3).subgroupOf h.M3) := (isPGroup_Q1 (h := h)).comap_subtype
  rw [← d.c_props.card_D.2.1, d.c_Q, ← inf_subgroupOf_right, Eight.card_map_of_isPGroup hker h2,
    ← card_map_of_injective h.M3.subtype_injective, map_subgroupOf_eq_of_le inf_le_right]

theorem card_B : Nat.card h.B = 2 := by
  rw [d.B_eq, Nat.card_zpowers, d.b_ord]

theorem B_le_centralizer_Q : h.B ≤ centralizer (h.Q : Set X) := by
  rw [d.B_eq, zpowers_le, mem_centralizer_iff]
  intro y hy
  have : y ∈ centralizer ({d.b} : Set X) := (d.Q_eq ▸ hy).2
  rw [mem_centralizer_singleton_iff] at this
  exact this

theorem card_Q (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card h.Q = 64 := by
  have hB : h.B ≤ normalizer ((h.Q ⊓ h.M3 : Subgroup X) : Set X) := by
    refine le_normalizer_of_conj fun y hy w hw => ?_
    have hc := mem_centralizer_iff.mp (d.B_le_centralizer_Q hy) w hw.1
    rw [← hc, mul_inv_cancel_right]
    exact hw
  have hdisj : Disjoint (h.Q ⊓ h.M3) h.B := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := hy
    rcases mem_zpowers_two d.b_ord (d.B_eq ▸ hy2) with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact absurd (h1 ▸ hy1.2) (d.b_not_mem_M3 hCF1 hCF2)
  rw [d.Q_eq_sup, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hB hdisj,
    d.card_Q1 hCF1 hCF2, d.card_B]

theorem K_le_centralizer_b : h.K ≤ centralizer ({d.b} : Set X) :=
  d.normalizer_B ▸ h.isPComponent_K.1

theorem g_norm_Q : d.g ∈ normalizer (h.Q : Set X) := by
  have hgb : d.g * d.b = d.b * d.g := mem_centralizer_singleton_iff.mp (d.K_le_centralizer_b d.g_K)
  have hgB : d.g ∈ normalizer (h.B : Set X) := by
    rw [d.B_eq]
    refine mem_normalizer_of_conjugate_eq ?_
    rw [Eight.conjugate_zpowers_eq, show d.g⁻¹ * d.b * d.g = d.b by rw [mul_assoc, ← hgb,
      inv_mul_cancel_left]]
  refine mem_normalizer_of_conjugate_eq ?_
  rw [d.Q_eq_sup, conjugate_sup, conjugate_eq_of_mem_normalizer d.g_norm,
    conjugate_eq_of_mem_normalizer hgB]

theorem tau_ne_one : d.tau ≠ 1 := by
  intro h1
  have hga : d.g⁻¹ * h.a * d.g = h.a := by rw [d.a_g, h1, mul_one]
  have hgC : d.g ∈ centralizer ({h.a} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc d.g * h.a = d.g * (d.g⁻¹ * h.a * d.g) := by rw [hga]
      _ = h.a * d.g := by group
  obtain ⟨hQY, hQS⟩ := h.sec8_Q_sylow H.J_normal
  have hgN : d.g ∈ normalizer (h.B : Set X) :=
    (d.normalizer_B ▸ d.K_le_centralizer_b d.g_K : d.g ∈ normalizer (h.B : Set X))
  have h2 : IsPGroup 2 ↥(h.Q ⊔ zpowers d.g) :=
    isPGroup_sup_zpowers h.sec8_isPGroup_Q d.g_norm_Q d.g_sq
  have h3 := eq_of_sylow_of_le hQS le_sup_left (sup_le hQY (zpowers_le.mpr ⟨hgC, hgN⟩)) h2
  exact d.g_not_mem (h3 ▸ mem_sup_right (mem_zpowers d.g))

theorem card_S (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card h.S = 128 := by
  have h1 := card_mul_index ((centralizer ({d.b} : Set X)).subgroupOf h.S)
  rw [d.index_Q, Six.card_subgroupOf_eq, inf_comm, ← d.Q_eq, d.card_Q hCF1 hCF2] at h1
  omega

theorem card_D (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) : Nat.card h.D = 8 := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hD2 : IsPGroup 2 (h.D.subgroupOf h.M3) :=
    ((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  have h1 := d.c_props.card_D.1
  rw [Cat8.Q3Conf.D, d.c_Q, d.c_a, ← H.map_D_eq hq hCF1 hCF2 hL0,
    Eight.card_map_of_isPGroup hker hD2, ← card_map_of_injective h.M3.subtype_injective,
    map_subgroupOf_eq_of_le H.D_le_M3] at h1
  exact h1

theorem tau_ne_z (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) : d.tau ≠ d.z := by
  intro htz
  have h1 := d.Q1_eq hCF1 hCF2 hq hL0
  have hle : zpowers d.tau ≤ h.D := by
    rw [htz, zpowers_le]
    exact d.z_D
  rw [sup_eq_left.mpr hle] at h1
  have haN : zpowers h.a ≤ normalizer (h.D : Set X) := by
    rw [zpowers_le]
    refine le_normalizer_of_conj (N := zpowers h.a) (fun y hy w hw => ?_) (mem_zpowers h.a)
    rcases mem_zpowers_two h.orderOf_a hy with rfl | rfl
    · rw [one_mul, inv_one, mul_one]
      exact hw
    · rw [← H.comm_a_of_mem_Q (h.sec8_D_le_Q hw), mul_inv_cancel_right]
      exact hw
  have hdisj : Disjoint h.D (zpowers h.a) := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr fun y hy => ?_
    rcases mem_zpowers_two h.orderOf_a hy.2 with rfl | rfl
    · exact one_mem _
    · exact absurd (H.fixedLayer_le_K (h.D_le_JB hy.1)) (H.a_not_mem_K hCF1 hCF2)
  have h2 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ haN hdisj
  rw [← h1, d.card_Q1 hCF1 hCF2, d.card_D hq hCF1 hCF2 hL0, Nat.card_zpowers, h.orderOf_a] at h2
  norm_num at h2

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
