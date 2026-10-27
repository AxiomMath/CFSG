module

public import CFSG.GH74.QTGen4.Recog.Ku.OpenLeaves
public import CFSG.GH74.QTGen4.Recog.Ku.HStructG

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

private theorem cardKuA_conj_fix {x z s : G} (hxz : Commute x z) (hs : s ∈ Subgroup.zpowers z) :
    x * s * x⁻¹ = s := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
  rw [mul_inv_eq_iff_eq_mul, ← hk]
  exact (hxz.zpow_right k).eq

private theorem cardKuA_comm_conj {x u g : G} (hcomm : x * u = u * x) :
    (x * g * x⁻¹) * u * (x * g * x⁻¹)⁻¹ * u⁻¹ = x * (g * u * g⁻¹ * u⁻¹) * x⁻¹ := by
  have h1 : x⁻¹ * u * x = u := by
    calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
      _ = x⁻¹ * (x * u) := by rw [hcomm]
      _ = u := by group
  have h2 : u⁻¹ * x⁻¹ = x⁻¹ * u⁻¹ := by
    calc u⁻¹ * x⁻¹ = (x * u)⁻¹ := by group
      _ = (u * x)⁻¹ := by rw [hcomm]
      _ = x⁻¹ * u⁻¹ := by group
  calc (x * g * x⁻¹) * u * (x * g * x⁻¹)⁻¹ * u⁻¹
      = x * g * (x⁻¹ * u * x) * g⁻¹ * (x⁻¹ * u⁻¹) := by group
    _ = x * g * u * g⁻¹ * (x⁻¹ * u⁻¹) := by rw [h1]
    _ = x * g * u * g⁻¹ * (u⁻¹ * x⁻¹) := by rw [h2]
    _ = x * (g * u * g⁻¹ * u⁻¹) * x⁻¹ := by group

private theorem cardKuA_comm_eq_one {u z t : G} (huz : Commute u z) (ht : t ∈ Subgroup.zpowers z) :
    t * u * t⁻¹ * u⁻¹ = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hcomm : t * u = u * t := by
    rw [← hk]
    exact (huz.zpow_right k).eq.symm
  rw [hcomm]
  group

private theorem cardKuA_mul_self_eq_one {z c : G} (hz : z * z = 1) (hc : c ∈ Subgroup.zpowers z) :
    c * c = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← hk, ← zpow_add, show k + k = 2 * k by ring, zpow_mul, zpow_two, hz, one_zpow]

private theorem cardKuA_comm_mul {a b u z : G} (haz : Commute a z)
    (hb : b * u * b⁻¹ * u⁻¹ ∈ Subgroup.zpowers z) :
    a * b * u * (a * b)⁻¹ * u⁻¹ = (b * u * b⁻¹ * u⁻¹) * (a * u * a⁻¹ * u⁻¹) := by
  have hc : a * (b * u * b⁻¹ * u⁻¹) = (b * u * b⁻¹ * u⁻¹) * a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (haz.zpow_right k).eq
  calc a * b * u * (a * b)⁻¹ * u⁻¹
      = (a * (b * u * b⁻¹ * u⁻¹) * a⁻¹) * (a * u * a⁻¹ * u⁻¹) := by group
    _ = (b * u * b⁻¹ * u⁻¹) * (a * u * a⁻¹ * u⁻¹) := by rw [hc]; group

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

private theorem coset_of_notMem (h : KuHyp G T M H P z) {u : G} (hu : u ∈ pCoreOf 2 H)
    (hnu : u ∉ P) : ∀ b ∈ pCoreOf 2 H, (b * u ∈ P ↔ b ∉ P) := by
  obtain ⟨u₁, hu₁, hcos₁⟩ := h.exists_u_coset
  have hq : ∀ q ∈ pCoreOf 2 H, q ∉ P → q * u₁⁻¹ ∈ P := by
    intro q hq hqP
    have hb : q * u₁⁻¹ ∈ pCoreOf 2 H := Subgroup.mul_mem _ hq (Subgroup.inv_mem _ hu₁)
    have e := hcos₁ (q * u₁⁻¹) hb
    rw [inv_mul_cancel_right] at e
    by_contra hc
    exact hqP (e.mpr hc)
  have hpu : u * u₁⁻¹ ∈ P := hq u hu hnu
  intro b hb
  have hbH : b ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hb
  have hconj : b * (u * u₁⁻¹) * b⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (h.hNormP hbH) _).mp hpu
  have e : b * u = (b * (u * u₁⁻¹) * b⁻¹) * (b * u₁) := by group
  rw [e, Subgroup.mul_mem_cancel_left P hconj]
  exact hcos₁ b hb

private theorem comm_mem_zpowers (h : KuHyp G T M H P z) {u : G} (hu : u ∈ pCoreOf 2 H)
    (hnu : u ∉ P) (hcos : ∀ b ∈ pCoreOf 2 H, (b * u ∈ P ↔ b ∉ P)) {r : G} (hr : r ∈ kuW P H) :
    r * u * r⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
  haveI := h.isEA_quot_P
  have hun : u ∈ Subgroup.normalizer (P : Set G) :=
    h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hWR := h.kuW_eq_psiPre hu hcos
  have hrP : r ∈ P := h.kuW_le_P hr
  have hmem : psi (⟨r, hrP⟩ : ↥P) ∈ LinearMap.range (kuDeltaLin (actV hun)) := by
    rw [hWR] at hr
    exact (mem_psiPre_iff.mp hr).2
  obtain ⟨s, hs⟩ := hmem
  rw [kuDeltaLin_apply] at hs
  have hcP : r * u * r⁻¹ * u⁻¹ ∈ P := by
    have e : r * u * r⁻¹ * u⁻¹ = r * (u * r⁻¹ * u⁻¹) := by group
    rw [e]
    exact P.mul_mem hrP ((Subgroup.mem_normalizer_iff.mp hun r⁻¹).mp (P.inv_mem hrP))
  have hc := psi_comm_eq hun ⟨r, hrP⟩ ⟨r * u * r⁻¹ * u⁻¹, hcP⟩ rfl
  have hfix : actV hun (psi (⟨r, hrP⟩ : ↥P)) = psi (⟨r, hrP⟩ : ↥P) := by
    rw [← hs, map_add, actV_involutive hun huu s, add_comm]
  have h0 : psi (⟨r * u * r⁻¹ * u⁻¹, hcP⟩ : ↥P) = 0 := by
    rw [hc, hfix, add_self_eq_zero_V]
  have hcen := (psi_eq_zero_iff _).mp h0
  rw [h.center_P_eq] at hcen
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcen
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

private theorem sum_orbit_mem (h : KuHyp G T M H P z) {x r : G} (hxH : x ∈ H)
    (hx3 : x ^ 3 = 1) (hfixx : ∀ p ∈ P, x * p * x⁻¹ = p → p ∈ Subgroup.zpowers z)
    (hrP : r ∈ P) (h1P : x * r * x⁻¹ ∈ P) (h2P : x * (x * r * x⁻¹) * x⁻¹ ∈ P) :
    r * (x * r * x⁻¹) * (x * (x * r * x⁻¹) * x⁻¹) ∈ Subgroup.zpowers z := by
  haveI := h.isEA_quot_P
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := h.hNormP hxH
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← h.hCz]
    exact hxH
  have hxz : Commute x z := (Subgroup.mem_centralizer_iff.mp hxC z (Set.mem_singleton z)).symm
  have hxxx : x * (x * x) = 1 := by
    rw [← pow_three]
    exact hx3
  have hfix : ∀ v, actV hxN v = v → v = 0 := fun v hv => actV_fixed_zero h hxN hx3 hxz hfixx v hv
  have hsum := sum_orbit_eq_zero (actV hxN) (actV_cube hxN hxxx) hfix (psi (⟨r, hrP⟩ : ↥P))
  have e1 : psi (⟨x * r * x⁻¹, h1P⟩ : ↥P) = actV hxN (psi (⟨r, hrP⟩ : ↥P)) :=
    psi_conj_eq hxN ⟨r, hrP⟩ h1P
  have e2 : psi (⟨x * (x * r * x⁻¹) * x⁻¹, h2P⟩ : ↥P) =
      actV hxN (psi (⟨x * r * x⁻¹, h1P⟩ : ↥P)) :=
    psi_conj_eq hxN ⟨x * r * x⁻¹, h1P⟩ h2P
  have htP : r * (x * r * x⁻¹) * (x * (x * r * x⁻¹) * x⁻¹) ∈ P :=
    P.mul_mem (P.mul_mem hrP h1P) h2P
  have hpt : psi (⟨r * (x * r * x⁻¹) * (x * (x * r * x⁻¹) * x⁻¹), htP⟩ : ↥P) = 0 := by
    have e : (⟨r * (x * r * x⁻¹) * (x * (x * r * x⁻¹) * x⁻¹), htP⟩ : ↥P) =
        ⟨r, hrP⟩ * ⟨x * r * x⁻¹, h1P⟩ * ⟨x * (x * r * x⁻¹) * x⁻¹, h2P⟩ := rfl
    rw [e, psi_mul, psi_mul, e2, e1]
    exact hsum
  have hcen := (psi_eq_zero_iff _).mp hpt
  rw [h.center_P_eq] at hcen
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcen
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem exists_mem_kuA_not_mem_P (h : KuHyp G T M H P z) : ∃ u ∈ kuA P H, u ∉ P := by
  haveI := h.isEA_quot_P
  obtain ⟨x, hxH, hx3o, hfixx⟩ := h.exists_x
  obtain ⟨u, hu, hnu, hxu⟩ := h.exists_fixed_coset hxH hx3o
  have hcos := h.coset_of_notMem hu hnu
  have hcomm : x * u = u * x := mul_inv_eq_iff_eq_mul.mp hxu
  have hx3 : x ^ 3 = 1 := by
    rw [← hx3o]
    exact pow_orderOf_eq_one x
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← h.hCz]
    exact hxH
  have hxz : Commute x z := (Subgroup.mem_centralizer_iff.mp hxC z (Set.mem_singleton z)).symm
  have huC : u ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← h.hCz]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 H hu
  have huz : Commute u z := (Subgroup.mem_centralizer_iff.mp huC z (Set.mem_singleton z)).symm
  have hzz : z * z = 1 := h.zP_sq
  have key : ∀ r ∈ kuW P H, r * u * r⁻¹ * u⁻¹ = 1 := by
    intro r hr
    have hrP : r ∈ P := h.kuW_le_P hr
    have hr1 : x * r * x⁻¹ ∈ kuW P H :=
      (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_kuW hxH) r).mp hr
    have hr2 : x * (x * r * x⁻¹) * x⁻¹ ∈ kuW P H :=
      (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_kuW hxH) _).mp hr1
    have hr1P : x * r * x⁻¹ ∈ P := h.kuW_le_P hr1
    have hr2P : x * (x * r * x⁻¹) * x⁻¹ ∈ P := h.kuW_le_P hr2
    have c0 := comm_mem_zpowers h hu hnu hcos hr
    have c1 := comm_mem_zpowers h hu hnu hcos hr1
    have c2 := comm_mem_zpowers h hu hnu hcos hr2
    have e1 : (x * r * x⁻¹) * u * (x * r * x⁻¹)⁻¹ * u⁻¹ = r * u * r⁻¹ * u⁻¹ := by
      rw [cardKuA_comm_conj (g := r) hcomm, cardKuA_conj_fix hxz c0]
    have e2 : (x * (x * r * x⁻¹) * x⁻¹) * u * (x * (x * r * x⁻¹) * x⁻¹)⁻¹ * u⁻¹ =
        (x * r * x⁻¹) * u * (x * r * x⁻¹)⁻¹ * u⁻¹ := by
      rw [cardKuA_comm_conj (g := x * r * x⁻¹) hcomm, cardKuA_conj_fix hxz c1]
    have ht := sum_orbit_mem h hxH hx3 hfixx hrP hr1P hr2P
    have h1 := cardKuA_comm_eq_one huz ht
    have h2 := cardKuA_comm_mul (show Commute (r * (x * r * x⁻¹)) z from
      h.zP_comm (P.mul_mem hrP hr1P)) c2
    have h3 := cardKuA_comm_mul (show Commute r z from h.zP_comm hrP) c1
    rw [h2, h3, e2, e1] at h1
    have hcc := cardKuA_mul_self_eq_one hzz c0
    rw [hcc, mul_one] at h1
    exact h1
  refine ⟨u, Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩, hnu⟩
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp (key w hw))

end KuHyp

theorem leafCardKuA : LeafCardKuA := by
  intro G _ _ T M H P z h
  obtain ⟨u, hu, hnu⟩ := h.exists_mem_kuA_not_mem_P
  have hA := Subgroup.relIndex_mul_card P (kuA P H)
  have hPA : P ⊓ kuA P H = kuW P H := by
    rw [inf_comm]
    exact h.kuA_inf_P
  rw [hPA, h.card_kuW] at hA
  have hle : P.relIndex (kuA P H) ≤ P.relIndex (pCoreOf 2 H) :=
    Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h.relIndex_P_pCore]; norm_num)
  rw [h.relIndex_P_pCore] at hle
  have hne1 : P.relIndex (kuA P H) ≠ 1 := fun h1 => hnu (Subgroup.relIndex_eq_one.mp h1 hu)
  have hpos : 0 < Nat.card (kuA P H) := Nat.card_pos
  have hne0 : P.relIndex (kuA P H) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hA
    omega
  omega

end CFSG.GH74.QTGen4.Ku
