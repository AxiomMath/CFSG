module

public import CFSG.GH74.QTGen4.Recog.Ku.HStructF
public import CFSG.GH74.QTGen4.Recog.Ku.HStructI
public import CFSG.GH74.QTGen4.Recog.Ku.Orders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_pCoreOf_self (K : Subgroup G) :
    K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
  have hle : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  have hN : (pCoreOf 2 K).subgroupOf K = Open.pCore 2 K := by
    ext y
    simp [pCoreOf, Subgroup.mem_subgroupOf]
  rw [hN]
  exact CFSG.LieType.BorelTits.pCore_normal 2

theorem conj_mem_commutator_of_mem {K L N : Subgroup G}
    (hK : N ≤ Subgroup.normalizer (K : Set G)) (hL : N ≤ Subgroup.normalizer (L : Set G))
    {g : G} (hg : g ∈ N) {x : G} (hx : x ∈ ⁅K, L⁆) : g * x * g⁻¹ ∈ ⁅K, L⁆ := by
  have key : ⁅K, L⁆ ≤ ⁅K, L⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅a, b⁆ =
        ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      show g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ =
        (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator
      ((Subgroup.mem_normalizer_iff.mp (hK hg) a).mp ha)
      ((Subgroup.mem_normalizer_iff.mp (hL hg) b).mp hb)
  have h2 := key hx
  rw [Subgroup.mem_comap] at h2
  exact h2

theorem le_normalizer_commutator_of {K L N : Subgroup G}
    (hK : N ≤ Subgroup.normalizer (K : Set G)) (hL : N ≤ Subgroup.normalizer (L : Set G)) :
    N ≤ Subgroup.normalizer ((⁅K, L⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_commutator_of_mem hK hL hg hx
  · intro hx
    have := conj_mem_commutator_of_mem hK hL (N.inv_mem hg) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem le_normalizer_centralizer_of {N W : Subgroup G}
    (hW : N ≤ Subgroup.normalizer (W : Set G)) :
    N ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have aux : ∀ y ∈ Subgroup.centralizer (W : Set G), ∀ k ∈ N, k * y * k⁻¹ ∈
      Subgroup.centralizer (W : Set G) := by
    intro y hy k hk
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro w hw
    have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hW (N.inv_mem hk)) w).mp hw
    have hc := hy _ hw'
    simp only [inv_inv] at hw' hc
    calc w * (k * y * k⁻¹) = (k * (k⁻¹ * w * k) * k⁻¹) * (k * y * k⁻¹) := by group
      _ = k * ((k⁻¹ * w * k) * y) * k⁻¹ := by group
      _ = k * (y * (k⁻¹ * w * k)) * k⁻¹ := by rw [hc]
      _ = k * y * k⁻¹ * (k * (k⁻¹ * w * k) * k⁻¹) := by group
      _ = k * y * k⁻¹ * w := by group
  constructor
  · intro hx
    exact aux x hx g hg
  · intro hx
    have := aux _ hx g⁻¹ (N.inv_mem hg)
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem le_normalizer_inf_of {K L N : Subgroup G}
    (hK : N ≤ Subgroup.normalizer (K : Set G)) (hL : N ≤ Subgroup.normalizer (L : Set G)) :
    N ≤ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (hK hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp (hL hg) x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr h1 h2

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem card_pCore_H (h : KuHyp G T M H P z) : Nat.card (pCoreOf 2 H) = 64 :=
  h.card_pCore_H_aux

theorem P_le_pCore_H (h : KuHyp G T M H P z) : P ≤ pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.pH h.hNormP h.isPGroup_P

theorem pCore_H_le_T (h : KuHyp G T M H P z) : pCoreOf 2 H ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hTn : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    h.tH.trans (le_normalizer_pCoreOf_self H)
  have hsup : IsPGroup 2 (pCoreOf 2 H ⊔ T : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_sup_of_normal_left' h.sylow.1 hTn
  have hEq : (pCoreOf 2 H ⊔ T : Subgroup G) = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_right
  have hS : (S : Subgroup G) = T := rfl
  rw [hS] at hEq
  exact le_sup_left.trans hEq.le

theorem H_le_normalizer_pCore_H (_h : KuHyp G T M H P z) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  le_normalizer_pCoreOf_self H

theorem exists_x (h : KuHyp G T M H P z) :
    ∃ x ∈ H, orderOf x = 3 ∧ ∀ p ∈ P, x * p * x⁻¹ = p → p ∈ Subgroup.zpowers z := by
  obtain ⟨X, hXs, hXC⟩ := h.xSylow
  obtain ⟨hXH, hXp, hXi⟩ := hXs
  have hcard : Nat.card X = 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
    have h1 : Nat.card (X.subgroupOf H) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    have h2 : X.relIndex H * Nat.card X = 384 := by
      have := Subgroup.card_mul_index (X.subgroupOf H)
      rw [h1, h.card_H] at this
      rw [mul_comm]
      exact this
    rw [hn] at h2 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hc
      have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      have h384 : 3 ^ n ∣ 384 := Dvd.intro_left _ h2
      have := dvd_trans h9 h384
      norm_num at this
    interval_cases n
    · exfalso
      apply hXi
      rw [pow_zero, mul_one] at h2
      rw [h2]
      norm_num
    · norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (dvd_of_eq hcard.symm)
  have hxH : (x : G) ∈ H := hXH x.2
  have hxord : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx
  refine ⟨(x : G), hxH, hxord, ?_⟩
  have hzX : Subgroup.zpowers (x : G) = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
      (le_of_eq (by rw [Nat.card_zpowers, hxord, hcard]))
  intro p hp hpx
  have hcomm : Commute (x : G) p := mul_inv_eq_iff_eq_mul.mp hpx
  have hpC : p ∈ P ⊓ Subgroup.centralizer (X : Set G) := by
    refine ⟨hp, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hk
    rw [← hzX] at hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact hcomm.zpow_left m
  rw [hXC] at hpC
  exact hpC

theorem mem_P_of_acts_trivially (h : KuHyp G T M H P z) {g : G} (hg : g ∈ H)
    (hgP : ∀ p ∈ P, g * p * g⁻¹ * p⁻¹ ∈ Subgroup.zpowers z) : g ∈ P :=
  h.mem_P_of_acts_trivially_aux hg hgP

theorem relIndex_P_pCore (h : KuHyp G T M H P z) : P.relIndex (pCoreOf 2 H) = 2 := by
  have h1 := Subgroup.relIndex_mul_card P (pCoreOf 2 H)
  rw [inf_eq_left.mpr h.P_le_pCore_H, h.card_pCore_H] at h1
  have hP : Nat.card P = 32 := by rw [h.pExtra.2.1]; norm_num
  rw [hP] at h1
  omega

theorem exists_u_coset (h : KuHyp G T M H P z) :
    ∃ u ∈ pCoreOf 2 H, ∀ b ∈ pCoreOf 2 H, (b * u ∈ P ↔ b ∉ P) := by
  obtain ⟨u, hu, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp h.relIndex_P_pCore
  refine ⟨u, hu, fun b hb => ?_⟩
  have := hxor b hb
  by_cases hbP : b ∈ P <;> by_cases hbu : b * u ∈ P <;> simp_all [Xor]

theorem kuW_le_P (h : KuHyp G T M H P z) : kuW P H ≤ P := by
  show ⁅P, pCoreOf 2 H⁆ ≤ P
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hbH : b ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hb
  have hconj : b * a * b⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (h.hNormP hbH) a).mp ha
  rw [commutatorElement_def]
  have e : a * b * a⁻¹ * b⁻¹ = a * (b * a * b⁻¹)⁻¹ := by group
  rw [e]
  exact P.mul_mem ha (P.inv_mem hconj)

theorem kuW_le_pCore_H (h : KuHyp G T M H P z) : kuW P H ≤ pCoreOf 2 H := by
  show ⁅P, pCoreOf 2 H⁆ ≤ pCoreOf 2 H
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ pCoreOf 2 H := h.P_le_pCore_H ha
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' hb) (Subgroup.inv_mem _ ha'))
    (Subgroup.inv_mem _ hb)

theorem z_mem_kuW (h : KuHyp G T M H P z) : z ∈ kuW P H := by
  obtain ⟨c, hc, hcz⟩ := h.exists_mem_kuW_not_mem_zpowers
  have hcP : c ∈ P := h.kuW_le_P hc
  have hcQ : c ∈ pCoreOf 2 H := h.kuW_le_pCore_H hc
  obtain ⟨p, hp, hpc⟩ := h.exists_comm_eq_z hcP hcz
  rw [← hpc]
  exact Subgroup.commutator_mem_commutator hp hcQ

theorem kuW_eq_psiPre (h : KuHyp G T M H P z) {u : G}
    [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    (hu : u ∈ pCoreOf 2 H) (hcos : ∀ b ∈ pCoreOf 2 H, (b * u ∈ P ↔ b ∉ P)) :
    kuW P H = psiPre (LinearMap.range (kuDeltaLin (actV
      (h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu))))) := by
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  apply le_antisymm
  · show ⁅P, pCoreOf 2 H⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbN : b ∈ Subgroup.normalizer (P : Set G) :=
      h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hb)
    have hcomm : ⁅a, b⁆ ∈ P := by
      rw [commutatorElement_def]
      have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact P.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (P.inv_mem ha))
    refine ⟨hcomm, ?_⟩
    have hcase : b ∈ P ∨ b * u ∈ P := by
      by_cases hbP : b ∈ P
      · exact Or.inl hbP
      · exact Or.inr ((hcos b hb).mpr hbP)
    exact psi_comm_mem_range hbN hcase hun huu ⟨a, ha⟩ ⟨⁅a, b⁆, hcomm⟩ rfl
  · intro g hg
    obtain ⟨hgP, hpg⟩ := hg
    obtain ⟨v, hv⟩ := hpg
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hpsia : psi a = v := congrArg Additive.ofMul ha
    have hcP : (a : G) * u * (a : G)⁻¹ * u⁻¹ ∈ P := by
      have e : (a : G) * u * (a : G)⁻¹ * u⁻¹ = a * (u * (a : G)⁻¹ * u⁻¹) := by group
      rw [e]
      exact P.mul_mem a.2 ((Subgroup.mem_normalizer_iff.mp hun (a : G)⁻¹).mp (P.inv_mem a.2))
    set c : ↥P := ⟨(a : G) * u * (a : G)⁻¹ * u⁻¹, hcP⟩ with hc
    have hpc : psi c = psi ⟨g, hgP⟩ := by
      rw [psi_comm_eq hun a c rfl, ← hv]
      simp only [hpsia, kuDeltaLin_apply]
    set t : ↥P := ⟨g, hgP⟩ * c⁻¹ with ht
    have htc : t ∈ Subgroup.center ↥P := by
      rw [← psi_eq_zero_iff, ht, psi_mul, psi_inv, hpc]
      exact add_neg_cancel _
    rw [h.center_P_eq] at htc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp htc
    have htG : (t : G) = z ^ n := by
      have := congrArg Subtype.val hn
      simpa using this.symm
    have htG': (t : G) = g * (c : G)⁻¹ := rfl
    have hz : (t : G) ∈ kuW P H := by
      rw [htG]
      exact Subgroup.zpow_mem _ h.z_mem_kuW n
    have hcW : (c : G) ∈ kuW P H := Subgroup.commutator_mem_commutator a.2 hu
    have hgt : g = (t : G) * (c : G) := by
      rw [htG']
      group
    have := mul_mem hz hcW
    rwa [← hgt] at this

attribute [local instance] IsMulCommutative.instCommGroup

theorem finrank_quotP (h : KuHyp G T M H P z)
    [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)] :
    Module.finrank (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) = 4 := by
  have hZ := h.card_center_P
  have hPc : Nat.card (↥P) = 32 := by rw [h.pExtra.2.1]; norm_num
  have hq : Nat.card (↥P ⧸ Subgroup.center ↥P) = 16 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hZ, hPc] at h1
    omega
  have hV : Nat.card (Additive (↥P ⧸ Subgroup.center ↥P)) = 16 :=
    (Nat.card_congr (Additive.ofMul :
      (↥P ⧸ Subgroup.center ↥P) ≃ Additive (↥P ⧸ Subgroup.center ↥P))).symm.trans hq
  have hpow : Nat.card (Additive (↥P ⧸ Subgroup.center ↥P)) =
      2 ^ Module.finrank (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
  have h16 : 2 ^ Module.finrank (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) = 2 ^ 4 := by
    rw [← hpow, hV]
    norm_num
  exact Nat.pow_right_injective (le_refl 2) h16

theorem exists_ne_actV (h : KuHyp G T M H P z) [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {u : G} (hu : u ∈ pCoreOf 2 H) (hnu : u ∉ P) :
    ∃ v, actV (h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)) v ≠ v := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hnu
  apply h.mem_P_of_acts_trivially (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  intro p hp
  have hfix := hcon (Additive.ofMul (QuotientGroup.mk (⟨p, hp⟩ : ↥P)))
  rw [actV_mk] at hfix
  have hq : (QuotientGroup.mk (conjP _ (⟨p, hp⟩ : ↥P)) : ↥P ⧸ Subgroup.center ↥P) =
      QuotientGroup.mk (⟨p, hp⟩ : ↥P) := congrArg Additive.toMul hfix
  rw [QuotientGroup.eq, h.center_P_eq] at hq
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hq
  have hG : z ^ n = (u * p * u⁻¹)⁻¹ * p := by
    have := congrArg Subtype.val hn
    simpa [conjP] using this
  have e1 : z ^ (-n) = p⁻¹ * (u * p * u⁻¹) := by
    rw [zpow_neg, hG]
    group
  have hcomm : p * z ^ (-n) = z ^ (-n) * p :=
    ((show Commute p z from h.zP_comm hp).zpow_right (-n)).eq
  refine Subgroup.mem_zpowers_iff.mpr ⟨-n, ?_⟩
  calc z ^ (-n) = p * z ^ (-n) * p⁻¹ := by rw [hcomm]; group
    _ = p * (p⁻¹ * (u * p * u⁻¹)) * p⁻¹ := by rw [← e1]
    _ = u * p * u⁻¹ * p⁻¹ := by group

theorem fix_of_conj_zpow {x z p : G} {m : ℤ} (hxz : Commute x z) (hz : z * z = 1) (hx3 : x ^ 3 = 1)
    (hpx : x * p * x⁻¹ = p * z ^ m) : x * p * x⁻¹ = p := by
  have hzm : z ^ m * z ^ m = 1 := by
    rw [← (Commute.refl z).mul_zpow, hz, one_zpow]
  have hxzm : x * z ^ m * x⁻¹ = z ^ m := by
    rw [(hxz.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : x * (x * p * x⁻¹) * x⁻¹ = p := by
    calc x * (x * p * x⁻¹) * x⁻¹ = x * (p * z ^ m) * x⁻¹ := by rw [hpx]
      _ = (x * p * x⁻¹) * (x * z ^ m * x⁻¹) := by group
      _ = (p * z ^ m) * z ^ m := by rw [hpx, hxzm]
      _ = p := by rw [mul_assoc, hzm, mul_one]
  have h5 : x * p * x⁻¹ = x * (x * (x * p * x⁻¹) * x⁻¹) * x⁻¹ := by rw [h2]
  have h6 : x * (x * (x * p * x⁻¹) * x⁻¹) * x⁻¹ = p := by
    have hxxx : x * x * x = 1 := by
      rw [← hx3, pow_three, mul_assoc]
    have e : x * (x * (x * p * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * p * (x * x * x)⁻¹ := by
      group
    rw [e, hxxx]
    simp
  exact h5.trans h6

theorem actV_fixed_zero (h : KuHyp G T M H P z) [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {x : G} (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hx3 : x ^ 3 = 1) (hxz : Commute x z)
    (hfixx : ∀ p ∈ P, x * p * x⁻¹ = p → p ∈ Subgroup.zpowers z)
    (v : Additive (↥P ⧸ Subgroup.center ↥P)) (hv : actV hxN v = v) : v = 0 := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hqv : psi q = v := congrArg Additive.ofMul hq
  rw [← hqv] at hv ⊢
  have hc : Additive.ofMul (QuotientGroup.mk (conjP hxN q) : ↥P ⧸ Subgroup.center ↥P) =
      Additive.ofMul (QuotientGroup.mk q : ↥P ⧸ Subgroup.center ↥P) := by
    rw [← actV_mk]
    exact hv
  have hc' : (QuotientGroup.mk (conjP hxN q) : ↥P ⧸ Subgroup.center ↥P) =
      QuotientGroup.mk q := congrArg Additive.toMul hc
  rw [QuotientGroup.eq, h.center_P_eq] at hc'
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc'
  have hG : z ^ n = (x * (q : G) * x⁻¹)⁻¹ * (q : G) := by
    have := congrArg Subtype.val hn
    simpa [conjP] using this
  have hpx : x * (q : G) * x⁻¹ = (q : G) * z ^ (-n) := by
    rw [zpow_neg, hG]
    group
  have hfix := fix_of_conj_zpow hxz h.zP_sq hx3 hpx
  have hqz := hfixx (q : G) q.2 hfix
  have hcen : q ∈ Subgroup.center ↥P := by
    rw [h.center_P_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqz
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  exact (psi_eq_zero_iff q).mpr hcen

theorem actV_congr_elt [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)] {g g' : G}
    (hN : g ∈ Subgroup.normalizer (P : Set G)) (hN' : g' ∈ Subgroup.normalizer (P : Set G))
    (e : g = g') : actV hN = actV hN' := by
  subst e
  rfl

theorem sgn_sq_mul_gen {Q : Type*} [Group Q] {z : Q} (C : KuZCore Q z) (a b : Q) :
    sgn ((a * b) ^ 2) = sgn (a ^ 2) + sgn (b ^ 2) + KuZCore.pairQ a b := by
  obtain ⟨c, hc⟩ : ∃ c, ⁅b, a⁆ = c := ⟨_, rfl⟩
  have hba : b * a = c * (a * b) := by
    rw [← hc]
    simp only [commutatorElement_def]
    group
  have hcen : ∀ g : Q, g * c = c * g := by
    intro g
    rw [← hc]
    exact Subgroup.mem_center_iff.mp (C.comm_mem b a) g
  have e : (a * b) ^ 2 = c * (a ^ 2 * b ^ 2) := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; simp only [mul_assoc]
      _ = a * (c * (a * b)) * b := by rw [hba]
      _ = c * (a * a) * (b * b) := by rw [← mul_assoc a c, hcen a]; simp only [mul_assoc]
      _ = c * (a ^ 2 * b ^ 2) := by simp only [sq, mul_assoc]
  have ha2 : a ^ 2 ∈ Subgroup.center Q := C.sq_mem a
  have hb2 : b ^ 2 ∈ Subgroup.center Q := C.sq_mem b
  have hm : a ^ 2 * b ^ 2 ∈ Subgroup.center Q := Subgroup.mul_mem _ ha2 hb2
  rw [C.center_eq] at ha2 hb2 hm
  have hcpair : c = 1 ∨ c = z := by
    rw [← hc]
    exact C.comm_pair b a
  have hsym : KuZCore.pairQ a b = sgn c := by
    rw [← hc]
    exact C.pairQ_symm a b
  rw [e, C.sgn_mul hcpair (KuZCore.mem_zpowers_cases C.z_sq hm),
    C.sgn_mul (KuZCore.mem_zpowers_cases C.z_sq ha2) (KuZCore.mem_zpowers_cases C.z_sq hb2), hsym]
  abel

theorem sgn_conjP {P : Subgroup G} {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G))
    (c : ↥P) : sgn (conjP hN c) = sgn c := by
  by_cases hc : c = 1
  · subst hc
    rw [map_one]
  · have hc' : conjP hN c ≠ 1 := fun e => hc (Subtype.ext (by
      have e' : g * (c : G) * g⁻¹ = 1 := congrArg Subtype.val e
      calc (c : G) = g⁻¹ * (g * (c : G) * g⁻¹) * g := by group
        _ = 1 := by rw [e']; group))
    simp [sgn, hc, hc']

theorem commForm_actV (h : KuHyp G T M H P z) [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G))
    (v w : Additive (↥P ⧸ Subgroup.center ↥P)) :
    h.kuZCore_P.commForm (actV hN v) (actV hN w) = h.kuZCore_P.commForm v w := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
  have hv : Additive.ofMul (QuotientGroup.mk q : ↥P ⧸ Subgroup.center ↥P) = v :=
    congrArg Additive.ofMul hq
  have hw : Additive.ofMul (QuotientGroup.mk r : ↥P ⧸ Subgroup.center ↥P) = w :=
    congrArg Additive.ofMul hr
  rw [← hv, ← hw, actV_mk, actV_mk, h.kuZCore_P.commForm_apply, h.kuZCore_P.commForm_apply]
  show KuZCore.pairV (QuotientGroup.mk (conjP hN q) : ↥P ⧸ Subgroup.center ↥P)
      (QuotientGroup.mk (conjP hN r) : ↥P ⧸ Subgroup.center ↥P) =
    KuZCore.pairV (QuotientGroup.mk q : ↥P ⧸ Subgroup.center ↥P) (QuotientGroup.mk r)
  rw [h.kuZCore_P.pairV_mk, h.kuZCore_P.pairV_mk]
  unfold KuZCore.pairQ
  rw [← map_commutatorElement (conjP hN) q r]
  exact sgn_conjP hN _

theorem pairQ_eq_zero_of_range (h : KuHyp G T M H P z) [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {u : G} (hun : u ∈ Subgroup.normalizer (P : Set G))
    (hγ : ∀ v, actV hun (actV hun v) = v) {a b : ↥P}
    (sa : psi a ∈ LinearMap.range (kuDeltaLin (actV hun)))
    (sb : psi b ∈ LinearMap.range (kuDeltaLin (actV hun))) : KuZCore.pairQ a b = 0 := by
  obtain ⟨s, hs⟩ := sa
  obtain ⟨t, ht⟩ := sb
  have hc : KuZCore.pairQ a b = h.kuZCore_P.commForm (psi a) (psi b) := by
    rw [h.kuZCore_P.commForm_apply]
    exact (h.kuZCore_P.pairV_mk a b).symm
  rw [hc, ← hs, ← ht]
  exact B_delta_delta (actV hun) hγ h.kuZCore_P.commForm (fun x y => commForm_actV h hun x y) s t

theorem card_kuW (h : KuHyp G T M H P z) : Nat.card (kuW P H) = 8 := by
  haveI := h.isEA_quot_P
  obtain ⟨u, hu, hcos⟩ := h.exists_u_coset
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  obtain ⟨x, hxH, hxord, hfixx⟩ := h.exists_x
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := h.hNormP hxH
  have hx3 : x ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hxxx : x * (x * x) = 1 := by
    rw [← pow_three]
    exact hx3
  have hxinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right hxxx
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [h.hCz] at hxH
    exact hxH
  have hxz : Commute x z := (Subgroup.mem_centralizer_iff.mp hxC z (Set.mem_singleton z)).symm
  have hid3 : actV (mul_mem hxN (mul_mem hxN hxN)) = LinearMap.id :=
    actV_eq_id_of_eq_one _ hxxx
  have hX3 : ∀ v, actV hxN (actV hxN (actV hxN v)) = v := fun v => by
    have e2 := actV_mul hxN hxN v
    have e := actV_mul hxN (mul_mem hxN hxN) v
    calc actV hxN (actV hxN (actV hxN v)) = actV hxN (actV (mul_mem hxN hxN) v) := by rw [e2]
      _ = actV (mul_mem hxN (mul_mem hxN hxN)) v := by rw [e]
      _ = v := by rw [hid3, LinearMap.id_apply]
  have hkey2 : ∀ v, actV (inv_mem hxN) v = actV hxN (actV hxN v) := fun v => by
    rw [actV_congr_elt (inv_mem hxN) (mul_mem hxN hxN) hxinv, actV_mul hxN hxN v]
  have hxu : x * u * x⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_pCore_H hxH) u).mp hu
  have hxcP : x * u * x⁻¹ ∉ P := fun hc =>
    hnu ((Subgroup.mem_normalizer_iff.mp hxN u).mpr hc)
  have hcu : x * u * x⁻¹ * u ∈ P := (hcos _ hxu).mpr hxcP
  have hconj : actV (mul_mem (mul_mem hxN hun) (inv_mem hxN)) = actV hun :=
    actV_eq_of_mul_mem _ hun hcu huu
  have hkey1 : ∀ v, actV (mul_mem (mul_mem hxN hun) (inv_mem hxN)) v =
      actV hxN (actV hun (actV (inv_mem hxN) v)) := fun v => by
    rw [actV_mul (mul_mem hxN hun) (inv_mem hxN) v, actV_mul hxN hun]
  have key : ∀ v, actV hxN (actV hun (actV hxN (actV hxN v))) = actV hun v := fun v => by
    have h1 := LinearMap.congr_fun hconj v
    rw [← h1, hkey1 v, hkey2 v]
  have hxγ : ∀ w, actV hun (actV hxN w) = actV hxN (actV hun w) := fun w => by
    have := key (actV hxN w)
    rw [hX3 w] at this
    exact this.symm
  have hγ : ∀ v, actV hun (actV hun v) = v := fun v => actV_involutive hun huu v
  have hrank := finrank_range_kuDeltaLin (actV hun) hγ (exists_ne_actV h hu hnu) (actV hxN) hX3 hxγ
    (fun v hv => actV_fixed_zero h hxN hx3 hxz hfixx v hv) h.finrank_quotP
  have hR : Nat.card (LinearMap.range (kuDeltaLin (actV hun))) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hrank] <;> simp [ZMod.card]
  rw [kuW_eq_psiPre h hu hcos, card_psiPre, h.card_center_P, hR] <;> norm_num

theorem B_self_kuW (h : KuHyp G T M H P z) {u : G} (hu : u ∈ pCoreOf 2 H)
    (hcos : ∀ b ∈ pCoreOf 2 H, (b * u ∈ P ↔ b ∉ P))
    [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    (s : Additive (↥P ⧸ Subgroup.center ↥P)) :
    h.kuZCore_P.commForm s (actV (h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)) s) = 0 := by
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  obtain ⟨x, hxH, hxord, hfixx⟩ := h.exists_x
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := h.hNormP hxH
  have hx3 : x ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hxxx : x * (x * x) = 1 := by
    rw [← pow_three]
    exact hx3
  have hxinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right hxxx
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [h.hCz] at hxH
    exact hxH
  have hxz : Commute x z := (Subgroup.mem_centralizer_iff.mp hxC z (Set.mem_singleton z)).symm
  have hid3 : actV (mul_mem hxN (mul_mem hxN hxN)) = LinearMap.id :=
    actV_eq_id_of_eq_one _ hxxx
  have hX3 : ∀ v, actV hxN (actV hxN (actV hxN v)) = v := fun v => by
    have e2 := actV_mul hxN hxN v
    have e := actV_mul hxN (mul_mem hxN hxN) v
    calc actV hxN (actV hxN (actV hxN v)) = actV hxN (actV (mul_mem hxN hxN) v) := by rw [e2]
      _ = actV (mul_mem hxN (mul_mem hxN hxN)) v := by rw [e]
      _ = v := by rw [hid3, LinearMap.id_apply]
  have hkey2 : ∀ v, actV (inv_mem hxN) v = actV hxN (actV hxN v) := fun v => by
    rw [actV_congr_elt (inv_mem hxN) (mul_mem hxN hxN) hxinv, actV_mul hxN hxN v]
  have hxu : x * u * x⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_pCore_H hxH) u).mp hu
  have hxcP : x * u * x⁻¹ ∉ P := fun hc =>
    hnu ((Subgroup.mem_normalizer_iff.mp hxN u).mpr hc)
  have hcu : x * u * x⁻¹ * u ∈ P := (hcos _ hxu).mpr hxcP
  have hconj : actV (mul_mem (mul_mem hxN hun) (inv_mem hxN)) = actV hun :=
    actV_eq_of_mul_mem _ hun hcu huu
  have hkey1 : ∀ v, actV (mul_mem (mul_mem hxN hun) (inv_mem hxN)) v =
      actV hxN (actV hun (actV (inv_mem hxN) v)) := fun v => by
    rw [actV_mul (mul_mem hxN hun) (inv_mem hxN) v, actV_mul hxN hun]
  have key : ∀ v, actV hxN (actV hun (actV hxN (actV hxN v))) = actV hun v := fun v => by
    have h1 := LinearMap.congr_fun hconj v
    rw [← h1, hkey1 v, hkey2 v]
  have hxγ : ∀ w, actV hun (actV hxN w) = actV hxN (actV hun w) := fun w => by
    have := key (actV hxN w)
    rw [hX3 w] at this
    exact this.symm
  have hBs : ∀ a b, h.kuZCore_P.commForm a b = h.kuZCore_P.commForm b a := fun a b => by
    rw [h.kuZCore_P.commForm_apply, h.kuZCore_P.commForm_apply]
    exact h.kuZCore_P.pairV_comm _ _
  have hfix : ∀ v, actV hxN v = v → v = 0 := fun v hv =>
    actV_fixed_zero h hxN hx3 hxz hfixx v hv
  have hγ : ∀ v, actV hun (actV hun v) = v := fun v => actV_involutive hun huu v
  exact B_self_gamma_eq_zero (actV hun) hγ h.kuZCore_P.commForm (fun a b => commForm_actV h hun a b)
    hBs (actV hxN) hxγ (fun a b => commForm_actV h hxN a b) hfix s

theorem sgn_inv' {Q : Type*} [Group Q] (c : Q) : sgn c⁻¹ = sgn c := by
  by_cases hc : c = 1
  · subst hc
    simp
  · have hi : c⁻¹ ≠ 1 := inv_ne_one.mpr hc
    simp [sgn, hc, hi]

theorem sq_comm_eq_one (h : KuHyp G T M H P z) [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {u : G} (hun : u ∈ Subgroup.normalizer (P : Set G))
    (hB : ∀ s, h.kuZCore_P.commForm s (actV hun s) = 0) (a : ↥P) :
    (a * conjP hun a⁻¹) ^ 2 = 1 := by
  have hab := sgn_sq_mul_gen h.kuZCore_P a (conjP hun a⁻¹)
  have hb2 : sgn ((conjP hun a⁻¹) ^ 2) = sgn (a ^ 2) := by
    rw [← map_pow, sgn_conjP, inv_pow, sgn_inv']
  have hpq : KuZCore.pairQ a (conjP hun a⁻¹) = 0 := by
    have hc : KuZCore.pairQ a (conjP hun a⁻¹) =
        h.kuZCore_P.commForm (psi a) (psi (conjP hun a⁻¹)) := by
      rw [h.kuZCore_P.commForm_apply]
      exact (h.kuZCore_P.pairV_mk a (conjP hun a⁻¹)).symm
    have hdef : psi (conjP hun a⁻¹) = actV hun (psi a⁻¹) := (actV_mk hun a⁻¹).symm
    rw [hc, hdef, psi_inv]
    simp only [map_neg]
    rw [hB, neg_zero]
  have hz : sgn ((a * conjP hun a⁻¹) ^ 2) = 0 := by
    rw [hab, hb2, hpq, add_zero]
    exact zmod2_add_self _
  exact sgn_eq_zero_iff_gen.mp hz

theorem kuW_sq_eq_one (h : KuHyp G T M H P z) {x : G} (hx : x ∈ kuW P H) : x ^ 2 = 1 := by
  haveI := h.isEA_quot_P
  obtain ⟨u, hu, hcos⟩ := h.exists_u_coset
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  have hB : ∀ s, h.kuZCore_P.commForm s (actV hun s) = 0 := fun s => B_self_kuW h hu hcos s
  rw [kuW_eq_psiPre h hu hcos] at hx
  obtain ⟨hxP, hsx⟩ := mem_psiPre_iff.mp hx
  obtain ⟨s, hs⟩ := hsx
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul s)
  have hpsia : psi a = s := congrArg Additive.ofMul ha
  have hW0 : ((a * conjP hun a⁻¹ : ↥P) : G) = (a : G) * u * (a : G)⁻¹ * u⁻¹ := by
    rw [Subgroup.coe_mul]
    show (a : G) * (u * ((a⁻¹ : ↥P) : G) * u⁻¹) = _
    rw [Subgroup.coe_inv]
    group
  have hpsiW0 : psi (a * conjP hun a⁻¹) = s + actV hun s := by
    rw [psi_comm_eq hun a _ hW0, hpsia]
  have hpsiX : psi (⟨x, hxP⟩ : ↥P) = s + actV hun s := by
    rw [← hs, kuDeltaLin_apply]
  have hcz : (a * conjP hun a⁻¹)⁻¹ * (⟨x, hxP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [← psi_eq_zero_iff, psi_mul, psi_inv, hpsiW0, hpsiX, neg_add_cancel]
  rw [h.center_P_eq] at hcz
  have hsq1 : (a * conjP hun a⁻¹) ^ 2 = 1 := sq_comm_eq_one h hun hB a
  rcases KuZCore.mem_zpowers_cases h.kuZCore_P.z_sq hcz with hc1 | hc2
  · have hXW : (a * conjP hun a⁻¹) = ⟨x, hxP⟩ := inv_mul_eq_one.mp hc1
    have e : ((a * conjP hun a⁻¹ : ↥P) : G) = x := congrArg Subtype.val hXW
    have h2 := congrArg Subtype.val hsq1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [← e]
    exact h2
  · have hzc : (⟨z, h.zP_mem⟩ : ↥P) ∈ Subgroup.center ↥P := by
      rw [h.center_P_eq]
      exact Subgroup.mem_zpowers _
    have hcomm : Commute (a * conjP hun a⁻¹) (⟨z, h.zP_mem⟩ : ↥P) :=
      Subgroup.mem_center_iff.mp hzc (a * conjP hun a⁻¹)
    have hXW : (⟨x, hxP⟩ : ↥P) = (a * conjP hun a⁻¹) * (⟨z, h.zP_mem⟩ : ↥P) := by
      rw [← hc2, mul_inv_cancel_left]
    have hsq : (⟨x, hxP⟩ : ↥P) ^ 2 = 1 := by
      rw [hXW, hcomm.mul_pow, hsq1, one_mul, sq]
      exact h.kuZCore_P.z_sq
    have h2 := congrArg Subtype.val hsq
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2

theorem kuW_comm_mem (h : KuHyp G T M H P z) {a b : G} (ha : a ∈ kuW P H) (hb : b ∈ kuW P H) :
    a * b = b * a := by
  haveI := h.isEA_quot_P
  obtain ⟨u, hu, hcos⟩ := h.exists_u_coset
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  have hγ : ∀ v, actV hun (actV hun v) = v := fun v => actV_involutive hun huu v
  rw [kuW_eq_psiPre h hu hcos] at ha hb
  obtain ⟨haP, hsa⟩ := mem_psiPre_iff.mp ha
  obtain ⟨hbP, hsb⟩ := mem_psiPre_iff.mp hb
  have hp : KuZCore.pairQ (⟨a, haP⟩ : ↥P) ⟨b, hbP⟩ = 0 := pairQ_eq_zero_of_range h hun hγ hsa hsb
  have e : sgn ⁅(⟨a, haP⟩ : ↥P), (⟨b, hbP⟩ : ↥P)⁆ = 0 := hp
  have e1 : ⁅(⟨a, haP⟩ : ↥P), (⟨b, hbP⟩ : ↥P)⁆ = 1 := sgn_eq_zero_iff_gen.mp e
  have e2 : ⁅a, b⁆ = (1 : G) := congrArg Subtype.val e1
  exact commutatorElement_eq_one_iff_mul_comm.mp e2

theorem isElemAbelian_kuW (h : KuHyp G T M H P z) : IsElemAbelian 2 (kuW P H) :=
  ⟨⟨⟨fun a b => Subtype.ext (h.kuW_comm_mem a.2 b.2)⟩⟩, fun _ hx => h.kuW_sq_eq_one hx⟩

theorem H_le_normalizer_kuW (h : KuHyp G T M H P z) :
    H ≤ Subgroup.normalizer (kuW P H : Set G) :=
  le_normalizer_commutator_of h.hNormP (le_normalizer_pCoreOf_self H)

theorem psi_eq_zero_iff_mem_zpowers (h : KuHyp G T M H P z) {v : G} (hv : v ∈ P) :
    psi (⟨v, hv⟩ : ↥P) = 0 ↔ v ∈ Subgroup.zpowers z := by
  rw [psi_eq_zero_iff, h.center_P_eq]
  constructor
  · intro hc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  · intro hm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩

theorem eq_or_z_mul_of_psi_eq (h : KuHyp G T M H P z) {a b : G} (ha : a ∈ P) (hb : b ∈ P)
    (hab : psi (⟨b, hb⟩ : ↥P) = psi (⟨a, ha⟩ : ↥P)) : b = a ∨ b = z * a := by
  haveI := h.isEA_quot_P
  have h0 : psi ((⟨b, hb⟩ : ↥P) * (⟨a, ha⟩ : ↥P)⁻¹) = 0 := by
    rw [psi_mul, psi_inv (⟨a, ha⟩ : ↥P), hab, add_neg_cancel]
  have hc : ((⟨b, hb⟩ : ↥P) * (⟨a, ha⟩ : ↥P)⁻¹) ∈ Subgroup.zpowers (⟨z, h.zP_mem⟩ : ↥P) := by
    rw [← h.center_P_eq]
    exact (psi_eq_zero_iff _).mp h0
  have hm : b * a⁻¹ = 1 ∨ b * a⁻¹ = z := by
    rcases KuZCore.mem_zpowers_cases h.kuZCore_P.z_sq hc with h1 | h1
    · left
      have := congrArg Subtype.val h1
      simpa using this
    · right
      have := congrArg Subtype.val h1
      simpa using this
  rcases hm with h1 | h1
  · exact Or.inl (mul_inv_eq_one.mp h1)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h1)

theorem exists_shear (h : KuHyp G T M H P z) {v : G} (hv : v ∈ P) (hvz : v ∉ Subgroup.zpowers z) :
    ∃ p ∈ P, p * v * p⁻¹ = z * v := by
  obtain ⟨p, hp, hc⟩ := h.exists_comm_eq_z hv hvz
  refine ⟨p, hp, ?_⟩
  rw [commutatorElement_def] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

theorem psi_conj_eq {P : Subgroup G} [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) (q : ↥P) (hgq : g * (q : G) * g⁻¹ ∈ P) :
    psi (⟨g * (q : G) * g⁻¹, hgq⟩ : ↥P) = actV hg (psi q) :=
  (actV_mk hg q).symm

theorem actV_cube {P : Subgroup G} [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {x : G} (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hxxx : x * (x * x) = 1)
    (v : Additive (↥P ⧸ Subgroup.center ↥P)) :
    actV hxN (actV hxN (actV hxN v)) = v := by
  have hid3 : actV (mul_mem hxN (mul_mem hxN hxN)) = LinearMap.id := actV_eq_id_of_eq_one _ hxxx
  have e2 := actV_mul hxN hxN v
  have e := actV_mul hxN (mul_mem hxN hxN) v
  calc actV hxN (actV hxN (actV hxN v)) = actV hxN (actV (mul_mem hxN hxN) v) := by rw [e2]
    _ = actV (mul_mem hxN (mul_mem hxN hxN)) v := by rw [e]
    _ = v := by rw [hid3, LinearMap.id_apply]

theorem exists_H_conj_of_psi_eq (h : KuHyp G T M H P z) {v w' : G} (hv : v ∈ P) (hw' : w' ∈ P)
    (hw'z : w' ∉ Subgroup.zpowers z) (hpsi : psi (⟨w', hw'⟩ : ↥P) = psi (⟨v, hv⟩ : ↥P)) :
    ∃ p ∈ H, p * v * p⁻¹ = w' := by
  have hvz : v ∉ Subgroup.zpowers z := fun hvz =>
    hw'z ((h.psi_eq_zero_iff_mem_zpowers hw').mp
      (hpsi.trans ((h.psi_eq_zero_iff_mem_zpowers hv).mpr hvz)))
  rcases h.eq_or_z_mul_of_psi_eq hv hw' hpsi with h1 | h1
  · exact ⟨1, H.one_mem, by simp [h1]⟩
  · obtain ⟨p, hp, hpv⟩ := h.exists_shear hv hvz
    exact ⟨p, CFSG.LieType.BorelTits.pCoreOf_le 2 H (h.P_le_pCore_H hp), by rw [h1]; exact hpv⟩

theorem H_transitive_kuW (h : KuHyp G T M H P z) {w w' : G} (hw : w ∈ kuW P H)
    (hwz : w ∉ Subgroup.zpowers z) (hw' : w' ∈ kuW P H) (hw'z : w' ∉ Subgroup.zpowers z) :
    ∃ g ∈ H, g * w * g⁻¹ = w' := by
  haveI := h.isEA_quot_P
  obtain ⟨u, hu, hcos⟩ := h.exists_u_coset
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  have hWR : kuW P H = psiPre (LinearMap.range (kuDeltaLin (actV hun))) :=
    kuW_eq_psiPre h hu hcos
  set R := LinearMap.range (kuDeltaLin (actV hun))
  obtain ⟨x, hxH, hxord, hfixx⟩ := h.exists_x
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := h.hNormP hxH
  have hx3 : x ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hxxx : x * (x * x) = 1 := by
    rw [← pow_three]
    exact hx3
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [h.hCz] at hxH
    exact hxH
  have hxz : Commute x z := (Subgroup.mem_centralizer_iff.mp hxC z (Set.mem_singleton z)).symm
  have hX3 : ∀ v, actV hxN (actV hxN (actV hxN v)) = v := actV_cube hxN hxxx
  have hfix : ∀ v, actV hxN v = v → v = 0 :=
    fun v hv => actV_fixed_zero h hxN hx3 hxz hfixx v hv
  have hfin : Module.finrank (ZMod 2) R = 2 := by
    have hc := card_kuW h
    rw [hWR, card_psiPre, h.card_center_P] at hc
    have h4 : Nat.card R = 4 := by omega
    have hpow : Nat.card R = 2 ^ Module.finrank (ZMod 2) R := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] <;> simp [ZMod.card]
    have h16 : 2 ^ Module.finrank (ZMod 2) R = 2 ^ 2 :=
      (hpow.symm.trans h4).trans (by norm_num)
    exact Nat.pow_right_injective (le_refl 2) h16
  have hlift : ∀ r ∈ R, ∃ q : ↥P, psi q = r := fun r _ => by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul r)
    exact ⟨q, congrArg Additive.ofMul hq⟩
  have hσR : ∀ v ∈ R, actV hxN v ∈ R := by
    intro v hv
    obtain ⟨q, rfl⟩ := hlift v hv
    have hqW : (q : G) ∈ kuW P H := by
      rw [hWR]
      exact mem_psiPre_iff.mpr ⟨q.2, hv⟩
    have hxq : x * (q : G) * x⁻¹ ∈ kuW P H :=
      (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_kuW hxH) (q : G)).mp hqW
    have hxqP : x * (q : G) * x⁻¹ ∈ P := h.kuW_le_P hxq
    rw [← psi_conj_eq hxN q hxqP]
    have hmem : x * (q : G) * x⁻¹ ∈ psiPre R := by
      rw [← hWR]
      exact hxq
    exact (mem_psiPre_iff.mp hmem).2
  rw [hWR] at hw hw'
  obtain ⟨hwP, hpw⟩ := mem_psiPre_iff.mp hw
  obtain ⟨hw'P, hpw'⟩ := mem_psiPre_iff.mp hw'
  have hr0 : psi (⟨w, hwP⟩ : ↥P) ≠ 0 := fun h0 =>
    hwz ((h.psi_eq_zero_iff_mem_zpowers hwP).mp h0)
  have hr'0 : psi (⟨w', hw'P⟩ : ↥P) ≠ 0 := fun h0 =>
    hw'z ((h.psi_eq_zero_iff_mem_zpowers hw'P).mp h0)
  rcases orbit_of_nonzero R hfin (actV hxN) hX3 hfix hσR hpw hr0 hpw' with h0 | h0 | h0 | h0
  · exact absurd h0 hr'0
  · exact h.exists_H_conj_of_psi_eq hwP hw'P hw'z h0
  · have hxwP : x * w * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxN w).mp hwP
    have hxw : psi (⟨x * w * x⁻¹, hxwP⟩ : ↥P) = actV hxN (psi (⟨w, hwP⟩ : ↥P)) :=
      psi_conj_eq hxN ⟨w, hwP⟩ hxwP
    obtain ⟨p, hp, hpc⟩ := h.exists_H_conj_of_psi_eq hxwP hw'P hw'z (h0.trans hxw.symm)
    refine ⟨p * x, H.mul_mem hp hxH, ?_⟩
    rw [← hpc]
    group
  · have hxxP : x * x * w * (x * x)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (mul_mem hxN hxN) w).mp hwP
    have hxx : psi (⟨x * x * w * (x * x)⁻¹, hxxP⟩ : ↥P) =
        actV hxN (actV hxN (psi (⟨w, hwP⟩ : ↥P))) := by
      have e := psi_conj_eq (mul_mem hxN hxN) (⟨w, hwP⟩ : ↥P) hxxP
      rw [actV_mul hxN hxN] at e
      exact e
    obtain ⟨p, hp, hpc⟩ := h.exists_H_conj_of_psi_eq hxxP hw'P hw'z (h0.trans hxx.symm)
    refine ⟨p * (x * x), H.mul_mem hp (H.mul_mem hxH hxH), ?_⟩
    rw [← hpc]
    group

theorem H_le_normalizer_kuA (h : KuHyp G T M H P z) :
    H ≤ Subgroup.normalizer (kuA P H : Set G) :=
  le_normalizer_inf_of (le_normalizer_pCoreOf_self H)
    (le_normalizer_centralizer_of h.H_le_normalizer_kuW)

theorem le_centralizer_kuW (h : KuHyp G T M H P z) :
    kuW P H ≤ Subgroup.centralizer (kuW P H : Set G) := by
  intro x hx
  have hc := h.isElemAbelian_kuW.1
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro k hk
  have := congrArg Subtype.val (hc.is_comm.comm ⟨k, hk⟩ ⟨x, hx⟩)
  simpa using this

theorem P_inf_centralizer_kuW (h : KuHyp G T M H P z) :
    P ⊓ Subgroup.centralizer (kuW P H : Set G) = kuW P H := by
  haveI := h.isEA_quot_P
  obtain ⟨u, hu, hcos⟩ := h.exists_u_coset
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hun := h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  have hγ : ∀ v, actV hun (actV hun v) = v := fun v => actV_involutive hun huu v
  have hWR : kuW P H = psiPre (LinearMap.range (kuDeltaLin (actV hun))) :=
    kuW_eq_psiPre h hu hcos
  set R := LinearMap.range (kuDeltaLin (actV hun)) with hR
  have hlift : ∀ r ∈ R, ∃ q : ↥P, psi q = r := fun r _ => by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul r)
    exact ⟨q, congrArg Additive.ofMul hq⟩
  have hBpsi : ∀ a b : ↥P, h.kuZCore_P.commForm (psi a) (psi b) = KuZCore.pairQ a b :=
    fun a b => by
      rw [h.kuZCore_P.commForm_apply]
      exact h.kuZCore_P.pairV_mk a b
  have hiso : R ≤ h.kuZCore_P.commForm.orthogonal R := by
    intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨a, rfl⟩ := hlift n hn
    obtain ⟨b, rfl⟩ := hlift m hm
    rw [hBpsi]
    exact pairQ_eq_zero_of_range h hun hγ hn hm
  have hfin : Module.finrank (ZMod 2) R = 2 := by
    have hc := card_kuW h
    rw [hWR, card_psiPre, h.card_center_P] at hc
    have h4 : Nat.card R = 4 := by omega
    have hpow : Nat.card R = 2 ^ Module.finrank (ZMod 2) R := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] <;> simp [ZMod.card]
    have h16 : 2 ^ Module.finrank (ZMod 2) R = 2 ^ 2 :=
      (hpow.symm.trans h4).trans (by norm_num)
    exact Nat.pow_right_injective (le_refl 2) h16
  apply le_antisymm
  · intro p hp
    obtain ⟨hpP, hpC⟩ := hp
    have horth : psi (⟨p, hpP⟩ : ↥P) ∈ h.kuZCore_P.commForm.orthogonal R := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨q, rfl⟩ := hlift n hn
      have hqW : (q : G) ∈ kuW P H := by
        rw [hWR]
        refine mem_psiPre_iff.mpr ⟨q.2, ?_⟩
        show psi (⟨(q : G), q.2⟩ : ↥P) ∈ R
        rw [show (⟨(q : G), q.2⟩ : ↥P) = q from rfl]
        exact hn
      have hcomm : (q : G) * p = p * (q : G) := Subgroup.mem_centralizer_iff.mp hpC (q : G) hqW
      have e1 : ⁅q, (⟨p, hpP⟩ : ↥P)⁆ = 1 := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hcomm)
      have e : sgn ⁅q, (⟨p, hpP⟩ : ↥P)⁆ = 0 := sgn_eq_zero_iff_gen.mpr e1
      rw [hBpsi]
      exact e
    have hdim : Module.finrank (ZMod 2) (h.kuZCore_P.commForm.orthogonal R) = 2 := by
      have := LinearMap.BilinForm.finrank_orthogonal h.kuZCore_P.commForm_nondegenerate R
      have h4 := h.finrank_quotP
      omega
    have heq : R = h.kuZCore_P.commForm.orthogonal R :=
      Submodule.eq_of_le_of_finrank_eq hiso (hfin.trans hdim.symm)
    have hpR : psi (⟨p, hpP⟩ : ↥P) ∈ R := by
      rw [heq]
      exact horth
    rw [hWR]
    exact mem_psiPre_iff.mpr ⟨hpP, hpR⟩
  · intro x hx
    exact ⟨h.kuW_le_P hx, h.le_centralizer_kuW hx⟩

theorem kuA_inf_P (h : KuHyp G T M H P z) : kuA P H ⊓ P = kuW P H := by
  unfold kuA
  ext x
  constructor
  · rintro ⟨⟨_, hxC⟩, hxP⟩
    have hx : x ∈ P ⊓ Subgroup.centralizer (kuW P H : Set G) := ⟨hxP, hxC⟩
    rwa [h.P_inf_centralizer_kuW] at hx
  · intro hx
    have hxP : x ∈ P := h.kuW_le_P hx
    exact ⟨⟨h.P_le_pCore_H hxP, h.le_centralizer_kuW hx⟩, hxP⟩

theorem kuW_le_kuA (h : KuHyp G T M H P z) : kuW P H ≤ kuA P H := by
  intro x hx
  unfold kuA
  exact ⟨h.P_le_pCore_H (h.kuW_le_P hx), h.le_centralizer_kuW hx⟩

end KuHyp

end CFSG.GH74.QTGen4.Ku
