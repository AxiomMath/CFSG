module

public import CFSG.ClassicalInvolution.AschTight.S19NTr

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Group

variable {G : Type} [Group G]

theorem eq_left_of_mul_eq {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {x₁ x₂ y₁ y₂ : G}
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ B) (hy₂ : y₂ ∈ B) (h : x₁ * y₁ = x₂ * y₂) :
    x₁ = x₂ := by
  have e : x₂⁻¹ * x₁ = y₂ * y₁⁻¹ := by
    calc x₂⁻¹ * x₁ = x₂⁻¹ * (x₁ * y₁) * y₁⁻¹ := by group
      _ = x₂⁻¹ * (x₂ * y₂) * y₁⁻¹ := by rw [h]
      _ = y₂ * y₁⁻¹ := by group
  have hmem : x₂⁻¹ * x₁ ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem hx₂) hx₁, e ▸ B.mul_mem hy₂ (B.inv_mem hy₁)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  calc x₁ = x₂ * (x₂⁻¹ * x₁) := by group
    _ = x₂ := by rw [hmem, mul_one]

theorem eq_right_of_mul_eq {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {x₁ x₂ y₁ y₂ : G}
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ B) (hy₂ : y₂ ∈ B) (h : x₁ * y₁ = x₂ * y₂) :
    y₁ = y₂ := by
  rw [eq_left_of_mul_eq hAB hx₁ hx₂ hy₁ hy₂ h] at h
  exact mul_left_cancel h

theorem forall_zpow_iff {u y : G} {α : ℤ} (hyu : y * u * y⁻¹ = u ^ α) (ε : ℤ) :
    (∀ x ∈ Subgroup.zpowers u, y * x * y⁻¹ = x ^ ε) ↔ (orderOf u : ℤ) ∣ α - ε := by
  have key : (orderOf u : ℤ) ∣ α - ε ↔ u ^ α = u ^ ε := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]
  rw [key]
  constructor
  · intro h
    rw [← hyu]
    exact h u (Subgroup.mem_zpowers u)
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hyu, h, ← zpow_mul, ← zpow_mul, mul_comm]

theorem conj_zpow_of_eq {u y : G} {α : ℤ} (hyu : y * u * y⁻¹ = u ^ α) (k : ℤ) :
    y * u ^ k * y⁻¹ = (u ^ k) ^ α := by
  rw [← conj_zpow, hyu, ← zpow_mul, ← zpow_mul, mul_comm]

theorem orderOf_eq_of_pow_ne_one {u x : G} {n : ℕ} (hn : 1 ≤ n) (hu : orderOf u = 2 ^ n)
    (hx : x ∈ Subgroup.zpowers u) (hx1 : x ^ (2 ^ n / 2) ≠ 1) : orderOf x = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hhalf : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; omega
  rw [hhalf] at hx1
  refine orderOf_eq_prime_pow hx1 ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu, pow_orderOf_eq_one,
    one_zpow]

end Group

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_gens [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V) :
    ∃ (u v : G) (n : ℕ), Subgroup.zpowers u = K ⊓ W ∧ Subgroup.zpowers v = V ∧
      orderOf u = 2 ^ n ∧ orderOf v = 2 ^ n ∧ 4 ≤ 2 ^ n ∧
      u ^ (2 ^ n / 2) = z ∧ v ^ (2 ^ n / 2) = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hdT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨-, -, -, hcycU, -⟩ := S19B.inf_mem_USet hdT
  obtain ⟨-, -, -, hcycV, -⟩ := hdT.memV
  obtain ⟨u, hu⟩ := S19B.exists_zpowers_eq_of_isCyclic hcycU
  obtain ⟨v, hv⟩ := S19B.exists_zpowers_eq_of_isCyclic hcycV
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := S.isPGroup'.to_le (inf_le_right.trans hd.hWS)
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  have huo : orderOf u = 2 ^ n := by rw [← Nat.card_zpowers, hu, hn]
  have hvo : orderOf v = 2 ^ n := by
    rw [← Nat.card_zpowers, hv, ← S1911.card_inf_eq_card hdT, hn]
  have h4 : 4 ≤ 2 ^ n := by
    have h := (S1911.etaYForm p f G K z S W L t V hdT).four
    rwa [← S1911.card_inf_eq_card hdT, hn] at h
  have huK : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  refine ⟨u, v, n, hu, hv, huo, hvo, h4, ?_, ?_⟩
  · rw [← huo]
    exact pow_half_eq hI huK.1 huo (by omega)
  · rw [← hvo]
    exact pow_half_eq hdT.invL (S1911.le_member hdT hvV) hvo (by omega)

theorem zpow_iff [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V) {y : G}
    (hyz : y ∈ Subgroup.centralizer ({z} : Set G)) (hyt : y ∈ Subgroup.centralizer ({t} : Set G))
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (ε : ℤ) :
    (∀ x ∈ K ⊓ W, y * x * y⁻¹ = x ^ ε) ↔ (∀ x ∈ V, y * x * y⁻¹ = x ^ ε) := by
  have hd := hdT.toSec19Data
  have ht := hd.tight
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  have hcomm := S1911.comm_of_mem hd
  obtain ⟨u, v, n, hu, hv, huo, hvo, h4, huz, hvt⟩ := exists_gens hdT
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hVW : V ≤ W := hdT.leW
  have hSL := S1911.inf_member_eq hdT
  have hbot : K ⊓ W ⊓ V = ⊥ := by
    rw [eq_bot_iff, ← S1911.inf_member_eq_bot hdT]
    exact fun x hx => ⟨hx.2, hx.1.1⟩
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := (S1916.sd_normalizer_eq hd).ge hyz
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    S1911.centralizer_le_normalizer_member ht.toTightBranch hdT.memL hdT.invL hyt
  obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hdT
  have hrW : r ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hdT hrR.1
  have hLr : conjSub r L ∈ CoreAssembly.conjClass K := conjInvariant_conjClass K r L hdT.memL
  have hILr : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hdT.invL.conj r
  have hytz : y ∈ Subgroup.centralizer ({t * z} : Set G) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyt
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hyz
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (t * z) = y * t * z := by group
      _ = t * (y * z) := by rw [h1]; group
      _ = t * z * y := by rw [h2]; group
  have hyLr : y ∈ Subgroup.normalizer ((conjSub r L : Subgroup G) : Set G) :=
    S1911.centralizer_le_normalizer_member ht.toTightBranch hLr hILr hytz
  obtain ⟨α, hα⟩ : ∃ α : ℤ, y * u * y⁻¹ = u ^ α := by
    have h : y * u * y⁻¹ ∈ Subgroup.zpowers u := hu ▸
      ⟨(Subgroup.mem_normalizer_iff.mp hyK u).mp huKW.1,
        (Subgroup.mem_normalizer_iff.mp hyW u).mp huKW.2⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨k, hk.symm⟩
  have hmemV : ∀ x ∈ L, x ∈ W → x ∈ V := fun x hxL hxW => hSL ▸ ⟨hd.hWS hxW, hxL⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, y * v * y⁻¹ = v ^ β := by
    have h : y * v * y⁻¹ ∈ Subgroup.zpowers v := hv ▸
      hmemV _ ((Subgroup.mem_normalizer_iff.mp hyL v).mp (S1911.le_member hdT hvV))
        ((Subgroup.mem_normalizer_iff.mp hyW v).mp (hVW hvV))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨k, hk.symm⟩
  obtain ⟨v', hv'⟩ : ∃ v', v' = r * v * r⁻¹ := ⟨_, rfl⟩
  have hv'W : v' ∈ W := hv' ▸ (Subgroup.mem_normalizer_iff.mp hrW v).mp (hVW hvV)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℤ, y * v' * y⁻¹ = v' ^ γ := by
    have h1 : y * v' * y⁻¹ ∈ conjSub r L :=
      (Subgroup.mem_normalizer_iff.mp hyLr v').mp
        (hv' ▸ conj_mem_conjSub (S1911.le_member hdT hvV))
    have h2 : y * v' * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hyW v').mp hv'W
    have h3 : r⁻¹ * (y * v' * y⁻¹) * r ∈ Subgroup.zpowers v := by
      rw [hv]
      refine hmemV _ (mem_conjSub_iff.mp h1) ?_
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrW) _).mp h2
      rwa [inv_inv] at this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h3
    refine ⟨k, ?_⟩
    calc y * v' * y⁻¹ = r * (r⁻¹ * (y * v' * y⁻¹) * r) * r⁻¹ := by group
      _ = r * v ^ k * r⁻¹ := by rw [hk]
      _ = (r * v * r⁻¹) ^ k := conj_zpow.symm
      _ = v' ^ k := by rw [hv']
  have hLE : W ⊓ K ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer (V : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun w hw => (hcomm x hx.1 w (hVW hw)).symm)
  have hWsup := (S1911.etaYForm p f G K z S W L t V hdT).supU
  obtain ⟨u₁, hu₁, v₁, hv₁, hv'eq⟩ :=
    Sec71.exists_mul_of_mem_sup hLE (show v' ∈ W ⊓ K ⊔ V by rw [← hWsup]; exact hv'W)
  have hu₁U : u₁ ∈ Subgroup.zpowers u := hu ▸ ⟨hu₁.2, hu₁.1⟩
  have hv₁V : v₁ ∈ Subgroup.zpowers v := hv ▸ hv₁
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁U
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv₁V
  have hc : Commute (u ^ i) (v ^ j) := hcomm _ hu₁.1 _ (hVW hv₁)
  have hcmp : (u ^ i) ^ α * (v ^ j) ^ β = (u ^ i) ^ γ * (v ^ j) ^ γ := by
    rw [← conj_zpow_of_eq hα, ← conj_zpow_of_eq hβ, ← hc.mul_zpow, ← hv'eq, ← hγ, hv'eq]
    group
  have hUm : ∀ k : ℤ, (u ^ i) ^ k ∈ K ⊓ W := fun k => hu ▸ Subgroup.zpow_mem _
    (Subgroup.zpow_mem_zpowers u i) k
  have hVm : ∀ k : ℤ, (v ^ j) ^ k ∈ V := fun k => hv ▸ Subgroup.zpow_mem _
    (Subgroup.zpow_mem_zpowers v j) k
  have hαγ := eq_left_of_mul_eq hbot (hUm α) (hUm γ) (hVm β) (hVm γ) hcmp
  have hβγ := eq_right_of_mul_eq hbot (hUm α) (hUm γ) (hVm β) (hVm γ) hcmp
  have hm : 1 ≤ n := by
    by_contra h
    rw [show n = 0 by omega] at h4
    norm_num at h4
  have htz : v' ^ (2 ^ n / 2) = t * z := by rw [hv', conj_pow, hvt, hrt]
  have hsplit : v' ^ (2 ^ n / 2) = (u ^ i) ^ (2 ^ n / 2) * (v ^ j) ^ (2 ^ n / 2) := by
    rw [hv'eq, hc.mul_pow]
  have hzKW : z ∈ K ⊓ W := huz ▸ Subgroup.pow_mem _ huKW _
  have htV : t ∈ V := hdT.memT
  have hUpow : (u ^ i) ^ (2 ^ n / 2) ∈ K ⊓ W :=
    hu ▸ Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers u i) _
  have hVpow : (v ^ j) ^ (2 ^ n / 2) ∈ V :=
    hv ▸ Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers v j) _
  have hU1 : (u ^ i) ^ (2 ^ n / 2) ≠ 1 := by
    intro h
    have h1 : t * z ∈ V := by rw [← htz, hsplit, h, one_mul]; exact hVpow
    have hzV : z ∈ V := by simpa using V.mul_mem (V.inv_mem htV) h1
    have hmem : z ∈ K ⊓ W ⊓ V := ⟨hzKW, hzV⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hI.ne_one hmem
  have hV1 : (v ^ j) ^ (2 ^ n / 2) ≠ 1 := by
    intro h
    have h1 : t * z ∈ K ⊓ W := by rw [← htz, hsplit, h, mul_one]; exact hUpow
    have htKW : t ∈ K ⊓ W := by simpa using (K ⊓ W).mul_mem h1 ((K ⊓ W).inv_mem hzKW)
    have hmem : t ∈ K ⊓ W ⊓ V := ⟨htKW, htV⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hdT.invL.ne_one hmem
  have hu₁o := orderOf_eq_of_pow_ne_one hm huo (Subgroup.zpow_mem_zpowers u i) hU1
  have hv₁o := orderOf_eq_of_pow_ne_one hm hvo (Subgroup.zpow_mem_zpowers v j) hV1
  have hdαγ : ((2 ^ n : ℕ) : ℤ) ∣ α - γ := by
    rw [← hu₁o]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub, hαγ, mul_inv_cancel])
  have hdβγ : ((2 ^ n : ℕ) : ℤ) ∣ β - γ := by
    rw [← hv₁o]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub, hβγ, mul_inv_cancel])
  rw [← hu, ← hv, forall_zpow_iff hα ε, forall_zpow_iff hβ ε, huo, hvo]
  constructor
  · intro h
    have := dvd_add (dvd_sub h hdαγ) hdβγ
    convert this using 1
    ring
  · intro h
    have := dvd_add (dvd_sub h hdβγ) hdαγ
    convert this using 1
    ring

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N
