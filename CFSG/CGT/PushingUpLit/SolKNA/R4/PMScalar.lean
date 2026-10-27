module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMData

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Helpers

open scoped Pointwise

variable {G : Type} [Group G]

private theorem exists_zpowers_eq_cyc {C : Subgroup G} (hC : IsCyclic ↥C) :
    ∃ c : G, Subgroup.zpowers c = C := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun y hy => ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  exact ⟨j, congrArg Subtype.val hj⟩

private theorem conj_zpow_of_eq' {u y : G} {α : ℤ} (hyu : y * u * y⁻¹ = u ^ α) (k : ℤ) :
    y * u ^ k * y⁻¹ = (u ^ k) ^ α := by
  rw [← conj_zpow, hyu, ← zpow_mul, ← zpow_mul, mul_comm]

private theorem forall_zpow_iff' {u y : G} {α : ℤ} (hyu : y * u * y⁻¹ = u ^ α) (ε : ℤ) :
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

private theorem orderOf_eq_of_pow_ne_one' {u x : G} {n : ℕ} (hn : 1 ≤ n)
    (hu : orderOf u = 2 ^ n) (hx : x ∈ Subgroup.zpowers u) (hx1 : x ^ (2 ^ n / 2) ≠ 1) :
    orderOf x = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hhalf : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; omega
  rw [hhalf] at hx1
  refine orderOf_eq_prime_pow hx1 ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu, pow_orderOf_eq_one,
    one_zpow]

private theorem pow_half_eq' {K : Subgroup G} {z c : G} (hI : IsUniqueInvolution K z)
    (hcK : c ∈ K) {N : ℕ} (hN : orderOf c = 2 ^ N) (h2 : 2 ≤ orderOf c) :
    c ^ (orderOf c / 2) = z := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, pow_zero] at hN
      omega
    · omega⟩
  have hhalf : orderOf c / 2 + orderOf c / 2 = orderOf c := by
    rw [hN, pow_succ]
    omega
  have hsq : c ^ (orderOf c / 2) * c ^ (orderOf c / 2) = 1 := by
    rw [← pow_add, hhalf, pow_orderOf_eq_one]
  have hne : c ^ (orderOf c / 2) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  exact (hI.unique _ (K.pow_mem hcK _) hsq).resolve_left hne

private theorem eq_left_of_mul_eq' {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {x₁ x₂ y₁ y₂ : G}
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ B) (hy₂ : y₂ ∈ B) (h : x₁ * y₁ = x₂ * y₂) :
    x₁ = x₂ := by
  have e : x₂⁻¹ * x₁ = y₂ * y₁⁻¹ := by
    calc x₂⁻¹ * x₁ = x₂⁻¹ * (x₁ * y₁) * y₁⁻¹ := by group
      _ = x₂⁻¹ * (x₂ * y₂) * y₁⁻¹ := by rw [h]
      _ = y₂ * y₁⁻¹ := by group
  have hmem : x₂⁻¹ * x₁ ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem hx₂) hx₁, ?_⟩
    rw [e]
    exact B.mul_mem hy₂ (B.inv_mem hy₁)
  rw [hAB, Subgroup.mem_bot] at hmem
  calc x₁ = x₂ * (x₂⁻¹ * x₁) := by group
    _ = x₂ := by rw [hmem, mul_one]

private theorem eq_right_of_mul_eq' {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {x₁ x₂ y₁ y₂ : G}
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ B) (hy₂ : y₂ ∈ B) (h : x₁ * y₁ = x₂ * y₂) :
    y₁ = y₂ := by
  rw [eq_left_of_mul_eq' hAB hx₁ hx₂ hy₁ hy₂ h] at h
  exact mul_left_cancel h

private theorem exists_mul_of_mem_sup' {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ H ⊔ N) :
    ∃ a ∈ H, ∃ b ∈ N, x = a * b := by
  have hx' : x ∈ (H : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H N hLE]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

end Helpers

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_gens :
    ∃ (u v : G) (n : ℕ), Subgroup.zpowers u = K ⊓ W ∧ Subgroup.zpowers v = V ∧
      orderOf u = 2 ^ n ∧ orderOf v = 2 ^ n ∧ 4 ≤ 2 ^ n ∧
      u ^ (2 ^ n / 2) = z ∧ v ^ (2 ^ n / 2) = t := by
  have hI := hd.tight.isUniqueInvolution
  obtain ⟨u, hu⟩ := exists_zpowers_eq_cyc hd.isCyclic_inf
  obtain ⟨v, hv⟩ := exists_zpowers_eq_cyc hd.isCyclic_V
  have huo : orderOf u = 2 ^ (r - 1) := by rw [← Nat.card_zpowers, hu, hd.natCard_inf_W]
  have hvo : orderOf v = 2 ^ (r - 1) := by rw [← Nat.card_zpowers, hv, hd.natCard_V]
  have h2 : 2 ≤ r - 1 := by
    have := hd.tight.three_le
    omega
  have h4 : 4 ≤ 2 ^ (r - 1) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) h2
  have huK : u ∈ K ⊓ W := by
    rw [← hu]
    exact Subgroup.mem_zpowers u
  have hvV : v ∈ V := by
    rw [← hv]
    exact Subgroup.mem_zpowers v
  refine ⟨u, v, r - 1, hu, hv, huo, hvo, h4, ?_, ?_⟩
  · rw [← huo]
    exact pow_half_eq' hI huK.1 huo (by omega)
  · rw [← hvo]
    exact pow_half_eq' hd.invL (hd.le_member hvV) hvo (by omega)

theorem zpow_iff {y : G} (hyz : y ∈ Subgroup.centralizer ({z} : Set G))
    (hyt : y ∈ Subgroup.centralizer ({t} : Set G)) (hyW : y ∈ Subgroup.normalizer (W : Set G))
    (ε : ℤ) : (∀ x ∈ K ⊓ W, y * x * y⁻¹ = x ^ ε) ↔ (∀ x ∈ V, y * x * y⁻¹ = x ^ ε) := by
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd.comm_of_mem
  obtain ⟨u, v, n, hu, hv, huo, hvo, h4, huz, hvt⟩ := hd.exists_gens
  have huKW : u ∈ K ⊓ W := by
    rw [← hu]
    exact Subgroup.mem_zpowers u
  have hvV : v ∈ V := by
    rw [← hv]
    exact Subgroup.mem_zpowers v
  have hVW : V ≤ W := hd.leW
  have hSL := hd.inf_member_eq
  have hbot := hd.inf_inf_eq_bot
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := hd.tight.centralizer_le_normalizer hyz
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hyt
  obtain ⟨r, hrR, hrt⟩ := hd.exists_conj_eq_mul
  have hrW : r ∈ Subgroup.normalizer (W : Set G) := hd.le_normalizer_W hrR.1
  have hLr : conjSub r L ∈ CoreAssembly.conjClass K :=
    hd.tight.hypGen.conjInvariant r L hd.memL
  have hILr : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
  have hytz : y ∈ Subgroup.centralizer ({t * z} : Set G) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyt
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hyz
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (t * z) = y * t * z := by group
      _ = t * (y * z) := by rw [h1]; group
      _ = t * z * y := by rw [h2]; group
  have hyLr : y ∈ Subgroup.normalizer ((conjSub r L : Subgroup G) : Set G) :=
    hd.tight.centralizer_le_normalizer_member hLr hILr hytz
  obtain ⟨α, hα⟩ : ∃ α : ℤ, y * u * y⁻¹ = u ^ α := by
    have h : y * u * y⁻¹ ∈ Subgroup.zpowers u := by
      rw [hu]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hyK u).mp huKW.1,
        (Subgroup.mem_normalizer_iff.mp hyW u).mp huKW.2⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨k, hk.symm⟩
  have hmemV : ∀ x ∈ L, x ∈ W → x ∈ V := fun x hxL hxW => by
    rw [← hd.inf_member_eq]
    exact ⟨hd.hWS hxW, hxL⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, y * v * y⁻¹ = v ^ β := by
    have h : y * v * y⁻¹ ∈ Subgroup.zpowers v := by
      rw [hv]
      exact hmemV _ ((Subgroup.mem_normalizer_iff.mp hyL v).mp (hd.le_member hvV))
        ((Subgroup.mem_normalizer_iff.mp hyW v).mp (hVW hvV))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨k, hk.symm⟩
  obtain ⟨v', hv'⟩ : ∃ v', v' = r * v * r⁻¹ := ⟨_, rfl⟩
  have hv'W : v' ∈ W := by
    rw [hv']
    exact (Subgroup.mem_normalizer_iff.mp hrW v).mp (hVW hvV)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℤ, y * v' * y⁻¹ = v' ^ γ := by
    have hv'L : v' ∈ conjSub r L := by
      rw [hv']
      exact conj_mem_conjSub (hd.le_member hvV)
    have h1 : y * v' * y⁻¹ ∈ conjSub r L :=
      (Subgroup.mem_normalizer_iff.mp hyLr v').mp hv'L
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
  have hLE : K ⊓ W ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer (V : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun w hw => (hcomm x hx.2 w (hVW hw)).symm)
  have hWsup : W = (K ⊓ W) ⊔ V := hd.sup_eq_inf_sup
  obtain ⟨u₁, hu₁, v₁, hv₁, hv'eq⟩ :=
    exists_mul_of_mem_sup' hLE (show v' ∈ (K ⊓ W) ⊔ V by rw [← hWsup]; exact hv'W)
  have hu₁U : u₁ ∈ Subgroup.zpowers u := by
    rw [hu]
    exact hu₁
  have hv₁V : v₁ ∈ Subgroup.zpowers v := by
    rw [hv]
    exact hv₁
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁U
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv₁V
  have hc : Commute (u ^ i) (v ^ j) := hcomm _ hu₁.2 _ (hVW hv₁)
  have hcmp : (u ^ i) ^ α * (v ^ j) ^ β = (u ^ i) ^ γ * (v ^ j) ^ γ := by
    rw [← conj_zpow_of_eq' hα, ← conj_zpow_of_eq' hβ, ← hc.mul_zpow, ← hv'eq, ← hγ, hv'eq]
    group
  have hUm : ∀ k : ℤ, (u ^ i) ^ k ∈ K ⊓ W := fun k => by
    rw [← hu]
    exact Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers u i) k
  have hVm : ∀ k : ℤ, (v ^ j) ^ k ∈ V := fun k => by
    rw [← hv]
    exact Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers v j) k
  have hαγ := eq_left_of_mul_eq' hbot (hUm α) (hUm γ) (hVm β) (hVm γ) hcmp
  have hβγ := eq_right_of_mul_eq' hbot (hUm α) (hUm γ) (hVm β) (hVm γ) hcmp
  have hm : 1 ≤ n := by
    by_contra h
    rw [show n = 0 by omega] at h4
    norm_num at h4
  have htz : v' ^ (2 ^ n / 2) = t * z := by rw [hv', conj_pow, hvt, hrt]
  have hsplit : v' ^ (2 ^ n / 2) = (u ^ i) ^ (2 ^ n / 2) * (v ^ j) ^ (2 ^ n / 2) := by
    rw [hv'eq, hc.mul_pow]
  have hzKW : z ∈ K ⊓ W := by
    rw [← huz]
    exact Subgroup.pow_mem _ huKW _
  have htV : t ∈ V := hd.memT
  have hUpow : (u ^ i) ^ (2 ^ n / 2) ∈ K ⊓ W := by
    rw [← hu]
    exact Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers u i) _
  have hVpow : (v ^ j) ^ (2 ^ n / 2) ∈ V := by
    rw [← hv]
    exact Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers v j) _
  have hU1 : (u ^ i) ^ (2 ^ n / 2) ≠ 1 := by
    intro h
    have h1 : t * z ∈ V := by
      rw [← htz, hsplit, h, one_mul]
      exact hVpow
    have hzV : z ∈ V := by simpa using V.mul_mem (V.inv_mem htV) h1
    have hmem : z ∈ K ⊓ W ⊓ V := ⟨hzKW, hzV⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hI.ne_one hmem
  have hV1 : (v ^ j) ^ (2 ^ n / 2) ≠ 1 := by
    intro h
    have h1 : t * z ∈ K ⊓ W := by
      rw [← htz, hsplit, h, mul_one]
      exact hUpow
    have htKW : t ∈ K ⊓ W := by simpa using (K ⊓ W).mul_mem h1 ((K ⊓ W).inv_mem hzKW)
    have hmem : t ∈ K ⊓ W ⊓ V := ⟨htKW, htV⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd.invL.ne_one hmem
  have hu₁o := orderOf_eq_of_pow_ne_one' hm huo (Subgroup.zpow_mem_zpowers u i) hU1
  have hv₁o := orderOf_eq_of_pow_ne_one' hm hvo (Subgroup.zpow_mem_zpowers v j) hV1
  have hdαγ : ((2 ^ n : ℕ) : ℤ) ∣ α - γ := by
    rw [← hu₁o]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub, hαγ, mul_inv_cancel])
  have hdβγ : ((2 ^ n : ℕ) : ℤ) ∣ β - γ := by
    rw [← hv₁o]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub, hβγ, mul_inv_cancel])
  rw [← hu, ← hv, forall_zpow_iff' hα ε, forall_zpow_iff' hβ ε, huo, hvo]
  constructor
  · intro h
    have := dvd_add (dvd_sub h hdαγ) hdβγ
    convert this using 1
    ring
  · intro h
    have := dvd_add (dvd_sub h hdβγ) hdαγ
    convert this using 1
    ring

theorem actsPM_V_of_actsPM_inf {y : G} (hyz : y ∈ Subgroup.centralizer ({z} : Set G))
    (hyt : y ∈ Subgroup.centralizer ({t} : Set G)) (hyW : y ∈ Subgroup.normalizer (W : Set G))
    (h : ActsPM (K ⊓ W) y) : ActsPM V y := by
  rcases h with h | h
  · left
    intro x hx
    have := (hd.zpow_iff hyz hyt hyW 1).mp (fun x hx => by simpa using h x hx) x hx
    simpa using this
  · right
    intro x hx
    have := (hd.zpow_iff hyz hyt hyW (-1)).mp (fun x hx => by simpa using h x hx) x hx
    simpa using this

theorem exists_scalar {y : G} (hyz : y ∈ Subgroup.centralizer ({z} : Set G))
    (hyt : y ∈ Subgroup.centralizer ({t} : Set G)) (hyW : y ∈ Subgroup.normalizer (W : Set G)) :
    ∃ α : ℤ, ∀ w ∈ W, y * w * y⁻¹ = w ^ α := by
  obtain ⟨u, -, -, hu, -, -, -, -, -, -⟩ := hd.exists_gens
  have huKW : u ∈ K ⊓ W := by
    rw [← hu]
    exact Subgroup.mem_zpowers u
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := hd.tight.centralizer_le_normalizer hyz
  obtain ⟨α, hα⟩ : ∃ α : ℤ, y * u * y⁻¹ = u ^ α := by
    have h : y * u * y⁻¹ ∈ Subgroup.zpowers u := by
      rw [hu]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hyK u).mp huKW.1,
        (Subgroup.mem_normalizer_iff.mp hyW u).mp huKW.2⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨k, hk.symm⟩
  have hKW : ∀ x ∈ K ⊓ W, y * x * y⁻¹ = x ^ α := by
    rw [← hu]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact conj_zpow_of_eq' hα k
  have hV := (hd.zpow_iff hyz hyt hyW α).mp hKW
  refine ⟨α, fun w hw => ?_⟩
  have hw' : w ∈ (K ⊓ W) ⊔ V := by
    rw [← hd.sup_eq_inf_sup]
    exact hw
  have hLE : K ⊓ W ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer (V : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun v hv => (hd.comm_of_mem x hx.2 v (hd.leW hv)).symm)
  obtain ⟨a, haKW, b, hbV, rfl⟩ := exists_mul_of_mem_sup' hLE hw'
  have hc : Commute a b := hd.comm_of_mem a haKW.2 b (hd.leW hbV)
  rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group, hKW a haKW, hV b hbV,
    hc.mul_zpow]

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
