module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64W

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G] {z j : G}

theorem mem_centralizer_Z {g : G} (hgz : g ∈ Subgroup.centralizer ({z} : Set G))
    (hgj : g ∈ Subgroup.centralizer ({j} : Set G)) :
    g ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro w hw
  rcases hw with rfl | rfl
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hgz).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hgj).symm

variable [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G} {u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
  [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]
include d

theorem rrstar_comm_rho {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G)) :
    (r * rs) * (r * t) * (r * rs)⁻¹ * (r * t)⁻¹ ∈ 𝕏(K, J) := by
  have hq := d.rrstar_mem_Y hRs hRsN hrs
  obtain ⟨hz, hj⟩ := d.rrstar_conj hRs hRsN hrs hrsj
  obtain ⟨k, hk⟩ := d.exists_of_conj_z_j hq hz hj
  have hmem : (r * rs) * (r * t) * (r * rs)⁻¹ * (r * t)⁻¹ ∈ pairNormalizers K J z j :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hq d.rho_mem_Y)
      (Subgroup.inv_mem _ hq)) (Subgroup.inv_mem _ d.rho_mem_Y)
  rw [← bar_eq_one_iff _ hmem]
  rw [show bar 𝕏(K, J) hmem = bar 𝕏(K, J) hq * bar 𝕏(K, J) d.rho_mem_Y *
    (bar 𝕏(K, J) hq)⁻¹ * (bar 𝕏(K, J) d.rho_mem_Y)⁻¹ from rfl, hk]
  group

theorem rrstar_inv (hne : conjSub (r * t)⁻¹ J ≠ K) {Rstar : Subgroup G}
    (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G)) :
    ∀ x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, (r * rs) * x * (r * rs)⁻¹ = x⁻¹ := by
  have hΩ := d.c.hΩ
  have hUs := d.Rstar_inf_eq hRs hRsN
  have hrsU : rs ∉ conjSub (r * t)⁻¹ (Subgroup.zpowers v) := by
    intro h
    rw [← hUs] at h
    exact hrsj h.2
  have hquat : IsQuatSub Rstar :=
    isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In d.Kstar_mem hRs)
  have hzRs : IsUniqueInvolution Rstar z := AscL62.isUniqueInvolution_of_le
    d.isUniqueInvolution_J' hRs.1 (mem_of_isSylow2In d.isUniqueInvolution_J' hRs)
  have hcard : Nat.card Rstar = 2 * Nat.card ↥(conjSub (r * t)⁻¹ (Subgroup.zpowers v)) := by
    rw [d.natCard_Ustar, ← d.c.natCard_R]
    exact natCard_isSylow2In_eq hΩ d.Kstar_mem d.c.hK hRs d.c.hR
  have h1 : ∀ w ∈ conjSub (r * t)⁻¹ (Subgroup.zpowers v), rs * w * rs⁻¹ = w⁻¹ :=
    fun w hw => AscL62.conj_eq_inv_of_not_mem hquat hzRs (d.Ustar_le_Rstar hRs hRsN)
      (AscL62.isCyclic_conjSub _ inferInstance) hcard hrs hrsU hw
  have h2 : ∀ w ∈ Subgroup.zpowers u, rs * w * rs⁻¹ = w := fun w hw =>
    d.comm_of_twin d.Kstar_mem d.c.hK hne d.isUniqueInvolution_J' d.c.hz (hRs.1 hrs) (hRsN hrs)
      (d.c.hUK hw) (Subgroup.mem_sup_left hw)
  have h3 : ∀ w ∈ conjSub (r * t)⁻¹ (Subgroup.zpowers v), r * w * r⁻¹ = w := fun w hw =>
    d.comm_of_twin d.c.hK d.Kstar_mem (Ne.symm hne) d.c.hz d.isUniqueInvolution_J'
      (d.c.hR.1 d.hr) (d.c.hRN d.hr) (conjSub_mono d.c.hVJ hw) (d.Ustar_le_UV hw)
  have hU : ∀ w ∈ Subgroup.zpowers u, (r * rs) * w * (r * rs)⁻¹ = w⁻¹ := by
    intro w hw
    calc (r * rs) * w * (r * rs)⁻¹ = r * (rs * w * rs⁻¹) * r⁻¹ := by group
      _ = w⁻¹ := by rw [h2 w hw, d.c.conj_U_of_not_mem d.hr d.hru hw]
  have hUs' : ∀ w ∈ conjSub (r * t)⁻¹ (Subgroup.zpowers v),
      (r * rs) * w * (r * rs)⁻¹ = w⁻¹ := by
    intro w hw
    calc (r * rs) * w * (r * rs)⁻¹ = r * (rs * w * rs⁻¹) * r⁻¹ := by group
      _ = w⁻¹ := by rw [h1 w hw, h3 w⁻¹ (Subgroup.inv_mem _ hw)]
  have hc := d.rrstar_comm_rho hRs hRsN hrs hrsj
  have hcN : (r * rs) * (r * t) * (r * rs)⁻¹ * (r * t)⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
    have hq : r * rs ∈ Subgroup.normalizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (d.c.hRN d.hr) (hRsN hrs)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hq d.rho_mem_normalizer)
      (Subgroup.inv_mem _ hq)) (Subgroup.inv_mem _ d.rho_mem_normalizer)
  have hcc := d.centralizes_of_mem_X hc hcN
  have hV : ∀ x ∈ Subgroup.zpowers v, (r * rs) * x * (r * rs)⁻¹ = x⁻¹ := by
    intro x hx
    have hy : (r * t)⁻¹ * x * (r * t)⁻¹⁻¹ ∈ conjSub (r * t)⁻¹ (Subgroup.zpowers v) :=
      conj_mem_conjSub hx
    have e : (r * rs) * x * (r * rs)⁻¹ =
        ((r * rs) * (r * t) * (r * rs)⁻¹ * (r * t)⁻¹) * ((r * t) *
          ((r * rs) * ((r * t)⁻¹ * x * (r * t)⁻¹⁻¹) * (r * rs)⁻¹) * (r * t)⁻¹) *
        ((r * rs) * (r * t) * (r * rs)⁻¹ * (r * t)⁻¹)⁻¹ := by group
    rw [e, hUs' _ hy]
    have e2 : (r * t) * ((r * t)⁻¹ * x * (r * t)⁻¹⁻¹)⁻¹ * (r * t)⁻¹ = x⁻¹ := by group
    rw [e2]
    exact hcc x⁻¹ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hx))
  intro x hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commutes d.c.hUV hx
  calc (r * rs) * (x₁ * x₂) * (r * rs)⁻¹ =
        ((r * rs) * x₁ * (r * rs)⁻¹) * ((r * rs) * x₂ * (r * rs)⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [hU x₁ hx₁, hV x₂ hx₂]
    _ = (x₁ * x₂)⁻¹ := by rw [d.c.hUV x₁ hx₁ x₂ hx₂, mul_inv_rev]

theorem rrstar_not_centralizes (hne : conjSub (r * t)⁻¹ J ≠ K) {Rstar : Subgroup G}
    (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G)) :
    ¬ ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, (r * rs) * w * (r * rs)⁻¹ = w := by
  intro hcen
  have hu : u ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have h1 := (hcen u hu).symm.trans (d.rrstar_inv hne hRs hRsN hrs hrsj u hu)
  have huu : u ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel u
  have h2 := orderOf_dvd_of_pow_eq_one huu
  have h4 := d.c.four_le_U
  rw [Nat.card_zpowers] at h4
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem rho_pow_three_mul (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) (k : ℤ) :
    bar 𝕏(K, J) d.rho_mem_Y ^ (3 * k) = 1 ∨
      bar 𝕏(K, J) d.rho_mem_Y ^ (3 * k) = bar 𝕏(K, J) d.rho_mem_Y ^ (3 : ℤ) := by
  have h6 : bar 𝕏(K, J) d.rho_mem_Y ^ (6 : ℤ) = 1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast, ← d.orderOf_rho hA]
    exact pow_orderOf_eq_one _
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [show 3 * (2 * m) = 6 * m by ring, zpow_mul, h6, one_zpow]
  · right
    rw [show 3 * (2 * m + 1) = 6 * m + 3 by ring, zpow_add, zpow_mul, h6, one_zpow, one_mul]

theorem mem_X_or_rrstar (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J)
    {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G))
    {y : G} (hyY : y ∈ pairNormalizers K J z j) (hyz : y * z * y⁻¹ = z)
    (hyj : y * j * y⁻¹ = j) : y ∈ 𝕏(K, J) ∨ (r * rs)⁻¹ * y ∈ 𝕏(K, J) := by
  have hne := d.Kstar_ne hA
  have hq := d.rrstar_mem_Y hRs hRsN hrs
  obtain ⟨hqz, hqj⟩ := d.rrstar_conj hRs hRsN hrs hrsj
  have hq3 : bar 𝕏(K, J) hq = bar 𝕏(K, J) d.rho_mem_Y ^ (3 : ℤ) := by
    obtain ⟨k, hk⟩ := d.exists_of_conj_z_j hq hqz hqj
    rcases d.rho_pow_three_mul hA k with h | h
    · exfalso
      have hqX : r * rs ∈ 𝕏(K, J) := (bar_eq_one_iff _ hq).mp (hk.trans h)
      exact d.rrstar_not_centralizes hne hRs hRsN hrs hrsj
        (d.centralizes_of_mem_X hqX (Subgroup.mul_mem _ (d.c.hRN d.hr) (hRsN hrs)))
    · exact hk.trans h
  obtain ⟨k, hk⟩ := d.exists_of_conj_z_j hyY hyz hyj
  rcases d.rho_pow_three_mul hA k with h | h
  · exact Or.inl ((bar_eq_one_iff _ hyY).mp (hk.trans h))
  · exact Or.inr ((bar_eq_bar_iff _ hq hyY).mp (hq3.trans (h.symm.trans hk.symm)))

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
