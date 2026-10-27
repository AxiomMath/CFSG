module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64P

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
  [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]
include d

theorem rho_cube_ne (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    bar 𝕏(K, J) d.rho_mem_Y ^ 3 ≠ 1 := by
  intro h3
  have hΩ := d.c.hΩ
  have hρiY : (r * t)⁻¹ ∈ pairNormalizers K J z j := Subgroup.inv_mem _ d.rho_mem_Y
  have hT'2 : IsPGroup 2 ↥(conjSub (r * t)⁻¹ T) := isPGroup_conjSub _ d.c.hT.2.1
  obtain ⟨P', hP', hT'P'⟩ := IsSylow2In.exists_ge hT'2 (d.conjSub_T_le_XR h3)
  obtain ⟨x, hxH, hxP⟩ := exists_conjSub_eq_of_isSylow2In hP' d.RUV_sylow
  have hxY : x ∈ pairNormalizers K J z j := (sup_le d.c.X_le_Y d.c.R_le_Y) hxH
  have hxz : x * z * x⁻¹ = z := by
    have hc : x ∈ Subgroup.centralizer ({z} : Set G) := (sup_le d.c.X_le_centralizer_z
      (d.c.hR.1.trans (le_centralizer_of_isUniqueInvolution d.c.hz))) hxH
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hLΩ : conjSub (x * (r * t)⁻¹) J ∈ Ω := hΩ.conjInvariant _ J d.c.hJ
  have hLz : IsUniqueInvolution (conjSub (x * (r * t)⁻¹) J) z := by
    have := d.c.hj.conj (x * (r * t)⁻¹)
    have e : x * (r * t)⁻¹ * j * (x * (r * t)⁻¹)⁻¹ = z := by
      calc x * (r * t)⁻¹ * j * (x * (r * t)⁻¹)⁻¹ =
            x * ((r * t)⁻¹ * j * (r * t)⁻¹⁻¹) * x⁻¹ := by group
        _ = z := by rw [d.conj_rho_inv_j, hxz]
    rwa [e] at this
  have hKL : K ≠ conjSub (x * (r * t)⁻¹) J := by
    intro h
    apply hA ((x * (r * t)⁻¹)⁻¹) (Subgroup.inv_mem _ (Subgroup.mul_mem _ hxY hρiY))
    rw [h, conjSub_inv_conjSub]
  have hSsyl : IsSylow2In (conjSub (x * (r * t)⁻¹) T) (conjSub (x * (r * t)⁻¹) J) :=
    IsSylow2In.conj d.c.hT _
  have hSB : conjSub (x * (r * t)⁻¹) T ≤ R ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
    rw [conjSub_mul, ← hxP]
    exact conjSub_mono hT'P'
  have hRB : R ≤ R ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := le_sup_left
  have hcomm : Commutes R (conjSub (x * (r * t)⁻¹) T) :=
    commutes_of_twin_of_isPGroup hΩ d.c.hK hLΩ hKL d.c.hz hLz d.c.hR.1 hSsyl.1
      (d.RUV_sylow.2.1.to_le (sup_le hRB hSB))
  have hSR : Nat.card (conjSub (x * (r * t)⁻¹) T) = Nat.card R :=
    natCard_isSylow2In_eq hΩ hLΩ d.c.hK hSsyl d.c.hR
  have hRS2 : Nat.card ↥(R ⊓ conjSub (x * (r * t)⁻¹) T) ≤ 2 :=
    card_le_two_of_le_inf hΩ d.c.hK hLΩ hKL (d.c.hR.2.1.to_le inf_le_left)
      (inf_le_left.trans d.c.hR.1) (inf_le_right.trans hSsyl.1)
  have hprod := card_sup_mul_card_inf_of_le_normalizer (AscL62.le_normalizer_of_commutes hcomm)
  rw [hSR, d.c.natCard_R] at hprod
  have hsup : R ⊔ conjSub (x * (r * t)⁻¹) T = R ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hRB hSB) ?_
    rw [d.natCard_RUV]
    nlinarith [Nat.mul_le_mul_left (Nat.card ↥(R ⊔ conjSub (x * (r * t)⁻¹) T)) hRS2]
  have hv : v ∈ R ⊔ conjSub (x * (r * t)⁻¹) T :=
    hsup ▸ Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  obtain ⟨r₁, hr₁, s₁, hs₁, hv1⟩ := exists_mul_of_mem_sup_of_commutes hcomm hv
  set e := Nat.card (Subgroup.zpowers u) / 2 with he
  have h4 := d.c.four_le_U
  have hU2 : 2 * e = Nat.card (Subgroup.zpowers u) := by
    have : 2 ∣ Nat.card (Subgroup.zpowers u) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers u) d.c.z_mem_U
      rwa [orderOf_eq_prime (by rw [pow_two]; exact d.c.hz.sq) d.c.hz.ne_one] at h
    omega
  have hR2 : Nat.card R / 2 = Nat.card (Subgroup.zpowers u) := by rw [d.c.natCard_R]; omega
  have hpowR : r₁ ^ e = 1 ∨ r₁ ^ e = z := by
    refine d.c.hz.unique _ (K.pow_mem (d.c.hR.1 hr₁) e) ?_
    rw [← pow_add, ← two_mul, hU2, ← hR2]
    exact IsQuatSub.pow_half_eq_one d.c.R_quat.1 hr₁
  have hpowS : s₁ ^ e = 1 ∨ s₁ ^ e = z := by
    refine hLz.unique _ (Subgroup.pow_mem _ (hSsyl.1 hs₁) e) ?_
    rw [← pow_add, ← two_mul, hU2, ← hR2, ← hSR]
    exact IsQuatSub.pow_half_eq_one
      (isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hLΩ hSsyl)) hs₁
  have hvj : v ^ e = j := by
    have hord : orderOf v = Nat.card (Subgroup.zpowers u) := by
      rw [← Nat.card_zpowers, d.c.natCard_U_eq_V]
    have hne : v ^ e ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hsq : v ^ e * v ^ e = 1 := by
      rw [← pow_add, ← two_mul, hU2, ← hord, pow_orderOf_eq_one]
    exact (d.c.hj.unique _ (Subgroup.pow_mem _ (d.c.hVJ (Subgroup.mem_zpowers v)) e)
      hsq).resolve_left hne
  have hve : v ^ e = r₁ ^ e * s₁ ^ e := by
    rw [hv1]
    exact (show Commute r₁ s₁ from hcomm r₁ hr₁ s₁ hs₁).mul_pow e
  rw [hvj] at hve
  rcases hpowR with h1 | h1 <;> rcases hpowS with h2 | h2 <;> rw [h1, h2] at hve
  · exact d.c.hj.ne_one (by simpa using hve)
  · exact d.c.z_ne_j (by simpa using hve.symm)
  · exact d.c.z_ne_j (by simpa using hve.symm)
  · exact d.c.hj.ne_one (by rw [hve, d.c.hz.sq])

theorem orderOf_rho (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    orderOf (bar 𝕏(K, J) d.rho_mem_Y) = 6 := by
  obtain ⟨a, ha⟩ := d.orderOf_rho_eq
  have h6 := Nat.le_of_dvd (by norm_num) (d.orderOf_rho_dvd_six hA)
  have hp1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  rw [ha] at h6 ⊢
  by_cases hp : 2 ^ a = 1
  · exfalso
    apply d.rho_cube_ne hA
    have := pow_orderOf_eq_one (bar 𝕏(K, J) d.rho_mem_Y)
    rwa [ha, hp, one_mul] at this
  · omega

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
