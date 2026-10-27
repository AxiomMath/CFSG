module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64M

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

theorem eq_one_of_comm_of_inv {Q : Type*} [Group Q] {a q : Q} (h1 : q * a * q⁻¹ * a⁻¹ = 1)
    (h2 : a * q * a⁻¹ = q⁻¹) {k : ℕ} (hk : Odd k) (h3 : q ^ k = 1) : q = 1 := by
  have hqa : q * a = a * q := by
    calc q * a = (q * a * q⁻¹ * a⁻¹) * (a * q) := by group
      _ = a * q := by rw [h1, one_mul]
  have hc : a * q * a⁻¹ = q := by
    rw [← hqa]
    group
  have hq : q = q⁻¹ := hc.symm.trans h2
  have hq2 : q ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hq]
    exact mul_inv_cancel q
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, hq2, one_pow, one_mul] at h3
  exact h3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem UV_sylow : IsSylow2In (Subgroup.zpowers u ⊔ Subgroup.zpowers v) 𝕏(K, J) :=
  isSylow2In_of_eq_oddCoreOf_sup (sup_le d.U_le_X d.V_le_X) d.c.UV_isPGroup
    (d.c.X_eq_oddCore_sup d.hK0 d.hJ0).2.2

theorem centralizes_of_mem_X {n : G} (hnX : n ∈ 𝕏(K, J))
    (hnN : n ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, n * w * n⁻¹ = w := by
  set X := 𝕏(K, J) with hX
  set UV := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hUV
  have hXe : X = oddCoreOf X ⊔ UV := (d.c.X_eq_oddCore_sup d.hK0 d.hJ0).2.2
  have hUVX : UV ≤ X := sup_le d.U_le_X d.V_le_X
  have hUVN : UV ≤ Subgroup.normalizer ((oddCoreOf X : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hUVX hw))
  have hn : n ∈ oddCoreOf X ⊔ UV := hXe ▸ hnX
  obtain ⟨o, ho, w₀, hw₀, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hUVN hn
  have hoN : o ∈ Subgroup.normalizer (UV : Set G) := by
    have := (Subgroup.normalizer _).mul_mem hnN
      ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hw₀))
    simpa using this
  have hoc : ∀ w ∈ UV, o * w * o⁻¹ = w := by
    intro w hw
    have h1 : o * w * o⁻¹ * w⁻¹ ∈ UV :=
      UV.mul_mem ((Subgroup.mem_normalizer_iff.mp hoN w).mp hw) (UV.inv_mem hw)
    have h2 : o * w * o⁻¹ * w⁻¹ ∈ oddCoreOf X := by
      have h3 : w * o⁻¹ * w⁻¹ ∈ oddCoreOf X :=
        (Subgroup.mem_normalizer_iff.mp (hUVN hw) o⁻¹).mp ((oddCoreOf X).inv_mem ho)
      have e : o * w * o⁻¹ * w⁻¹ = o * (w * o⁻¹ * w⁻¹) := by group
      rw [e]
      exact (oddCoreOf X).mul_mem ho h3
    have h4 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) h2
      (d.c.UV_isPGroup.to_le (Subgroup.zpowers_le.mpr h1))
    calc o * w * o⁻¹ = o * w * o⁻¹ * w⁻¹ * w := by group
      _ = w := by rw [h4, one_mul]
  intro w hw
  have hcw : w₀ * w * w₀⁻¹ = w := by
    rw [d.c.UV_comm w₀ hw₀ w hw]
    group
  calc o * w₀ * w * (o * w₀)⁻¹ = o * (w₀ * w * w₀⁻¹) * o⁻¹ := by group
    _ = w := by rw [hcw, hoc w hw]

variable [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]

theorem mem_X_of_odd {b : G} (hb : b ∈ pairNormalizers K J z j) (hbz : b * z * b⁻¹ = z)
    (hbj : b * j * b⁻¹ = j) {k : ℕ} (hk : Odd k) (hbk : bar 𝕏(K, J) hb ^ k = 1)
    (hrb : bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) hb * (bar 𝕏(K, J) d.r_mem_Y)⁻¹ =
      (bar 𝕏(K, J) hb)⁻¹) : b ∈ 𝕏(K, J) := by
  have hYN := d.c.Y_le_normalizer_X d.hK0 d.hJ0
  obtain ⟨x, hx, n, ⟨hnY, hnN⟩, rfl⟩ := frattini d.c.X_le_Y hYN d.UV_sylow hb
  have hbar : bar 𝕏(K, J) hnY = bar 𝕏(K, J) hb := by
    rw [bar_eq_bar_iff]
    have := (Subgroup.mem_normalizer_iff.mp (hYN (Subgroup.inv_mem _ hnY)) x).mp hx
    have e : n⁻¹ * (x * n) = n⁻¹ * x * n⁻¹⁻¹ := by group
    rw [e]
    exact this
  have hnz : n * z * n⁻¹ = z :=
    (conj_eq_of_bar_eq _ hnY hb hbar d.c.X_le_centralizer_z).trans hbz
  have hnj : n * j * n⁻¹ = j :=
    (conj_eq_of_bar_eq _ hnY hb hbar d.c.X_le_centralizer_j).trans hbj
  have hnk : n ^ k ∈ 𝕏(K, J) := by
    rw [← bar_eq_one_iff _ (Subgroup.pow_mem _ hnY k), ← bar_pow _ hnY, hbar, hbk]
  have hnkc := d.centralizes_of_mem_X hnk (Subgroup.pow_mem _ hnN k)
  have hinv : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, w * w = 1 → n * w * n⁻¹ = w := by
    intro w hw hww
    rcases d.c.sq_eq_one_of_mem_UV hw hww with rfl | rfl | rfl | rfl
    · group
    · exact hnz
    · exact hnj
    · calc n * (z * j) * n⁻¹ = (n * z * n⁻¹) * (n * j * n⁻¹) := by group
        _ = z * j := by rw [hnz, hnj]
  have hnc := centralizes_of_odd_pow d.c.UV_isPGroup d.c.UV_comm hnN hinv hk hnkc
  have hnK : conjSub n K = K := by
    refine eq_of_le_of_le d.c.hΩ (d.c.hΩ.conjInvariant n K d.c.hK) d.c.hK d.c.U_isPGroup
      d.c.four_le_U ?_ d.c.hUK
    intro w hw
    have := conj_mem_conjSub (n := n) (d.c.hUK hw)
    rwa [hnc w (Subgroup.mem_sup_left hw)] at this
  have hcomm : n * r * n⁻¹ * r⁻¹ ∈ 𝕏(K, J) := by
    have hrK := d.c.hR.1 d.hr
    have hK : n * r * n⁻¹ * r⁻¹ ∈ K := by
      have h1 : n * r * n⁻¹ ∈ K := by
        have := conj_mem_conjSub (n := n) hrK
        rwa [hnK] at this
      exact K.mul_mem h1 (K.inv_mem hrK)
    have hr' : r⁻¹ ∉ Subgroup.zpowers u := fun h => d.hru (by simpa using Subgroup.inv_mem _ h)
    have h1 := d.c.conj_j_of_not_mem (R.inv_mem d.hr) hr'
    have h2 := d.c.conj_j_of_not_mem d.hr d.hru
    have hrz := d.c.conj_z d.hr
    have hnzj : n⁻¹ * (z * j) * n = z * j := by
      calc n⁻¹ * (z * j) * n = n⁻¹ * ((n * z * n⁻¹) * (n * j * n⁻¹)) * n := by rw [hnz, hnj]
        _ = z * j := by group
    have hj' : (n * r * n⁻¹ * r⁻¹) * j * (n * r * n⁻¹ * r⁻¹)⁻¹ = j := by
      calc (n * r * n⁻¹ * r⁻¹) * j * (n * r * n⁻¹ * r⁻¹)⁻¹ =
            n * r * n⁻¹ * (r⁻¹ * j * r⁻¹⁻¹) * n * r⁻¹ * n⁻¹ := by group
        _ = n * r * (n⁻¹ * (z * j) * n) * r⁻¹ * n⁻¹ := by rw [h1]; group
        _ = n * ((r * z * r⁻¹) * (r * j * r⁻¹)) * n⁻¹ := by rw [hnzj]; group
        _ = n * (z * z * j) * n⁻¹ := by rw [hrz, h2, mul_assoc z z j]
        _ = j := by rw [d.c.hz.sq, one_mul, hnj]
    have hjc : (n * r * n⁻¹ * r⁻¹) * j = j * (n * r * n⁻¹ * r⁻¹) := by
      calc (n * r * n⁻¹ * r⁻¹) * j =
            (n * r * n⁻¹ * r⁻¹) * j * (n * r * n⁻¹ * r⁻¹)⁻¹ * (n * r * n⁻¹ * r⁻¹) := by group
        _ = j * (n * r * n⁻¹ * r⁻¹) := by rw [hj']
    exact d.c.X_eq ▸ Subgroup.mem_sup_right ⟨hK, Subgroup.mem_centralizer_singleton_iff.mpr hjc⟩
  have h1 : bar 𝕏(K, J) hnY * bar 𝕏(K, J) d.r_mem_Y * (bar 𝕏(K, J) hnY)⁻¹ *
      (bar 𝕏(K, J) d.r_mem_Y)⁻¹ = 1 := by
    rw [bar_inv, bar_inv, bar_mul, bar_mul, bar_mul, bar_eq_one_iff]
    exact hcomm
  rw [← hbar] at hbk hrb
  have hq := eq_one_of_comm_of_inv h1 hrb hk hbk
  have hnX : n ∈ 𝕏(K, J) := (bar_eq_one_iff _ hnY).mp hq
  exact Subgroup.mul_mem _ hx hnX

theorem orderOf_rho_eq : ∃ a : ℕ, orderOf (bar 𝕏(K, J) d.rho_mem_Y) = 2 ^ a * 3 := by
  set ρb := bar 𝕏(K, J) d.rho_mem_Y with hρb
  have hm0 : orderOf ρb ≠ 0 := (orderOf_pos ρb).ne'
  have h3 : 3 ∣ orderOf ρb := by
    have h1 : (r * t) ^ (orderOf ρb) ∈ 𝕏(K, J) := by
      rw [← bar_eq_one_iff _ (Subgroup.pow_mem _ d.rho_mem_Y _), ← bar_pow]
      exact pow_orderOf_eq_one ρb
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (d.c.X_le_centralizer_z h1)
    have h4 : (r * t) ^ ((orderOf ρb : ℕ) : ℤ) * z * ((r * t) ^ ((orderOf ρb : ℕ) : ℤ))⁻¹ = z := by
      rw [zpow_natCast, h2]
      group
    have := (d.c.conj_rho_zpow_z_eq_iff d.hr d.hru d.ht d.htv _).mp h4
    exact_mod_cast this
  obtain ⟨a, e, he, hm⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  obtain ⟨e', rfl⟩ : 3 ∣ e := hcop.dvd_of_dvd_mul_left (hm ▸ h3)
  have hbY : (r * t) ^ (2 ^ a * 3) ∈ pairNormalizers K J z j := Subgroup.pow_mem _ d.rho_mem_Y _
  have hbb : bar 𝕏(K, J) hbY = ρb ^ (2 ^ a * 3) := (bar_pow _ d.rho_mem_Y _).symm
  have hcast : (3 : ℤ) * ((2 ^ a : ℕ) : ℤ) = ((2 ^ a * 3 : ℕ) : ℤ) := by push_cast; ring
  have hbX : (r * t) ^ (2 ^ a * 3) ∈ 𝕏(K, J) := by
    refine d.mem_X_of_odd hbY ?_ ?_ (k := e') (Nat.odd_mul.mp he).2 ?_ ?_
    · have := d.conj_rho_zpow_three_z ((2 ^ a : ℕ) : ℤ)
      rwa [hcast, zpow_natCast] at this
    · have := d.conj_rho_zpow_three_j ((2 ^ a : ℕ) : ℤ)
      rwa [hcast, zpow_natCast] at this
    · rw [hbb, ← pow_mul, show 2 ^ a * 3 * e' = 2 ^ a * (3 * e') by ring, ← hm]
      exact pow_orderOf_eq_one ρb
    · rw [hbb]
      have := d.bar_r_conj_zpow ((2 ^ a * 3 : ℕ) : ℤ)
      rwa [zpow_natCast] at this
  have hb1 : ρb ^ (2 ^ a * 3) = 1 := by
    rw [← hbb]
    exact (bar_eq_one_iff _ hbY).mpr hbX
  have hdvd := orderOf_dvd_of_pow_eq_one hb1
  rw [hm] at hdvd
  have h2a : 0 < 2 ^ a := pow_pos (by norm_num) a
  have h3e : 3 * e' ∣ 3 := Nat.dvd_of_mul_dvd_mul_left h2a hdvd
  have he1 : e' = 1 := by
    have := Nat.le_of_dvd (by norm_num) h3e
    have he0 : e' ≠ 0 := by
      rintro rfl
      rw [mul_zero, mul_zero] at hm
      exact hm0 hm
    omega
  exact ⟨a, by rw [hm, he1, mul_one]⟩

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
