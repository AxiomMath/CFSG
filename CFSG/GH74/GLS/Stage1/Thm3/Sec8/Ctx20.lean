module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx17

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem t_sq (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ : G} (hy₁S : y₁ ∈ S)
    (hy₁sq : y₁ * y₁ = z) (hy : y₁ * u * y₁⁻¹ = u * z) :
    (y₁ * (h⁻¹ * z * h)) * (y₁ * (h⁻¹ * z * h)) = 1 := by
  have hconj := hs.conj_z₁ hII hy₁S hy
  calc (y₁ * (h⁻¹ * z * h)) * (y₁ * (h⁻¹ * z * h))
      = (y₁ * (h⁻¹ * z * h) * y₁⁻¹) * (y₁ * y₁) * (h⁻¹ * z * h) := by group
    _ = ((h⁻¹ * z * h) * z) * z * (h⁻¹ * z * h) := by rw [hconj, hy₁sq]
    _ = (h⁻¹ * z * h) * (z * z) * (h⁻¹ * z * h) := by group
    _ = 1 := by
      rw [hs.z_sq, mul_one]
      calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
        _ = 1 := by rw [hs.z_sq]; group

theorem t_comm_y (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁)
    (hyW : y₁ * y₂ ∈ Wsub S U) :
    (y₁ * (h⁻¹ * z * h)) * (y₁ * y₂) = (y₁ * y₂) * (y₁ * (h⁻¹ * z * h)) := by
  have hcU : h⁻¹ * z * h ∈ U := hs.hz_inv_mem_U
  have hcy : (h⁻¹ * z * h) * (y₁ * y₂) = (y₁ * y₂) * (h⁻¹ * z * h) :=
    (Subgroup.mem_centralizer_iff.1 hyW.2) _ hcU
  have hy₁y : (y₁ * y₂) * y₁ = y₁ * (y₁ * y₂) := by
    calc (y₁ * y₂) * y₁ = y₁ * (y₂ * y₁) := by group
      _ = y₁ * (y₁ * y₂) := by rw [← hc]
  calc (y₁ * (h⁻¹ * z * h)) * (y₁ * y₂) = y₁ * ((h⁻¹ * z * h) * (y₁ * y₂)) := by group
    _ = y₁ * ((y₁ * y₂) * (h⁻¹ * z * h)) := by rw [hcy]
    _ = (y₁ * (y₁ * y₂)) * (h⁻¹ * z * h) := by group
    _ = ((y₁ * y₂) * y₁) * (h⁻¹ * z * h) := by rw [hy₁y]
    _ = (y₁ * y₂) * (y₁ * (h⁻¹ * z * h)) := by group

theorem t_conj_u (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ : G} (hy : y₁ * u * y₁⁻¹ = u * z) :
    (y₁ * (h⁻¹ * z * h)) * u * (y₁ * (h⁻¹ * z * h))⁻¹ = u * z := by
  have hcU : h⁻¹ * z * h ∈ U := hs.hz_inv_mem_U
  have hcu : (h⁻¹ * z * h) * u * (h⁻¹ * z * h)⁻¹ = u := by
    rw [hs.four_comm _ hcU u hs.u_mem]; group
  calc (y₁ * (h⁻¹ * z * h)) * u * (y₁ * (h⁻¹ * z * h))⁻¹
      = y₁ * ((h⁻¹ * z * h) * u * (h⁻¹ * z * h)⁻¹) * y₁⁻¹ := by group
    _ = y₁ * u * y₁⁻¹ := by rw [hcu]
    _ = u * z := hy

theorem t_not_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y₁ : G} (hy : y₁ * u * y₁⁻¹ = u * z) :
    y₁ * (h⁻¹ * z * h) ∉ Aof S K₁ W₂ h := by
  intro htA
  have h1 := hs.t_conj_u hy
  have h2 : (y₁ * (h⁻¹ * z * h)) * u = u * (y₁ * (h⁻¹ * z * h)) :=
    hs.A_comm hII hq hrec _ htA u (hs.U_le_A hII hq hrec hk2 hk hs.u_mem)
  have h3 : (y₁ * (h⁻¹ * z * h)) * u * (y₁ * (h⁻¹ * z * h))⁻¹ = u := by rw [h2]; group
  rw [h3] at h1
  apply hs.z_ne
  have := mul_left_cancel (a := u) (by simpa using h1.symm : u * 1 = u * z)
  exact this.symm

theorem ty_not_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y₁ y : G} (hy₁ : y₁ * u * y₁⁻¹ = u * z)
    (hyW : y ∈ Wsub S U) : (y₁ * (h⁻¹ * z * h)) * y ∉ Aof S K₁ W₂ h := by
  intro htA
  have h1 := hs.t_conj_u hy₁
  have hyu : y * u = u * y := ((hs.mem_W_iff hII).1 hyW).2
  have h2 : ((y₁ * (h⁻¹ * z * h)) * y) * u = u * ((y₁ * (h⁻¹ * z * h)) * y) :=
    hs.A_comm hII hq hrec _ htA u (hs.U_le_A hII hq hrec hk2 hk hs.u_mem)
  have h3 : ((y₁ * (h⁻¹ * z * h)) * y) * u * ((y₁ * (h⁻¹ * z * h)) * y)⁻¹ = u := by
    rw [h2]; group
  have h4 : ((y₁ * (h⁻¹ * z * h)) * y) * u * ((y₁ * (h⁻¹ * z * h)) * y)⁻¹ = u * z := by
    calc ((y₁ * (h⁻¹ * z * h)) * y) * u * ((y₁ * (h⁻¹ * z * h)) * y)⁻¹
        = (y₁ * (h⁻¹ * z * h)) * (y * u * y⁻¹) * (y₁ * (h⁻¹ * z * h))⁻¹ := by group
      _ = (y₁ * (h⁻¹ * z * h)) * u * (y₁ * (h⁻¹ * z * h))⁻¹ := by rw [hyu]; group
      _ = u * z := h1
  rw [h3] at h4
  apply hs.z_ne
  have := mul_left_cancel (a := u) (by simpa using h4 : u * 1 = u * z)
  exact this.symm

theorem exists_a (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {m : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) :
    ∃ a ∈ Aof S K₁ W₂ h, orderOf a = 2 ^ (m + 1) ∧ u = a ^ (2 ^ m) := by
  have hm : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have := hs.four_le_V₁ hII hq
    rw [hk, hm0] at this
    norm_num at this
  obtain ⟨x, hxV, hVx⟩ := Basic.exists_generator_of_cyclic hs.V₁_cyclic
  have hxo : orderOf x = 2 ^ (m + 1) := by rw [← Nat.card_zpowers, ← hVx]; exact hk
  have hx2m : x ^ (2 ^ (m + 1)) = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxsq : x ^ (2 ^ m) * x ^ (2 ^ m) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hx2m
  have hz : x ^ (2 ^ m) = z := by
    have hzV : z ∈ Vof S K₁ W₂ := hs.z_mem_V₁ hII hq (by omega) hk
    have h1 : x ^ (2 ^ m) ∈ Vof S K₁ W₂ := by rw [hVx]; exact Subgroup.npow_mem_zpowers x _
    have hne : x ^ (2 ^ m) ≠ 1 := by
      intro h'
      have h2 := orderOf_dvd_of_pow_eq_one h'
      rw [hxo] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    exact Basic.cyc_inv_unique hs.V₁_cyclic h1 hzV hxsq hs.z_sq hne hs.z_ne
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hx'V : h⁻¹ * x * h ∈ conjugate (Vof S K₁ W₂) h := by
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rw [e]; exact hxV
  have hx'A : h⁻¹ * x * h ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_right hx'V
  have hx'pow : ∀ n : ℕ, (h⁻¹ * x * h) ^ n = h⁻¹ * x ^ n * h := by
    intro n
    have := conj_pow (a := h⁻¹) (b := x) (i := n)
    rwa [inv_inv] at this
  have hx'z : (h⁻¹ * x * h) ^ (2 ^ m) = h⁻¹ * z * h := by rw [hx'pow, hz]
  have hx'2m : (h⁻¹ * x * h) ^ (2 ^ (m + 1)) = 1 := by rw [hx'pow, hx2m]; group
  have hz1sq : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hs.z_sq]; group
  have hu1 : u ≠ 1 := by
    intro h'
    exact hs.u_ne (h' ▸ one_mem _)
  have hcomm : Commute x (h⁻¹ * x * h) := hs.A_comm hII hq hrec _ hxA _ hx'A
  rcases hs.z₁_cases hII with h1 | h1
  · refine ⟨h⁻¹ * x * h, hx'A, ?_, ?_⟩
    · refine orderOf_eq_prime_pow ?_ hx'2m
      rw [hx'z, h1]; exact hu1
    · rw [hx'z, h1]
  · have hzu : z * u = u * z := hs.four_comm _ hs.z_mem _ hs.u_mem
    have hpow : (x * (h⁻¹ * x * h)) ^ (2 ^ m) = u := by
      rw [hcomm.mul_pow, hz, hx'z, h1]
      calc z * (u * z) = (z * u) * z := by group
        _ = (u * z) * z := by rw [hzu]
        _ = u := by rw [mul_assoc, hs.z_sq, mul_one]
    refine ⟨x * (h⁻¹ * x * h), mul_mem hxA hx'A, ?_, hpow.symm⟩
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [hpow]; exact hu1
    · rw [hcomm.mul_pow, hx2m, hx'2m, one_mul]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
