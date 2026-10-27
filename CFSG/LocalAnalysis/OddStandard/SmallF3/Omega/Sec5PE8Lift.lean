module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPLift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X] {t z : G} {T : Subgroup G}
  {π : ↥(centralizer ({z} : Set G)) →* X}

private theorem sec5pe8l_exists_pow_coprime {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (y : A) (hc : Nat.Coprime (orderOf (f y)) 6) :
    ∃ g : ℕ, Nat.Coprime (orderOf (y ^ g)) 6 ∧ f (y ^ g) = f y := by
  set n := orderOf y with hn_def
  have hn : n ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m₂, hm₂, hn₂⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by norm_num)
  have hm₂nz : m₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hn₂
    exact hn hn₂
  obtain ⟨b, m, hm₃, hm₂eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm₂nz 3 (by norm_num)
  have hn_eq : n = 2 ^ a * 3 ^ b * m := by rw [hn₂, hm₂eq]; ring
  have hm_not2 : ¬ 2 ∣ m := fun h => hm₂ (hm₂eq.symm ▸ dvd_mul_of_dvd_right h (3 ^ b))
  have hm_cop2 : Nat.Coprime m 2 :=
    Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp (mt Even.two_dvd hm_not2))
  have hm_cop3 : Nat.Coprime m 3 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm₃ |>.symm
  have hm_cop6 : Nat.Coprime m 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.coprime_mul_iff_right.mpr ⟨hm_cop2, hm_cop3⟩
  have hNd : Nat.Coprime (orderOf (f y)) (2 ^ a * 3 ^ b) := by
    have h2 : Nat.Coprime (orderOf (f y)) 2 :=
      Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hc
    have h3 : Nat.Coprime (orderOf (f y)) 3 :=
      Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hc
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2) (Nat.Coprime.pow_right b h3)
  have hN_dvd_m : orderOf (f y) ∣ m := by
    refine hNd.dvd_of_dvd_mul_left ?_
    rw [← hn_eq, hn_def]
    exact orderOf_map_dvd f y
  let g : ℕ := (Nat.chineseRemainder hNd 1 0).1
  have hgN : g ≡ 1 [MOD orderOf (f y)] := (Nat.chineseRemainder hNd 1 0).2.1
  have hg0 : g ≡ 0 [MOD 2 ^ a * 3 ^ b] := (Nat.chineseRemainder hNd 1 0).2.2
  have hpow : (y ^ g) ^ m = 1 := by
    obtain ⟨c, hc_eq⟩ := Nat.modEq_zero_iff_dvd.mp hg0
    rw [← pow_mul, hc_eq]
    have hexp : 2 ^ a * 3 ^ b * c * m = n * c := by
      rw [show 2 ^ a * 3 ^ b * c * m = (2 ^ a * 3 ^ b * m) * c by ring, ← hn_eq]
    rw [hexp, pow_mul, pow_orderOf_eq_one, one_pow]
  have hcop : Nat.Coprime (orderOf (y ^ g)) 6 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_iff_pow_eq_one.mpr hpow) hm_cop6
  have hf : f (y ^ g) = f y := by
    rw [map_pow]
    simpa using (pow_eq_pow_iff_modEq (x := f y) (n := g) (m := 1)).mpr hgN
  exact ⟨g, hcop, hf⟩

theorem sec5pe8_lift_coprime (hyp : Sec5OPHyp t z T π) (c : Sec5GBar (sec5op_Tb z T π))
    (hc : Nat.Coprime (orderOf c) 6)
    (hct : c * sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ =
      sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ * c) :
    ∃ (y : G) (hy : y ∈ sec5op_Y t z), y * t = t * y ∧ Nat.Coprime (orderOf y) 6 ∧
      sec5op_cls hyp ⟨y, hy⟩ = c := by
  have hodd : Odd (orderOf c) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hc)
  obtain ⟨y₂, hy₂, hcomm, _hy₂odd, hcls₂⟩ := sec5op_lift_odd hyp c hodd hct
  let y₀ : ↥(sec5op_Y t z) := ⟨y₂, hy₂⟩
  have hcls_y₀ : sec5op_cls hyp y₀ = c := hcls₂
  obtain ⟨g, hgcop, hgimg⟩ :=
    sec5pe8l_exists_pow_coprime (sec5op_cls hyp) y₀ (by rw [hcls_y₀]; exact hc)
  have horder : orderOf (y₂ ^ g) = orderOf (y₀ ^ g) := by
    rw [← Subgroup.orderOf_coe (y₀ ^ g)]
    have hcoe : ((y₀ ^ g : ↥(sec5op_Y t z)) : G) = y₂ ^ g := by
      rw [Subgroup.coe_pow]
    rw [hcoe]
  have hy_eq : (⟨y₂ ^ g, pow_mem hy₂ g⟩ : ↥(sec5op_Y t z)) = y₀ ^ g := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
  refine ⟨y₂ ^ g, pow_mem hy₂ g, Commute.pow_left hcomm g, ?_, ?_⟩
  · rw [horder]; exact hgcop
  · rw [hy_eq, hgimg, hcls_y₀]

end CFSG.OddStandard.SmallF3.Omega
