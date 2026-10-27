module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7P1
public import Certificates.Certificate9320

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7P1

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform


theorem a7_pow_le_seven :
    ∀ y : Hat2A7.A7, y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 ∨ y ^ 5 = 1 ∨ y ^ 6 = 1 ∨
      y ^ 7 = 1 :=
  Certificates.certificate9320

theorem orderOf_le_seven (y : Hat2A7.A7) : orderOf y ≤ 7 := by
  have key : ∃ k : ℕ, 0 < k ∧ k ≤ 7 ∧ y ^ k = 1 := by
    rcases a7_pow_le_seven y with h | h | h | h | h | h | h <;>
      exact ⟨_, by norm_num, by norm_num, h⟩
  obtain ⟨k, hk0, hk7, hk⟩ := key
  exact (orderOf_le_of_pow_eq_one hk0 hk).trans hk7

section Witness

variable {G : Type} [Group G] [Finite G]

theorem sylow16_of_witness {J R : Subgroup G} (hw : A7Witness J) (hR : IsSylow2In R J) :
    16 ≤ Nat.card R := by
  obtain ⟨π, zE, hcov, -⟩ := Hat2A7.exists_cover_of_witness hw
  rw [Uniform.natCard_isSylow2In_eq hR]
  have h5040 : Nat.card (↥J ⧸ classicalInvolutionOddCore ↥J) = 5040 := hcov.card_E
  rw [h5040]
  have h4 : (Nat.factorization 5040) 2 = 4 := by decide +kernel
  rw [h4]
  norm_num

theorem odd8_of_witness {J : Subgroup G} (hw : A7Witness J)
    {u d : G} (huJ : u ∈ J) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (hu8 : 8 ≤ orderOf u)
    (hdJ : d ∈ J) (hdu : d * u = u * d) (hodd : Odd (orderOf d)) : d ∈ oddCoreOf J := by
  obtain ⟨-, hZ, ⟨ψ⟩⟩ := hw
  set N : Subgroup ↥J := classicalInvolutionOddCore ↥J with hN
  rw [mem_oddCoreOf_iff]
  refine ⟨hdJ, ?_⟩
  set a : ↥J := ⟨u, huJ⟩ with ha
  set b : ↥J := ⟨d, hdJ⟩ with hb
  rw [← QuotientGroup.eq_one_iff]
  by_contra hD1
  set U : ↥J ⧸ N := (a : ↥J ⧸ N) with hU
  set D : ↥J ⧸ N := (b : ↥J ⧸ N) with hD
  have hao : orderOf a = orderOf u := Subgroup.orderOf_mk u huJ
  have hbo : orderOf b = orderOf d := Subgroup.orderOf_mk d hdJ
  have hUdvd : orderOf U ∣ orderOf u := by
    rw [← hao]
    exact orderOf_dvd_of_pow_eq_one (by rw [hU, ← QuotientGroup.mk_pow, pow_orderOf_eq_one,
      QuotientGroup.mk_one])
  have hDdvd : orderOf D ∣ orderOf d := by
    rw [← hbo]
    exact orderOf_dvd_of_pow_eq_one (by rw [hD, ← QuotientGroup.mk_pow, pow_orderOf_eq_one,
      QuotientGroup.mk_one])
  have hUge : 8 ≤ orderOf U := by
    have hpos : 0 < orderOf U := orderOf_pos U
    have hUk : U ^ orderOf U = 1 := pow_orderOf_eq_one U
    have hmem : a ^ orderOf U ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hUk
    have hmemO : u ^ orderOf U ∈ oddCoreOf J :=
      mem_oddCoreOf_iff.mpr ⟨J.pow_mem huJ _, hmem⟩
    have hp2 : IsPGroup 2 (Subgroup.zpowers (u ^ orderOf U)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _))
    have h1 : u ^ orderOf U = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) hmemO hp2
    have : orderOf u ∣ orderOf U := orderOf_dvd_of_pow_eq_one h1
    exact hu8.trans (Nat.le_of_dvd hpos this)
  have hDodd : Odd (orderOf D) := hodd.of_dvd_nat hDdvd
  have hD3 : 3 ≤ orderOf D := by
    have hne : orderOf D ≠ 1 := fun h => hD1 (orderOf_eq_one_iff.mp h)
    obtain ⟨m, hm⟩ := hDodd
    omega
  obtain ⟨n, hn⟩ := hu2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hcop : Nat.Coprime (orderOf U) (orderOf D) := by
    have h2 : Nat.Coprime (2 ^ n) (orderOf D) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hDodd)
    rw [hn] at hUdvd
    exact Nat.Coprime.coprime_dvd_left hUdvd h2
  have hcomm : Commute U D := by
    have : a * b = b * a := Subtype.ext hdu.symm
    show U * D = D * U
    rw [hU, hD, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  have hprod : orderOf (U * D) = orderOf U * orderOf D :=
    hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have h24 : 24 ≤ orderOf (U * D) := by
    rw [hprod]
    calc 24 = 8 * 3 := by norm_num
      _ ≤ orderOf U * orderOf D := Nat.mul_le_mul hUge hD3
  set x : ↥J ⧸ N := U * D with hx
  set Z : Subgroup (↥J ⧸ N) := Subgroup.center (↥J ⧸ N) with hZdef
  set m := orderOf (QuotientGroup.mk (s := Z) x : (↥J ⧸ N) ⧸ Z) with hm
  have hxm : x ^ m ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  have hxm2 : (x ^ m) ^ 2 = 1 := by
    have := Subgroup.orderOf_dvd_natCard Z hxm
    rw [hZ] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdvd : orderOf x ∣ m * 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]
    exact hxm2
  have hle7 : m ≤ 7 := by
    have := orderOf_le_seven (ψ (QuotientGroup.mk (s := Z) x))
    rwa [MulEquiv.orderOf_eq] at this
  have hmpos : 0 < m * 2 := by
    have : 0 < m := orderOf_pos _
    omega
  have := Nat.le_of_dvd hmpos hdvd
  omega

end Witness

theorem classicalClause8_of_members {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (h : ∀ J ∈ Ω, ∃ z : G, IsClassicalMemberU .twoA7 J z) :
    ClassicalClause8 Ω where
  subnormal J hJ := by
    obtain ⟨z, hz⟩ := h J hJ
    exact ⟨z, hz.mem, hz.orderOf_eq_two, hz.subnormal⟩
  sylow16 J hJ R hR := by
    obtain ⟨z, hz⟩ := h J hJ
    exact sylow16_of_witness hz.witness hR
  odd8 J hJ u d huJ hu2 hu8 hdJ hdu hodd := by
    obtain ⟨z, hz⟩ := h J hJ
    exact odd8_of_witness hz.witness huJ hu2 hu8 hdJ hdu hodd

end CFSG.ClassicalInvolution.Hat2A7P1
