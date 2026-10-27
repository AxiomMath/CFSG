module

public import CFSG.LargeExtraspecial.S12I4MCls

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12I4M

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary CFSG.LargeExtraspecial.S12InspPSU
open CFSG.Blueprint.Fischer (K)

variable {d z : Fin 2 → K}

theorem ι_ne_zero (hz0 : z ≠ 0) : ι 2 z ≠ 0 := fun h => hz0 (ι_injective (by rw [h, map_zero]))

theorem lin_ne_zero (c : K) (hd0 : d ≠ 0) : c • v₀ 2 + ι 2 d ≠ 0 := fun h => hd0 (by
  have := congrArg (π 2) h
  simpa using this)

theorem tq_ι_mem_DG (hz0 : z ≠ 0) (hz : herm frob z z = 0) : tq (ι 2 z) ∈ DG 4 :=
  tq_mem_DG (ι_ne_zero hz0) (by rw [herm_ι_ι, hz])

theorem tq_lin_mem_DG (c : K) (hd0 : d ≠ 0) (hdd : herm frob d d = 0) :
    tq (c • v₀ 2 + ι 2 d) ∈ DG 4 :=
  tq_mem_DG (lin_ne_zero c hd0) (isotropic_lin hdd c)

theorem tq_v₀_ne_ι (hz0 : z ≠ 0) (hz : herm frob z z = 0) : tq (v₀ 2) ≠ tq (ι 2 z) := by
  intro h
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff (by norm_num) v₀_ne_zero herm_v₀_v₀ (ι_ne_zero hz0)
    (by rw [herm_ι_ι, hz])).1 h
  apply hz0
  have := congrArg (π 2) hc
  simpa using this

theorem tq_v₀_ne_lin (c : K) (hd0 : d ≠ 0) (hdd : herm frob d d = 0) :
    tq (v₀ 2) ≠ tq (c • v₀ 2 + ι 2 d) := by
  intro h
  obtain ⟨e, he⟩ := (tq_eq_tq_iff (by norm_num) v₀_ne_zero herm_v₀_v₀ (lin_ne_zero c hd0)
    (isotropic_lin hdd c)).1 h
  apply hd0
  have := congrArg (π 2) he
  simpa using this

theorem tq_lin_ne_lin (hd0 : d ≠ 0) (hdd : herm frob d d = 0) :
    tq (ω • v₀ 2 + ι 2 d) ≠ tq (frob ω • v₀ 2 + ι 2 d) := by
  intro h
  obtain ⟨e, he⟩ := (tq_eq_tq_iff (by norm_num) (lin_ne_zero ω hd0) (isotropic_lin hdd ω)
    (lin_ne_zero (frob ω) hd0) (isotropic_lin hdd (frob ω))).1 h
  have hπ := congrArg (π 2) he
  simp only [map_add, map_smul, π_v₀, π_ι, smul_zero, zero_add] at hπ
  have he1 : e = 1 := by
    have h1 : (1 - e) • d = 0 := by rw [sub_smul, one_smul, ← hπ, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hd0)).symm
  rw [he1, one_smul] at he
  have hv : (frob ω - ω) • v₀ 2 = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_right_cancel he
  have := (smul_eq_zero.1 hv).resolve_right v₀_ne_zero
  rw [frob_omega, add_sub_cancel_left] at this
  exact one_ne_zero this

theorem commute_v₀_ι (hz : herm frob z z = 0) :
    tq (v₀ 2) * tq (ι 2 z) = tq (ι 2 z) * tq (v₀ 2) := by
  rw [← QuotientGroup.mk_mul, tvU_commute herm_v₀_v₀ (by rw [herm_ι_ι, hz]) (herm_v₀_ι z),
    QuotientGroup.mk_mul]

theorem commute_v₀_lin (c : K) (hdd : herm frob d d = 0) :
    tq (v₀ 2) * tq (c • v₀ 2 + ι 2 d) = tq (c • v₀ 2 + ι 2 d) * tq (v₀ 2) := by
  rw [← QuotientGroup.mk_mul, tvU_commute herm_v₀_v₀ (isotropic_lin hdd c) (herm_v₀_lin c d),
    QuotientGroup.mk_mul]

theorem commute_lin_lin (c c' : K) (hdd : herm frob d d = 0) :
    tq (c • v₀ 2 + ι 2 d) * tq (c' • v₀ 2 + ι 2 d) =
      tq (c' • v₀ 2 + ι 2 d) * tq (c • v₀ 2 + ι 2 d) := by
  rw [← QuotientGroup.mk_mul, tvU_commute (isotropic_lin hdd c) (isotropic_lin hdd c')
    (by rw [herm_lin, hdd]), QuotientGroup.mk_mul]

theorem orderOf_tq_mul_tq_eq_three {a b : Fin 4 → K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : herm frob a a = 0) (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0) :
    orderOf (tq a * tq b) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (tq a * tq b) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, tvU_mul_tvU_pow_three ha hb hab,
      QuotientGroup.mk_one]
  refine orderOf_eq_prime h3 fun h1 => hab ((tq_commute_iff (by norm_num) ha0 ha hb0 hb).1 ?_)
  have e : tq a = tq b := by
    calc tq a = tq a * tq b * tq b := by rw [mul_assoc, tq_mul_self hb, mul_one]
      _ = tq b := by rw [h1, one_mul]
  rw [e]

theorem orderOf_conj_lin_mul_lin_eq_three {u : Fin 2 → K} (hd0 : d ≠ 0)
    (hdd : herm frob d d = 0) (hu : herm frob u u = 0) (hdu : herm frob d u = 1) :
    orderOf (tq (ι 2 u) * tq (ω • v₀ 2 + ι 2 d) * tq (ι 2 u) * tq (ω • v₀ 2 + ι 2 d)) = 3 := by
  have hιu : herm frob (ι 2 u) (ι 2 u) = 0 := by rw [herm_ι_ι, hu]
  have ha := isotropic_lin hdd ω
  rw [tq_mul_tq_mul_tq hιu ha]
  have hc : herm frob (ι 2 u) (ω • v₀ 2 + ι 2 d) = 1 := by
    rw [herm_ι_left, map_add, map_smul, π_v₀, π_ι, smul_zero, zero_add,
      herm_conj frob frob_frob, hdu, map_one]
  have hsm : tvU (ι 2 u) • (ω • v₀ 2 + ι 2 d) = ω • v₀ 2 + ι 2 d + ι 2 u := by
    rw [tvU_smul hιu, hc, one_smul]
  have hiso' : herm frob (tvU (ι 2 u) • (ω • v₀ 2 + ι 2 d))
      (tvU (ι 2 u) • (ω • v₀ 2 + ι 2 d)) = 0 := by rw [herm_smul_smul, ha]
  refine orderOf_tq_mul_tq_eq_three ((smul_ne_zero_iff_ne _).2 (lin_ne_zero ω hd0))
    (lin_ne_zero ω hd0) hiso' ha ?_
  rw [hsm, herm_add_left, ha, zero_add, hc]
  exact one_ne_zero

end CFSG.LargeExtraspecial.S12I4M
