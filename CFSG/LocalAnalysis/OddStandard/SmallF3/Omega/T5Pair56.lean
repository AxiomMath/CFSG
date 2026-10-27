module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Step56
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PairOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma mul_self_eq_one_of_commuting_involutions {H : Type*} [Group H] {a b c : H}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) * (a * b * c) = 1 := by
  have hbc_sq : (b * c) * (b * c) = 1 := by
    have h := (show Commute b c from hbc).mul_pow 2
    simpa [pow_two, hb, hc] using h
  have ha_bc : Commute a (b * c) :=
    (show Commute a b from hab).mul_right (show Commute a c from hac)
  have hmain : (a * (b * c)) * (a * (b * c)) = 1 := by
    have h := ha_bc.mul_pow 2
    simpa [pow_two, ha, hbc_sq] using h
  simpa [mul_assoc] using hmain

theorem asc82Pair56_of (hS : Asc82SchurU43) : Asc82Pair56 := by
  intro G _ _ L hL t ht ht2 z hz
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, h⟩ := t5_exists_cover hS hL
  letI := i1; letI := i2; letI := i3
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  have hz2 : orderOf z = 2 := hz.1
  obtain ⟨K, hzK, hKL, _, _⟩ := hz.2
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hKL hzK)).1
  have htL : t ∈ L := Subgroup.map_subtype_le (Subgroup.center L) ht
  let zbar : OGroup Q := ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)
  have hz'sq : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have hzbar_sq : zbar * zbar = 1 := by
    have h' : ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
        ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, hz'sq, map_one]
      rfl
    exact h'
  have hzbar_t : invType zbar = (4, 1) := t5_phi_pocket_invType h hL hz hzL
  obtain ⟨wbar, hwbarΩ, hwbar_sq, hwbar_t, hwbar_zbar, hpi_sq, hpi_t⟩ :=
    t5_omega_pair hQ hdim hsgn hzbar_sq hzbar_t
  let Wbar : omegaGroup hQ := ⟨wbar, hwbarΩ⟩
  have hWbar_sq : Wbar * Wbar = 1 := Subtype.ext hwbar_sq
  have hwbar_ne : wbar ≠ 1 := by
    intro h1
    rw [h1, invType_one] at hwbar_t
    exact absurd hwbar_t (by decide)
  have hWbar_ne : Wbar ≠ 1 := fun hh => hwbar_ne (congrArg Subtype.val hh)
  obtain ⟨w', hw'sq, hw'φ⟩ := hO.exists_mul_self_eq_one_lift (z := Wbar) hWbar_sq
  have hw'sqG : (w' : G) * (w' : G) = 1 := by
    have := congrArg Subtype.val hw'sq
    simpa [Subgroup.coe_mul] using this
  have hw'ne : (w' : G) ≠ 1 := by
    intro h1
    have h1' : w' = 1 := Subtype.ext h1
    exact hWbar_ne (by rw [← hw'φ, h1', map_one])
  have hw2 : orderOf (w' : G) = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hw'sqG) hw'ne
  have hwI : IsI4PlusIn L (w' : G) := by
    refine (t5_isI4PlusIn_iff hL h w'.2 hw2).mpr ?_
    have hw'e : (⟨(w' : G), w'.2⟩ : ↥L) = w' := Subtype.ext rfl
    rw [hw'e, hw'φ]
    exact (t5_isI4PlusIn_omega_iff hdim hsgn (by simpa using hwbar_sq) hWbar_ne).mpr hwbar_t
  have hab : φ w' * φ ⟨z, hzL⟩ = φ ⟨z, hzL⟩ * φ w' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hw'φ]
    exact hwbar_zbar
  have hw'z' : w' * ⟨z, hzL⟩ = ⟨z, hzL⟩ * w' :=
    hO.commute_of_mul_self_eq_one hw'sq hz'sq hab
  have hwz : (w' : G) * z = z * (w' : G) := by
    have := congrArg Subtype.val hw'z'
    simpa [Subgroup.coe_mul] using this
  have ht'_center : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp ht
    have hxw : x = (⟨t, htL⟩ : ↥L) := Subtype.ext hxval
    rw [← hxw]; exact hx
  have ht'sq : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ht2])
  have hTZ : (⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ = ⟨z, hzL⟩ * ⟨t, htL⟩ :=
    (Subgroup.mem_center_iff.mp ht'_center ⟨z, hzL⟩).symm
  have hTW : (⟨t, htL⟩ : ↥L) * w' = w' * ⟨t, htL⟩ :=
    (Subgroup.mem_center_iff.mp ht'_center w').symm
  have hzw' : ⟨z, hzL⟩ * w' = w' * ⟨z, hzL⟩ := hw'z'.symm
  have hu'sq : ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ * w') *
      ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ * w') = 1 :=
    mul_self_eq_one_of_commuting_involutions ht'sq hz'sq hw'sq hTZ hTW hzw'
  have hu'_val : ((φ ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ * w') : omegaGroup hQ) : OGroup Q) =
      piOrth Q * zbar * wbar := by
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      h.map_central hL ht ht2 htL, hw'φ]
  have hu'_ne : φ ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ * w') ≠ 1 := by
    intro h1
    have hprod1 : piOrth Q * zbar * wbar = 1 := by
      rw [← hu'_val, h1]
      rfl
    rw [hprod1, invType_one] at hpi_t
    exact absurd hpi_t (by decide)
  have huL : t * z * (w' : G) ∈ L := ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ * w').2
  have hu_val : (⟨t * z * (w' : G), huL⟩ : ↥L) =
      (⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ * w' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
  have hu2 : orderOf (t * z * (w' : G)) = 2 := by
    have h1 : orderOf (⟨t * z * (w' : G), huL⟩ : ↥L) = 2 := by
      rw [hu_val]
      refine orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hu'sq) ?_
      intro heq
      exact hu'_ne (by rw [heq, map_one])
    rwa [Subgroup.orderOf_mk] at h1
  have huI : IsI4PlusIn L (t * z * (w' : G)) := by
    refine (t5_isI4PlusIn_iff hL h huL hu2).mpr ?_
    rw [hu_val]
    exact (t5_isI4PlusIn_omega_iff hdim hsgn
      (by rw [hu'_val]; exact hpi_sq) hu'_ne).mpr (by rw [hu'_val]; exact hpi_t)
  exact ⟨(w' : G), hwI, hwz, huI⟩

end CFSG.OddStandard.SmallF3.Omega
