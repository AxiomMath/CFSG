module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoBinaryEndResidue

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def principalCongruenceSubgroup (R : Type*) [Ring R] (n : ℕ) : Subgroup Rˣ :=
  (Units.map (Ideal.Quotient.mk (ringMultipleIdeal R n)).toMonoidHom).ker

theorem principalCongruenceSubgroup_mem {R : Type*} [Ring R] (n : ℕ) (u : Rˣ) :
    u ∈ principalCongruenceSubgroup R n ↔ ∃ r : R, (u : R) = 1 + n • r := by
  change Units.map (Ideal.Quotient.mk (ringMultipleIdeal R n)).toMonoidHom u = 1 ↔ _
  constructor
  · intro h
    have hval := congrArg Units.val h
    have hz : Ideal.Quotient.mk (ringMultipleIdeal R n) ((u : R) - 1) = 0 := by
      rw [map_sub, map_one]
      exact sub_eq_zero.mpr hval
    obtain ⟨r, hr⟩ := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact ⟨r, (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)⟩
  · rintro ⟨r, hr⟩
    apply Units.ext
    change Ideal.Quotient.mk (ringMultipleIdeal R n) u = 1
    have hz : Ideal.Quotient.mk (ringMultipleIdeal R n) (n • r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ⟨r, rfl⟩
    rw [hr, map_add, map_one, hz, add_zero]

instance principalCongruenceSubgroup_normal (R : Type*) [Ring R] (n : ℕ) :
    (principalCongruenceSubgroup R n).Normal := inferInstanceAs (MonoidHom.ker _).Normal

theorem principalCongruenceSubgroup_four (R : Type*) [Ring R] :
    principalCongruenceSubgroup R 4 = principalFourSubgroup R := by
  ext u
  rw [principalCongruenceSubgroup_mem]
  change (∃ r : R, (u : R) = 1 + 4 • r) ↔ ∃ r : R, (u : R) = 1 + 4 * r
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

section Leading

variable {R F : Type*} [Ring R] [Ring F] [Module (ZMod 2) F]
variable (residue : R →+* F)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (n : ℕ) (heven : 2 ∣ n)
variable (hcancel : ∀ r : R, n • r = 0 → residue r = 0)

@[expose] noncomputable def principalLeadingRepresentative
    (u : principalCongruenceSubgroup R n) : R :=
  Classical.choose ((principalCongruenceSubgroup_mem n u.val).mp u.property)

theorem principalLeadingRepresentative_spec (u : principalCongruenceSubgroup R n) :
    (u.val : R) = 1 + n • principalLeadingRepresentative n u :=
  Classical.choose_spec ((principalCongruenceSubgroup_mem n u.val).mp u.property)

@[expose] noncomputable def principalLeadingResidue
    (u : principalCongruenceSubgroup R n) : F :=
  residue (principalLeadingRepresentative n u)

omit [Module (ZMod 2) F] in
include hcancel in
theorem principalLeadingResidue_spec (u : principalCongruenceSubgroup R n)
    (r : R) (hr : (u.val : R) = 1 + n • r) : principalLeadingResidue residue n u = residue r := by
  have heq : n • principalLeadingRepresentative n u = n • r :=
    add_left_cancel ((principalLeadingRepresentative_spec n u).symm.trans hr)
  have hz : n • (principalLeadingRepresentative n u - r) = 0 := by
    rw [nsmul_sub, heq, sub_self]
  exact sub_eq_zero.mp (by
    change residue (principalLeadingRepresentative n u) - residue r = 0
    rw [← map_sub]
    exact hcancel _ hz)

omit [Module (ZMod 2) F] in
include hkernel heven in
theorem residue_nat_even : residue (n : R) = 0 := by
  obtain ⟨m, hm⟩ := heven
  apply (hkernel _).mpr
  refine ⟨(m : R), ?_⟩
  rw [hm, Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat]

@[expose] noncomputable def principalLeadingResidueHom :
    principalCongruenceSubgroup R n →* Multiplicative F where
  toFun u := Multiplicative.ofAdd (principalLeadingResidue residue n u)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change principalLeadingResidue residue n 1 = 0
    rw [principalLeadingResidue_spec residue n hcancel 1 0 (by simp), map_zero]
  map_mul' := by
    intro u v
    apply Multiplicative.toAdd.injective
    change principalLeadingResidue residue n (u * v) =
      principalLeadingResidue residue n u + principalLeadingResidue residue n v
    let r := principalLeadingRepresentative n u
    let s := principalLeadingRepresentative n v
    have hproduct : ((u * v).val : R) = 1 + n • (r + s + r * (n • s)) := by
      change (u.val : R) * v.val = _
      rw [principalLeadingRepresentative_spec, principalLeadingRepresentative_spec]
      change (1 + n • r) * (1 + n • s) = _
      simp only [nsmul_eq_mul]
      noncomm_ring
    rw [principalLeadingResidue_spec residue n hcancel (u * v) _ hproduct]
    simp only [map_add, map_mul, nsmul_eq_mul, residue_nat_even residue hkernel n heven,
      zero_mul, mul_zero, add_zero]
    rfl

omit [Module (ZMod 2) F] in
include hkernel hcancel in
theorem principalLeadingResidueHom_kernel (u : principalCongruenceSubgroup R n) :
    principalLeadingResidueHom residue hkernel n heven hcancel u = 1 ↔
      u.val ∈ principalCongruenceSubgroup R (n * 2) := by
  rw [principalCongruenceSubgroup_mem]
  change principalLeadingResidue residue n u = 0 ↔ _
  constructor
  · intro hz
    obtain ⟨r, hr⟩ := (hkernel _).mp hz
    refine ⟨r, ?_⟩
    rw [principalLeadingRepresentative_spec, hr, mul_nsmul']
  · rintro ⟨r, hr⟩
    have hr' : (u.val : R) = 1 + n • (2 • r) := by
      simpa only [mul_nsmul'] using hr
    rw [principalLeadingResidue_spec residue n hcancel u _ hr']
    exact (hkernel _).mpr ⟨r, rfl⟩

end Leading

section SquaresAndCommutators

variable {R F : Type*} [Ring R] [Ring F]
variable (residue : R →+* F)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)

include hkernel in
theorem residue_principal_two (u : Rˣ) (hu : u ∈ principalCongruenceSubgroup R 2) :
    residue (u : R) = 1 := by
  obtain ⟨r, hr⟩ := (principalCongruenceSubgroup_mem 2 u).mp hu
  have hz : residue (2 • r) = 0 := (hkernel _).mpr ⟨r, rfl⟩
  rw [hr, map_add, map_one, hz, add_zero]

theorem principal_two_square_mem_four (u : Rˣ) (hu : u ∈ principalCongruenceSubgroup R 2) :
    u ^ 2 ∈ principalCongruenceSubgroup R 4 := by
  obtain ⟨r, hr⟩ := (principalCongruenceSubgroup_mem 2 u).mp hu
  apply (principalCongruenceSubgroup_mem 4 _).mpr
  refine ⟨r + r * r, ?_⟩
  change (u : R) ^ 2 = _
  rw [hr]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

theorem principal_two_commutator_mem_four (u v : Rˣ)
    (hu : u ∈ principalCongruenceSubgroup R 2) (hv : v ∈ principalCongruenceSubgroup R 2) :
    u * v * u⁻¹ * v⁻¹ ∈ principalCongruenceSubgroup R 4 := by
  obtain ⟨r, hr⟩ := (principalCongruenceSubgroup_mem 2 u).mp hu
  obtain ⟨s, hs⟩ := (principalCongruenceSubgroup_mem 2 v).mp hv
  apply (principalCongruenceSubgroup_mem 4 _).mpr
  refine ⟨(r * s - s * r) * (u⁻¹ : Rˣ).val * (v⁻¹ : Rˣ).val, ?_⟩
  change (u : R) * v * (u⁻¹ : Rˣ).val * (v⁻¹ : Rˣ).val = _
  have hidentity : (u : R) * v * (u⁻¹ : Rˣ).val * (v⁻¹ : Rˣ).val =
      1 + ((u : R) * v - (v : R) * u) * (u⁻¹ : Rˣ).val * (v⁻¹ : Rˣ).val := by
    rw [sub_mul, sub_mul]
    have hcancel : (v : R) * u * (u⁻¹ : Rˣ).val * (v⁻¹ : Rˣ).val = 1 := by
      rw [mul_assoc (v : R) (u : R), Units.mul_inv, mul_one, Units.mul_inv]
    rw [hcancel]
    abel
  rw [hidentity, hr, hs]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)
variable (hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0)

include hcancelFour in
theorem principal_two_square_leading (u : principalCongruenceSubgroup R 2) :
    principalLeadingResidue residue 4
        ⟨u.val ^ 2, principal_two_square_mem_four u.val u.property⟩ =
      principalLeadingResidue residue 2 u +
        principalLeadingResidue residue 2 u * principalLeadingResidue residue 2 u := by
  let r := principalLeadingRepresentative 2 u
  have hr : ((u.val ^ 2 : Rˣ) : R) = 1 + 4 • (r + r * r) := by
    change (u.val : R) ^ 2 = _
    rw [principalLeadingRepresentative_spec]
    change (1 + 2 • r) ^ 2 = _
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  rw [principalLeadingResidue_spec residue 4 hcancelFour _ _ hr]
  change residue (r + r * r) = residue r + residue r * residue r
  rw [map_add, map_mul]

include hkernel hcancelFour in
theorem principal_two_commutator_leading (u v : principalCongruenceSubgroup R 2) :
    principalLeadingResidue residue 4
        ⟨u.val * v.val * u.val⁻¹ * v.val⁻¹,
          principal_two_commutator_mem_four u.val v.val u.property v.property⟩ =
      principalLeadingResidue residue 2 u * principalLeadingResidue residue 2 v -
        principalLeadingResidue residue 2 v * principalLeadingResidue residue 2 u := by
  let r := principalLeadingRepresentative 2 u
  let s := principalLeadingRepresentative 2 v
  have hidentity : (u.val : R) * v.val * (u.val⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val =
      1 + ((u.val : R) * v.val - (v.val : R) * u.val) *
        (u.val⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val := by
    rw [sub_mul, sub_mul]
    have hcancel : (v.val : R) * u.val * (u.val⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val = 1 := by
      rw [mul_assoc (v.val : R) (u.val : R), Units.mul_inv, mul_one, Units.mul_inv]
    rw [hcancel]
    abel
  have hr : ((u.val * v.val * u.val⁻¹ * v.val⁻¹ : Rˣ) : R) =
      1 + 4 • ((r * s - s * r) * (u.val⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val) := by
    change (u.val : R) * v.val * (u.val⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val = _
    rw [hidentity, principalLeadingRepresentative_spec, principalLeadingRepresentative_spec]
    change 1 + ((1 + 2 • r) * (1 + 2 • s) - (1 + 2 • s) * (1 + 2 • r)) * _ * _ = _
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  rw [principalLeadingResidue_spec residue 4 hcancelFour _ _ hr]
  rw [map_mul, map_mul, map_sub, map_mul, map_mul,
    residue_principal_two residue hkernel u.val⁻¹ ((principalCongruenceSubgroup R 2).inv_mem u.property),
    residue_principal_two residue hkernel v.val⁻¹ ((principalCongruenceSubgroup R 2).inv_mem v.property),
    mul_one, mul_one]
  rfl

end SquaresAndCommutators

theorem zmod_multiple_zero_binary {modulus n : ℕ} [NeZero modulus]
    (hn : 0 < n) (hdivides : n * 2 ∣ modulus) (x : ZMod modulus) (hz : n • x = 0) :
    ∃ r : ZMod modulus, x = 2 • r := by
  have hcast : ((n * x.val : ℕ) : ZMod modulus) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    simpa only [nsmul_eq_mul] using hz
  have hperiod : modulus ∣ n * x.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have heven : 2 ∣ x.val := Nat.dvd_of_mul_dvd_mul_left hn (hdivides.trans hperiod)
  refine ⟨(x.val / 2 : ℕ), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' heven, ZMod.natCast_zmod_val]

theorem cyclicPairEndBinaryResidueHom_cancel (scale modulus : ℕ) [NeZero scale] [NeZero modulus]
    [NeZero (scale * modulus)] (htwo : 2 ∣ modulus) (n : ℕ) (hn : 0 < n)
    (hdivides : n * 2 ∣ modulus) (f : AddMonoid.End (CyclicPair scale modulus))
    (hz : n • f = 0) : cyclicPairEndBinaryResidueHom scale modulus htwo f = 0 := by
  apply (cyclicPairEndBinaryResidueHom_zero scale modulus htwo f).mpr
  let c := cyclicPairEndCoefficients scale modulus f
  have hc : n • c = 0 := by
    have h := congrArg (cyclicPairEndCoefficients scale modulus) hz
    simpa only [cyclicPairEndCoefficients_nsmul, cyclicPairEndCoefficients_zero] using h
  obtain ⟨a, ha⟩ := zmod_multiple_zero_binary hn
    (hdivides.trans (dvd_mul_left modulus scale)) c.1.1 (congrArg (fun z => z.1.1) hc)
  obtain ⟨b, hb⟩ := zmod_multiple_zero_binary hn hdivides c.1.2 (congrArg (fun z => z.1.2) hc)
  obtain ⟨d, hd⟩ := zmod_multiple_zero_binary hn hdivides c.2.1 (congrArg (fun z => z.2.1) hc)
  obtain ⟨e, he⟩ := zmod_multiple_zero_binary hn hdivides c.2.2 (congrArg (fun z => z.2.2) hc)
  refine ⟨cyclicPairEndFromCoefficients scale modulus ((a, b), (d, e)), ?_⟩
  apply cyclicPairEndCoefficients_injective scale modulus
  rw [cyclicPairEndCoefficients_nsmul, cyclicPairEndCoefficients_from]
  change c = 2 • ((a, b), (d, e))
  apply Prod.ext <;> apply Prod.ext
  · exact ha
  · exact hb
  · exact hd
  · exact he

end CFSG.LargeEvenClassification.Helpers
