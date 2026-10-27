module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem cyclicFourInclusion_reduction (n : ℕ) (x : ZMod 4) :
    cyclicReduction (2 ^ (n + 2)) 4 (scaledCyclicInclusion (2 ^ (n + 2)) 4 x) = 0 := by
  rw [cyclicReduction_inclusion, cyclicFourScale_zero, zero_mul]

theorem cyclicFourInclusion_product (n : ℕ) (x y : ZMod 4) :
    scaledCyclicInclusion (2 ^ (n + 2)) 4 x * scaledCyclicInclusion (2 ^ (n + 2)) 4 y = 0 := by
  rw [← scaledCyclicInclusion_scalar, cyclicFourInclusion_reduction, zero_mul, map_zero]

@[expose] noncomputable def cyclicFourHalfDifference (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    AddMonoid.End (CyclicFourSpace n) :=
  cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4
    ((scaledCyclicInclusion (2 ^ (n + 2)) 4 (x.1.toAdd.val : ZMod 4), (x.2.1.toAdd.val : ZMod 4)),
      ((x.2.2.toAdd.val : ZMod 4), 0))

theorem cyclicFourHalfDifference_cube (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    cyclicFourHalfDifference n x ^ 3 = 0 := by
  apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
  rw [pow_succ (cyclicFourHalfDifference n x) 2, pow_two (cyclicFourHalfDifference n x),
    cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul,
    cyclicFourHalfDifference, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_zero]
  simp only [cyclicPairCoefficientProduct, cyclicFourInclusion_product,
    cyclicFourInclusion_reduction, cyclicFourScale_zero, mul_zero, zero_mul, add_zero, zero_add,
    map_zero]
  rfl

theorem cyclicFourElementaryHom_coefficients (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourElementaryHom n x).val =
      ((1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * (x.1.toAdd.val : ZMod 4)),
        2 * (x.2.1.toAdd.val : ZMod 4)), (2 * (x.2.2.toAdd.val : ZMod 4), 1)) := by
  have hcases : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide +kernel
  rw [cyclicFourElementaryHom_spec]
  rcases hcases x.1.toAdd with he | he <;>
    rcases hcases x.2.1.toAdd with hi | hi <;>
    rcases hcases x.2.2.toAdd with hj | hj <;>
    simp only [he, hi, hj, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one,
      mul_zero, mul_one, pow_zero, pow_one, one_mul, mul_one] <;>
    simp only [Units.val_mul, Units.val_one, cyclicPairEndCoefficients_mul,
      cyclicPairEndCoefficients_one, cyclicFourDelta_inclusion_coefficients,
      cyclicFourU_square_coefficients, cyclicFourV_square_coefficients,
      cyclicPairCoefficientProduct, map_one, map_zero, map_add,
      cyclicFourInclusion_reduction, cyclicFourScale_zero, mul_one, one_mul,
      mul_zero, zero_mul, add_zero, zero_add, show (2 * 2 : ZMod 4) = 0 by decide +kernel]

theorem cyclicFourElementaryHom_norm_factor (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    1 + (cyclicFourElementaryHom n x).val = 2 * (1 + cyclicFourHalfDifference n x) := by
  apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
  rw [two_mul]
  simp only [cyclicPairEndCoefficients_add, cyclicPairEndCoefficients_one,
    cyclicFourElementaryHom_coefficients, cyclicFourHalfDifference, cyclicPairEndCoefficients_from]
  change ((1, 0), (0, 1)) +
      ((1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * (x.1.toAdd.val : ZMod 4)),
        2 * (x.2.1.toAdd.val : ZMod 4)), (2 * (x.2.2.toAdd.val : ZMod 4), 1)) = _
  rw [two_mul, map_add]
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, zero_add, two_mul] <;> abel

theorem cyclicFourElementaryHom_norm (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    (∀ a : CyclicFourSpace n, (cyclicFourElementaryHom n x).val a + a = 0 ↔ 2 • a = 0) ∧
    (∀ a : CyclicFourSpace n, ∃ b : CyclicFourSpace n,
      (cyclicFourElementaryHom n x).val b + b = 2 • a) := by
  let f := 1 + cyclicFourHalfDifference n x
  have hf : IsUnit f := (show IsNilpotent (cyclicFourHalfDifference n x) from
    ⟨3, cyclicFourHalfDifference_cube n x⟩).isUnit_one_add
  have hnorm (a : CyclicFourSpace n) : (cyclicFourElementaryHom n x).val a + a = f (2 • a) := by
    have h := congrArg (fun r : AddMonoid.End (CyclicFourSpace n) => r a)
      (cyclicFourElementaryHom_norm_factor n x)
    change a + (cyclicFourElementaryHom n x).val a = 2 • f a at h
    rw [map_nsmul f]
    exact (add_comm _ _).trans h
  constructor
  · intro a
    rw [hnorm]
    exact hf.smul_eq_zero
  · intro a
    obtain ⟨b, hb⟩ := hf.smul_bijective.2 a
    refine ⟨b, ?_⟩
    rw [hnorm, map_nsmul]
    exact congrArg (fun y : CyclicFourSpace n => 2 • y) hb

@[expose] noncomputable def cyclicFourAutomorphismEquiv {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A) (n : ℕ)
    (coordinates : Additive A ≃+ CyclicFourSpace n) : MulAut A ≃* CyclicFourAut n := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  exact (MulEquiv.ofBijective (abelianAutomorphismUnits A)
    ⟨abelianAutomorphismUnits_injective A, abelianAutomorphismUnits_surjective A⟩).trans
    (Units.mapEquiv (addEndCoordinateTransport coordinates).toMulEquiv)

theorem cyclicFourAutomorphismEquiv_apply {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A) (n : ℕ)
    (coordinates : Additive A ≃+ CyclicFourSpace n) (α : MulAut A) (a : A) :
    coordinates (Additive.ofMul (α a)) =
      (cyclicFourAutomorphismEquiv hcommutative n coordinates α).val
        (coordinates (Additive.ofMul a)) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  change coordinates (Additive.ofMul (α a)) =
    coordinates ((abelianAutomorphismUnits A α).val
      (coordinates.symm (coordinates (Additive.ofMul a))))
  rw [coordinates.symm_apply_apply]
  rfl

@[expose] def cyclicFourBinaryCoordinates (n : ℕ) : CyclicFourSpace n →+ ZMod 2 × ZMod 2 where
  toFun x := ((ZMod.castHom (show 2 ∣ 2 ^ (n + 2) * 4 from
      (dvd_pow_self 2 (by omega)).trans (dvd_mul_right _ _)) (ZMod 2)) x.1,
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) x.2)
  map_zero' := Prod.ext (map_zero _) (map_zero _)
  map_add' x y := Prod.ext (map_add _ x.1 y.1) (map_add _ x.2 y.2)

theorem cyclicFourBinaryCoordinates_zero (n : ℕ) (x : CyclicFourSpace n) :
    cyclicFourBinaryCoordinates n x = 0 ↔ ∃ y : CyclicFourSpace n, 2 • y = x := by
  constructor
  · intro h
    have hlong := congrArg Prod.fst h
    have hshort := congrArg Prod.snd h
    have hl : 2 ∣ x.1.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have hh := ZMod.natCast_zmod_val x.1
      change (ZMod.castHom _ (ZMod 2)) x.1 = 0 at hlong
      rw [← hh, map_natCast] at hlong
      exact hlong
    have hs : 2 ∣ x.2.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have hh := ZMod.natCast_zmod_val x.2
      change (ZMod.castHom _ (ZMod 2)) x.2 = 0 at hshort
      rw [← hh, map_natCast] at hshort
      exact hshort
    refine ⟨((x.1.val / 2 : ℕ), (x.2.val / 2 : ℕ)), ?_⟩
    apply Prod.ext
    · change 2 • ((x.1.val / 2 : ℕ) : ZMod (2 ^ (n + 2) * 4)) = x.1
      rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hl, ZMod.natCast_zmod_val]
    · change 2 • ((x.2.val / 2 : ℕ) : ZMod 4) = x.2
      rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hs, ZMod.natCast_zmod_val]
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    have h : ∀ z : ZMod 2 × ZMod 2, 2 • z = 0 := by decide +kernel
    exact h _

theorem cyclicFourElementaryHom_fixed_mixed (n : ℕ) (e : ZMod 2) (a : CyclicFourSpace n)
    (hfixed : (cyclicFourElementaryHom n (Multiplicative.ofAdd e,
      (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1))).val a = a) :
    cyclicFourBinaryCoordinates n a = 0 := by
  let x := (Multiplicative.ofAdd e, (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)))
  have hcoeff := cyclicFourElementaryHom_coefficients n x
  have ha := cyclicPairEnd_apply (2 ^ (n + 2)) 4 (cyclicFourElementaryHom n x).val a
  rw [hcoeff] at ha
  dsimp only [x] at ha
  simp only [one_mul] at ha
  change (cyclicFourElementaryHom n x).val a =
    ((1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * (e.val : ZMod 4))) * a.1 +
    scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * a.2),
    2 * cyclicReduction (2 ^ (n + 2)) 4 a.1 + a.2) at ha
  have hs : 2 * cyclicReduction (2 ^ (n + 2)) 4 a.1 = 0 := by
    have hh := congrArg Prod.snd (ha.symm.trans hfixed)
    change 2 * cyclicReduction (2 ^ (n + 2)) 4 a.1 + a.2 = a.2 at hh
    linear_combination hh
  have hlongEven : ∃ y : ZMod (2 ^ (n + 2) * 4), 2 • y = a.1 := by
    have hc : ((2 * a.1.val : ℕ) : ZMod 4) = 0 := by
      have hh := ZMod.natCast_zmod_val a.1
      rw [← hh, map_natCast] at hs
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
    have hd : 4 ∣ 2 * a.1.val := (ZMod.natCast_eq_zero_iff _ _).mp hc
    have he : 2 ∣ a.1.val := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd
    refine ⟨(a.1.val / 2 : ℕ), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' he, ZMod.natCast_zmod_val]
  have hzero : scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * a.2) = 0 := by
    have hh := congrArg Prod.fst (ha.symm.trans hfixed)
    change (1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * (e.val : ZMod 4))) * a.1 +
      scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * a.2) = a.1 at hh
    have hscalar : scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * (e.val : ZMod 4)) * a.1 = 0 := by
      rw [mul_comm (scaledCyclicInclusion (2 ^ (n + 2)) 4 (2 * (e.val : ZMod 4))) a.1,
        ← scaledCyclicInclusion_scalar]
      rw [show cyclicReduction (2 ^ (n + 2)) 4 a.1 * (2 * (e.val : ZMod 4)) = 0 from by
        rw [← mul_assoc, mul_comm (cyclicReduction (2 ^ (n + 2)) 4 a.1) 2, hs, zero_mul], map_zero]
    rw [add_mul, one_mul, hscalar, add_zero] at hh
    exact add_left_cancel (hh.trans (add_zero a.1).symm)
  have hshortEven : ∃ y : ZMod 4, 2 • y = a.2 := by
    have hshort : 2 * a.2 = 0 := by
      apply scaledCyclicInclusion_injective (2 ^ (n + 2)) 4 (by positivity)
      rw [map_zero]
      exact hzero
    have h : ∀ z : ZMod 4, 2 * z = 0 → ∃ y : ZMod 4, 2 • y = z := by decide +kernel
    exact h a.2 hshort
  obtain ⟨y, hy⟩ := hlongEven
  obtain ⟨z, hz⟩ := hshortEven
  exact (cyclicFourBinaryCoordinates_zero n a).mpr ⟨(y, z), Prod.ext hy hz⟩

theorem cyclicFourE_norm (n : ℕ) (g : CyclicFourAut n) (hg : g ∈ cyclicFourE n) :
    (∀ a : CyclicFourSpace n, g.val a + a = 0 ↔ 2 • a = 0) ∧
    (∀ a : CyclicFourSpace n, ∃ b : CyclicFourSpace n, g.val b + b = 2 • a) := by
  obtain ⟨x, rfl⟩ := hg
  exact cyclicFourElementaryHom_norm n x

theorem cyclicFour_central_action_primitive_square {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicFourSpace n)
    (g : CyclicFourAut n) (hg : g ∈ cyclicFourE n) (hgne : g ≠ 1)
    (hcentral : ∀ s : S, Commute g
      (cyclicFourAutomorphismEquiv hcommutative n coordinates (MulAut.conjNormal (H := A) s)))
    (t : S) (ht : cyclicFourAutomorphismEquiv hcommutative n coordinates
      (MulAut.conjNormal (H := A) t) = g) :
    ∃ a : A, (a : S) = t ^ 2 ∧ (∀ b : A, a ≠ b ^ 2) ∧
      g.val (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := cyclicFourAutomorphismEquiv hcommutative n coordinates
  let δ := MulAut.conjNormal (H := A) t
  have hsquare : δ ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, ht]
    exact (cyclicFourE_elementary n).2 g hg
  have hne : δ ≠ 1 := by
    intro h
    exact hgne (ht.symm.trans (congrArg e h |>.trans (map_one e)))
  have hcentralNative (s : S) : Commute δ (MulAut.conjNormal (H := A) s) := by
    apply e.injective
    rw [map_mul, map_mul, ht]
    exact (hcentral s).eq
  have hnormCoordinates (a : A) :
      coordinates (Additive.ofMul (δ a * a)) =
        g.val (coordinates (Additive.ofMul a)) + coordinates (Additive.ofMul a) := by
    change coordinates (Additive.ofMul (δ a) + Additive.ofMul a) = _
    rw [map_add, cyclicFourAutomorphismEquiv_apply hcommutative, ht]
  have hkernel (a : A) : δ a * a = 1 ↔ a ^ 2 = 1 := by
    have hleft : δ a * a = 1 ↔ coordinates (Additive.ofMul (δ a * a)) = 0 := by
      constructor
      · rintro h
        rw [h]
        exact map_zero coordinates
      · intro h
        apply Additive.ofMul.injective
        apply coordinates.injective
        rw [h]
        exact (map_zero coordinates).symm
    have hright : a ^ 2 = 1 ↔ 2 • coordinates (Additive.ofMul a) = 0 := by
      constructor
      · intro h
        rw [← map_zero coordinates]
        rw [← map_nsmul]
        exact congrArg coordinates (congrArg Additive.ofMul h)
      · intro h
        apply Additive.ofMul.injective
        apply coordinates.injective
        change coordinates (2 • Additive.ofMul a) = coordinates 0
        rw [map_nsmul, h, map_zero]
    rw [hleft, hright, hnormCoordinates]
    exact (cyclicFourE_norm n g hg).1 _
  let pairs : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4) :=
    (AddEquiv.toMultiplicativeRight coordinates).trans
      ((MulEquiv.prodMultiplicative (ZMod (2 ^ (n + 2) * 4)) (ZMod 4)).trans
        (MulEquiv.prodCongr (AddEquiv.toMultiplicative
          (ZMod.ringEquivCongr (show 2 ^ (n + 2) * 4 = 2 ^ (n + 4) by
            rw [show n + 4 = (n + 2) + 2 by omega, pow_add 2 (n + 2) 2]; norm_num)).toAddEquiv)
          (MulEquiv.refl _)))
  have hcard := binary_rank_two_square_kernel_card A hcommutative (by omega : 0 < n + 4)
    (by decide : 0 < 2) pairs
  obtain ⟨hmem, hnotNorm⟩ := central_action_involution_norm_obstruction A hcommutative
    hselfCentralizing hnoEight δ hsquare hne hcentralNative hkernel hcard t rfl
  let a : A := ⟨t ^ 2, hmem⟩
  have hprimitive (b : A) : a ≠ b ^ 2 := by
    intro h
    obtain ⟨y, hy⟩ := (cyclicFourE_norm n g hg).2 (coordinates (Additive.ofMul b))
    let c := (coordinates.symm y).toMul
    have hnorm : δ c * c = b ^ 2 := by
      apply Additive.ofMul.injective
      apply coordinates.injective
      rw [hnormCoordinates]
      dsimp only [c]
      change g.val (coordinates (coordinates.symm y)) + coordinates (coordinates.symm y) = _
      rw [coordinates.apply_symm_apply, hy]
      change 2 • coordinates (Additive.ofMul b) = coordinates (2 • Additive.ofMul b)
      exact (map_nsmul coordinates 2 _).symm
    apply hnotNorm c
    exact (congrArg Subtype.val h).trans (congrArg Subtype.val hnorm).symm
  have hfixed : g.val (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
    rw [← ht, ← cyclicFourAutomorphismEquiv_apply hcommutative]
    exact congrArg (fun b : A => coordinates (Additive.ofMul b)) (lift_square_fixed_by_conjugation A t a rfl)
  exact ⟨a, rfl, hprimitive, hfixed⟩

theorem cyclicFour_mixed_action_excluded {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicFourSpace n)
    (e : ZMod 2)
    (hcentral : ∀ s : S, Commute (cyclicFourElementaryHom n
      (Multiplicative.ofAdd e, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)))
      (cyclicFourAutomorphismEquiv hcommutative n coordinates (MulAut.conjNormal (H := A) s))) :
    cyclicFourElementaryHom n (Multiplicative.ofAdd e, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) ∉
      ((cyclicFourAutomorphismEquiv hcommutative n coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := A))).range := by
  intro hmem
  obtain ⟨t, ht⟩ := hmem
  let x := (Multiplicative.ofAdd e, (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)))
  have hne : cyclicFourElementaryHom n x ≠ 1 := by
    intro h
    have hx := cyclicFourElementaryHom_injective n (h.trans (map_one (cyclicFourElementaryHom n)).symm)
    have hi := congrArg (fun x => x.2.1.toAdd) hx
    change (1 : ZMod 2) = 0 at hi
    exact one_ne_zero hi
  obtain ⟨a, _, hprimitive, hfixed⟩ := cyclicFour_central_action_primitive_square A hcommutative
    hselfCentralizing hnoEight n coordinates _ ⟨x, rfl⟩ hne hcentral t ht
  have hzero := cyclicFourElementaryHom_fixed_mixed n e (coordinates (Additive.ofMul a)) hfixed
  obtain ⟨y, hy⟩ := (cyclicFourBinaryCoordinates_zero n _).mp hzero
  apply hprimitive (coordinates.symm y).toMul
  apply Additive.ofMul.injective
  apply coordinates.injective
  change coordinates (Additive.ofMul a) = coordinates (2 • coordinates.symm y)
  rw [map_nsmul, coordinates.apply_symm_apply, hy]

end CFSG.LargeEvenClassification.Helpers
