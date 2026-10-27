module

public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourAction
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem abelianAutomorphismUnits_surjective (A : Type*) [CommGroup A] :
    Function.Surjective (abelianAutomorphismUnits A) := by
  intro u
  let automorphism : MulAut A := {
    toFun x := (u.val (Additive.ofMul x)).toMul
    invFun x := (u.inv (Additive.ofMul x)).toMul
    left_inv x := by
      have h := congrArg (fun f : AddMonoid.End (Additive A) => f (Additive.ofMul x)) u.inv_val
      exact congrArg Additive.toMul h
    right_inv x := by
      have h := congrArg (fun f : AddMonoid.End (Additive A) => f (Additive.ofMul x)) u.val_inv
      exact congrArg Additive.toMul h
    map_mul' x y := congrArg Additive.toMul (map_add u.val (Additive.ofMul x) (Additive.ofMul y)) }
  refine ⟨automorphism, ?_⟩
  apply Units.ext
  apply AddMonoid.End.ext
  intro x
  rfl

@[expose] noncomputable def smallCfourAutomorphismEquiv {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) : MulAut A ≃* (ResidualRing 1)ˣ := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  exact (MulEquiv.ofBijective (abelianAutomorphismUnits A)
    ⟨abelianAutomorphismUnits_injective A, abelianAutomorphismUnits_surjective A⟩).trans
    ((Units.mapEquiv (addEndCoordinateTransport coordinates).toMulEquiv).trans
      (Units.mapEquiv smallCfourEndRingEquiv.toMulEquiv))

@[expose] def smallCfourMatrixApply (m : ResidualRing 1) (x : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (m.1.1 * x.1 + m.1.2 * x.2, m.2.1 * x.1 + m.2.2 * x.2)

theorem smallCfourAutomorphismEquiv_apply {A : Type*} [Group A] (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) (automorphism : MulAut A) (x : A) :
    coordinates (Additive.ofMul (automorphism x)) =
      smallCfourMatrixApply (smallCfourAutomorphismEquiv hcommutative coordinates automorphism).val
        (coordinates (Additive.ofMul x)) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let f := addEndCoordinateTransport coordinates (abelianAutomorphismUnits A automorphism).val
  have heq : (smallCfourAutomorphismEquiv hcommutative coordinates automorphism).val =
      cyclicPairEndCoefficients 1 4 f := smallCfourEndRingEquiv_coefficients f
  rw [heq]
  have happly := cyclicPairEnd_apply 1 4 f (coordinates (Additive.ofMul x))
  have hinclusion : ∀ z : ZMod 4, scaledCyclicInclusion 1 4 z = z := by
    intro z
    rw [scaledCyclicInclusion_apply]
    change (1 : ZMod 4) * (z.val : ZMod 4) = z
    rw [one_mul, ZMod.natCast_zmod_val]
  have hreduction : ∀ z : ZMod 4, cyclicReduction 1 4 z = z := by
    intro z
    change ZMod.castHom (by decide : 4 ∣ 4) (ZMod 4) z = z
    rw [ZMod.castHom_self]
    rfl
  simp only [hinclusion, hreduction] at happly
  change f (coordinates (Additive.ofMul x)) = _ at happly
  have hleft : f (coordinates (Additive.ofMul x)) = coordinates (Additive.ofMul (automorphism x)) := by
    change coordinates ((abelianAutomorphismUnits A automorphism).val
      (coordinates.symm (coordinates (Additive.ofMul x)))) = _
    rw [coordinates.symm_apply_apply]
    rfl
  exact hleft.symm.trans happly

@[expose] def smallCfourBinaryVector (x : ZMod 4 × ZMod 4) : ZMod 2 × ZMod 2 :=
  let reduction := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  (reduction x.1, reduction x.2)

@[expose] def smallCfourBinaryApply (f : RankTwoBinaryResidue 1) (x : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (f.1.1 * x.1 + f.1.2 * x.2, f.2.1 * x.1 + f.2.2 * x.2)

@[expose] def smallCfourBinaryDeterminant (f : RankTwoBinaryResidue 1) : ZMod 2 :=
  f.1.1 * f.2.2 - f.1.2 * f.2.1

theorem smallCfourBinary_isUnit_iff (f : RankTwoBinaryResidue 1) :
    IsUnit f ↔ smallCfourBinaryDeterminant f = 1 := by
  rw [isUnit_iff_exists]
  have h : ∀ f : RankTwoBinaryResidue 1,
      (∃ g, f * g = 1 ∧ g * f = 1) ↔ smallCfourBinaryDeterminant f = 1 := by decide +kernel
  exact h f

theorem smallCfour_even_norm_coordinates :
    ∀ f : RankTwoBinaryResidue 1, smallCfourBinaryDeterminant (1 + f) = 1 →
      (∀ x : ZMod 4 × ZMod 4, smallCfourMatrixApply (smallCfourEvenMatrix f) x + x = 0 ↔ 2 • x = 0) ∧
      (∀ x : ZMod 4 × ZMod 4, ∃ y : ZMod 4 × ZMod 4,
        smallCfourMatrixApply (smallCfourEvenMatrix f) y + y = 2 • x) := by
  decide +kernel

theorem smallCfour_even_fixed_coordinates :
    ∀ (f : RankTwoBinaryResidue 1) (x : ZMod 4 × ZMod 4),
      smallCfourMatrixApply (smallCfourEvenMatrix f) x = x ↔
        smallCfourBinaryApply f (smallCfourBinaryVector x) = 0 := by
  decide +kernel

theorem smallCfour_binary_vector_zero :
    ∀ x : ZMod 4 × ZMod 4, smallCfourBinaryVector x = 0 ↔ ∃ y : ZMod 4 × ZMod 4, x = 2 • y := by
  decide +kernel

theorem smallCfour_binary_killed_not_unit :
    ∀ (f : RankTwoBinaryResidue 1) (x : ZMod 2 × ZMod 2),
      x ≠ 0 → smallCfourBinaryApply f x = 0 → smallCfourBinaryDeterminant f ≠ 1 := by
  decide +kernel

theorem small_cfour_central_action_lift_square {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4))
    (f : RankTwoBinaryResidue 1) (hnonzero : f ≠ 0)
    (hnorm : smallCfourBinaryDeterminant (1 + f) = 1)
    (hcentral : ∀ s : S,
      Commute (smallCfourEvenUnit f)
        (smallCfourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)))
    (t : S)
    (hlift : smallCfourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) t) = smallCfourEvenUnit f) :
    ∃ square : A, (square : S) = t ^ 2 ∧
      (∀ a : A, square ≠ a ^ 2) ∧
      smallCfourBinaryVector (coordinates (Additive.ofMul square)) ≠ 0 ∧
      smallCfourBinaryApply f (smallCfourBinaryVector (coordinates (Additive.ofMul square))) = 0 ∧
      smallCfourBinaryDeterminant f = 0 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let equivalence := smallCfourAutomorphismEquiv hcommutative coordinates
  let automorphism := MulAut.conjNormal (H := A) t
  have hsquare : automorphism ^ 2 = 1 := by
    apply equivalence.injective
    rw [map_pow, map_one, hlift]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_two]
    change smallCfourEvenMatrix f * smallCfourEvenMatrix f = 1
    exact smallCfourEvenMatrix_square f
  have hnontrivial : automorphism ≠ 1 := by
    intro h
    have heq : smallCfourEvenUnit f = 1 := hlift.symm.trans (congrArg equivalence h |>.trans (map_one equivalence))
    have hzero : smallCfourEvenHom (Multiplicative.ofAdd f) = smallCfourEvenHom 1 := by
      rw [map_one]
      exact heq
    have hf := smallCfourEvenHom_injective hzero
    exact hnonzero (congrArg Multiplicative.toAdd hf)
  have hcentralNative (s : S) : Commute automorphism (MulAut.conjNormal (H := A) s) := by
    apply equivalence.injective
    rw [map_mul, map_mul]
    rw [hlift]
    exact (hcentral s).eq
  have hnormCoordinates (a : A) :
      coordinates (Additive.ofMul (automorphism a * a)) =
        smallCfourMatrixApply (smallCfourEvenMatrix f) (coordinates (Additive.ofMul a)) +
          coordinates (Additive.ofMul a) := by
    change coordinates (Additive.ofMul (automorphism a) + Additive.ofMul a) = _
    rw [map_add, smallCfourAutomorphismEquiv_apply hcommutative, hlift]
    rfl
  have hnormKernel (a : A) : automorphism a * a = 1 ↔ a ^ 2 = 1 := by
    have hleft : automorphism a * a = 1 ↔
        coordinates (Additive.ofMul (automorphism a * a)) = 0 := by
      exact (coordinates.injective.eq_iff' (map_zero coordinates)).symm
    have hright : a ^ 2 = 1 ↔ 2 • coordinates (Additive.ofMul a) = 0 := by
      have hpower : coordinates (Additive.ofMul (a ^ 2)) = 2 • coordinates (Additive.ofMul a) := by
        exact map_nsmul coordinates 2 (Additive.ofMul a)
      constructor
      · intro h
        rw [← hpower, h]
        exact map_zero coordinates
      · intro h
        apply coordinates.injective
        change coordinates (Additive.ofMul (a ^ 2)) = coordinates 0
        rw [hpower, h, map_zero]
    rw [hleft, hnormCoordinates, hright]
    exact (smallCfour_even_norm_coordinates f hnorm).1 _
  let pairCoordinates : A ≃* Multiplicative (ZMod (2 ^ 2)) × Multiplicative (ZMod (2 ^ 2)) := {
    toFun a := (Multiplicative.ofAdd (coordinates (Additive.ofMul a)).1,
      Multiplicative.ofAdd (coordinates (Additive.ofMul a)).2)
    invFun a := (coordinates.symm (a.1.toAdd, a.2.toAdd)).toMul
    left_inv a := congrArg Additive.toMul (coordinates.symm_apply_apply (Additive.ofMul a))
    right_inv a := congrArg (fun z : ZMod 4 × ZMod 4 => (Multiplicative.ofAdd z.1, Multiplicative.ofAdd z.2))
      (coordinates.apply_symm_apply (a.1.toAdd, a.2.toAdd))
    map_mul' a b := congrArg (fun z : ZMod 4 × ZMod 4 => (Multiplicative.ofAdd z.1, Multiplicative.ofAdd z.2))
      (map_add coordinates (Additive.ofMul a) (Additive.ofMul b)) }
  obtain ⟨hmem, hnotNorm⟩ := central_action_involution_norm_obstruction A hcommutative
    hselfCentralizing hnoEight automorphism hsquare hnontrivial hcentralNative hnormKernel
    (binary_rank_two_square_kernel_card A hcommutative (by decide) (by decide) pairCoordinates) t rfl
  let square : A := ⟨t ^ 2, hmem⟩
  have hprimitive (a : A) : square ≠ a ^ 2 := by
    intro h
    obtain ⟨y, hy⟩ := (smallCfour_even_norm_coordinates f hnorm).2 (coordinates (Additive.ofMul a))
    let b : A := (coordinates.symm y).toMul
    have hnormEq : automorphism b * b = a ^ 2 := by
      apply coordinates.injective
      change coordinates (Additive.ofMul (automorphism b * b)) = coordinates (Additive.ofMul (a ^ 2))
      rw [hnormCoordinates]
      change smallCfourMatrixApply (smallCfourEvenMatrix f) (coordinates (coordinates.symm y)) +
        coordinates (coordinates.symm y) = coordinates (Additive.ofMul (a ^ 2))
      rw [coordinates.apply_symm_apply, hy]
      exact (map_nsmul coordinates 2 (Additive.ofMul a)).symm
    apply hnotNorm b
    change (square : S) = _
    exact congrArg (fun a : A => a.val) (h.trans hnormEq.symm)
  have hnonzeroResidue : smallCfourBinaryVector (coordinates (Additive.ofMul square)) ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := (smallCfour_binary_vector_zero _).mp hz
    let a : A := (coordinates.symm y).toMul
    apply hprimitive a
    apply coordinates.injective
    change coordinates (Additive.ofMul square) = coordinates (2 • coordinates.symm y)
    rw [hy, map_nsmul, coordinates.apply_symm_apply]
  have hfixed : smallCfourMatrixApply (smallCfourEvenMatrix f) (coordinates (Additive.ofMul square)) =
      coordinates (Additive.ofMul square) := by
    have h := congrArg (fun a : A => coordinates (Additive.ofMul a))
      (lift_square_fixed_by_conjugation A t square rfl)
    rw [smallCfourAutomorphismEquiv_apply hcommutative, hlift] at h
    exact h
  have hkilled := (smallCfour_even_fixed_coordinates f _).mp hfixed
  have hsingular := smallCfour_binary_killed_not_unit f _ hnonzeroResidue hkilled
  have hbinary : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  exact ⟨square, rfl, hprimitive, hnonzeroResidue, hkilled, hbinary _ hsingular⟩

end CFSG.LargeEvenClassification.Helpers
