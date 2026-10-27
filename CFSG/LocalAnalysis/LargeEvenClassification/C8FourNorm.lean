module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourDelta : C8FourCode := ⟨64⟩
@[expose] def c8FourNu : C8FourCode := ⟨4⟩

theorem c8FourDelta_central (g : C8FourCode) : Commute c8FourDelta g := by
  have h : ∀ g : C8FourCode, c8FourDelta * g = g * c8FourDelta := by decide +kernel
  exact h g

theorem c8FourDelta_square : c8FourDelta ^ 2 = 1 := by decide +kernel
theorem c8FourDelta_ne_one : c8FourDelta ≠ 1 := by decide +kernel
theorem c8FourNu_square : c8FourNu ^ 2 = 1 := by decide +kernel
theorem c8FourNu_ne_one : c8FourNu ≠ 1 := by decide +kernel
theorem c8FourDeltaNu_square : (c8FourDelta * c8FourNu) ^ 2 = 1 := by decide +kernel
theorem c8FourDeltaNu_ne_one : c8FourDelta * c8FourNu ≠ 1 := by decide +kernel

@[expose] def c8FourNormKernel (g : C8FourCode) : Prop :=
  ∀ x : CyclicPair 2 4, c8FourApply g x + x = 0 ↔ 2 • x = 0

@[expose] def c8FourNormDoubles (g : C8FourCode) : Prop :=
  ∀ x : CyclicPair 2 4, ∃ y : CyclicPair 2 4, c8FourApply g y + y = 2 • x

instance c8FourNormKernel_decidable (g : C8FourCode) : Decidable (c8FourNormKernel g) :=
  inferInstanceAs (Decidable (∀ x : CyclicPair 2 4, c8FourApply g x + x = 0 ↔ 2 • x = 0))

instance c8FourNormDoubles_decidable (g : C8FourCode) : Decidable (c8FourNormDoubles g) :=
  inferInstanceAs (Decidable (∀ x : CyclicPair 2 4, ∃ y : CyclicPair 2 4, c8FourApply g y + y = 2 • x))

theorem c8Four_scalar_shear_norms :
    c8FourNormKernel c8FourDelta ∧ c8FourNormDoubles c8FourDelta ∧
    c8FourNormKernel c8FourNu ∧ c8FourNormDoubles c8FourNu ∧
    c8FourNormKernel (c8FourDelta * c8FourNu) ∧ c8FourNormDoubles (c8FourDelta * c8FourNu) := by
  decide +kernel

@[expose] noncomputable def c8FourAutomorphismEquiv {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A) (coordinates : Additive A ≃+ CyclicPair 2 4) :
    MulAut A ≃* C8FourCode := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  exact ((MulEquiv.ofBijective (abelianAutomorphismUnits A)
    ⟨abelianAutomorphismUnits_injective A, abelianAutomorphismUnits_surjective A⟩).trans
    (Units.mapEquiv (addEndCoordinateTransport coordinates).toMulEquiv)).trans c8FourNativeEquiv.symm

theorem c8FourAutomorphismEquiv_apply {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A) (coordinates : Additive A ≃+ CyclicPair 2 4)
    (α : MulAut A) (a : A) :
    coordinates (Additive.ofMul (α a)) =
      c8FourApply (c8FourAutomorphismEquiv hcommutative coordinates α) (coordinates (Additive.ofMul a)) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  have hnative : c8FourNativeUnit (c8FourAutomorphismEquiv hcommutative coordinates α) =
      (Units.mapEquiv (addEndCoordinateTransport coordinates).toMulEquiv) (abelianAutomorphismUnits A α) :=
    c8FourNativeEquiv.apply_symm_apply _
  rw [← c8FourNativeUnit_apply, hnative]
  change coordinates (Additive.ofMul (α a)) =
    coordinates ((abelianAutomorphismUnits A α).val (coordinates.symm (coordinates (Additive.ofMul a))))
  rw [coordinates.symm_apply_apply]
  rfl

@[expose] def c8FourBinaryCoordinates : CyclicPair 2 4 →+ ZMod 2 × ZMod 2 :=
  (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)).toAddMonoidHom.prodMap
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

theorem c8FourBinaryCoordinates_zero (x : CyclicPair 2 4) :
    c8FourBinaryCoordinates x = 0 ↔ ∃ y : CyclicPair 2 4, 2 • y = x := by
  have h : ∀ x : CyclicPair 2 4, c8FourBinaryCoordinates x = 0 ↔
      ∃ y : CyclicPair 2 4, 2 • y = x := by decide +kernel
  exact h x

theorem c8_four_central_action_primitive_square {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (g : C8FourCode)
    (hsquare : g ^ 2 = 1) (hne : g ≠ 1) (hkernel : c8FourNormKernel g)
    (himage : c8FourNormDoubles g)
    (hcentral : ∀ s : S, Commute g (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)))
    (t : S) (hlift : c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) t) = g) :
    ∃ a : A, (a : S) = t ^ 2 ∧ (∀ b : A, a ≠ b ^ 2) ∧
      c8FourApply g (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  let α := e.symm g
  have hαsquare : α ^ 2 = 1 := by rw [← map_pow, hsquare, map_one]
  have hαne : α ≠ 1 := by
    intro h
    apply hne
    have h' := congrArg e h
    change e (e.symm g) = e 1 at h'
    simpa only [e.apply_symm_apply, map_one] using h'
  have hαcentral (s : S) : Commute α (MulAut.conjNormal (H := A) s) := by
    apply e.injective
    change e (e.symm g * MulAut.conjNormal (H := A) s) =
      e (MulAut.conjNormal (H := A) s * e.symm g)
    simpa only [map_mul, e.apply_symm_apply] using (hcentral s).eq
  have hnorm (a : A) : coordinates (Additive.ofMul (α a * a)) =
      c8FourApply g (coordinates (Additive.ofMul a)) + coordinates (Additive.ofMul a) := by
    change coordinates (Additive.ofMul (α a) + Additive.ofMul a) = _
    rw [map_add, c8FourAutomorphismEquiv_apply]
    change c8FourApply (e (e.symm g)) _ + _ = _
    rw [e.apply_symm_apply]
  have hαkernel (a : A) : α a * a = 1 ↔ a ^ 2 = 1 := by
    have hleft : α a * a = 1 ↔ c8FourApply g (coordinates (Additive.ofMul a)) + coordinates (Additive.ofMul a) = 0 := by
      rw [← hnorm, ← map_zero coordinates]
      constructor
      · intro h
        rw [h]
        rfl
      · intro h
        exact Additive.ofMul.injective (coordinates.injective h)
    have hright : a ^ 2 = 1 ↔ 2 • coordinates (Additive.ofMul a) = 0 := by
      rw [← map_nsmul, ← map_zero coordinates]
      constructor
      · intro h
        exact congrArg coordinates (congrArg Additive.ofMul h)
      · intro h
        exact Additive.ofMul.injective (coordinates.injective h)
    rw [hleft, hright]
    exact hkernel _
  let pairs : A ≃* Multiplicative (ZMod 8) × Multiplicative (ZMod 4) :=
    (AddEquiv.toMultiplicativeRight coordinates).trans (MulEquiv.prodMultiplicative _ _)
  have hcard := binary_rank_two_square_kernel_card A hcommutative (by decide : 0 < 3) (by decide : 0 < 2) pairs
  have hliftα : MulAut.conjNormal (H := A) t = α := e.injective (by rw [hlift, e.apply_symm_apply])
  obtain ⟨hmem, hnotNorm⟩ := central_action_involution_norm_obstruction A hcommutative hselfCentralizing
    hnoEight α hαsquare hαne hαcentral hαkernel hcard t hliftα
  let a : A := ⟨t ^ 2, hmem⟩
  have hprimitive (b : A) : a ≠ b ^ 2 := by
    intro h
    obtain ⟨x, hx⟩ := himage (coordinates (Additive.ofMul b))
    let c := (coordinates.symm x).toMul
    have heq : α c * c = b ^ 2 := by
      apply Additive.ofMul.injective
      apply coordinates.injective
      rw [hnorm]
      change c8FourApply g (coordinates (coordinates.symm x)) + coordinates (coordinates.symm x) =
        coordinates (2 • Additive.ofMul b)
      rw [coordinates.apply_symm_apply, hx, map_nsmul]
    exact hnotNorm c (congrArg Subtype.val (h.trans heq.symm))
  refine ⟨a, rfl, hprimitive, ?_⟩
  rw [← hlift, ← c8FourAutomorphismEquiv_apply]
  apply congrArg (fun b : A => coordinates (Additive.ofMul b))
  apply Subtype.ext
  change t * t ^ 2 * t⁻¹ = t ^ 2
  group

end CFSG.LargeEvenClassification.Helpers
