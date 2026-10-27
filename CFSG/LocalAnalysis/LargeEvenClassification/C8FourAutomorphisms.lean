module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoEndCoordinates
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LargeEvenClassification.Helpers

structure C8FourCode where
  index : Fin 128

instance c8FourDecidableEq : DecidableEq C8FourCode := fun g h =>
  if heq : g.index = h.index then isTrue (by cases g; cases h; cases heq; rfl)
  else isFalse (fun hequal => heq (congrArg C8FourCode.index hequal))

instance c8FourFintype : Fintype C8FourCode := Fintype.ofEquiv (Fin 128) {
  toFun := fun i => ⟨i⟩
  invFun := C8FourCode.index
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl }

@[expose] def c8FourCoefficients (g : C8FourCode) : CyclicPairCoefficients 2 4 :=
  (((2 * (g.index.val / 32) + 1 : ℕ), (g.index.val / 8 % 4 : ℕ)),
    ((g.index.val / 2 % 4 : ℕ), (2 * (g.index.val % 2) + 1 : ℕ)))

@[expose] def c8FourEncode (c : CyclicPairCoefficients 2 4) : C8FourCode :=
  ⟨Fin.ofNat 128 (c.1.1.val / 2 * 32 + c.1.2.val * 8 + c.2.1.val * 2 + c.2.2.val / 2)⟩

@[expose] def c8FourMultiply (g h : C8FourCode) : C8FourCode :=
  let a := c8FourCoefficients g
  let b := c8FourCoefficients h
  c8FourEncode (cyclicPairCoefficientProduct 2 4 a b)

@[expose] def c8FourInverseIndices : Array (Fin 128) :=
  #[0, 1, 6, 3, 4, 5, 2, 7, 24, 9, 107, 62, 92, 77, 47, 122, 16, 17, 86, 83, 20, 21, 82, 87, 8, 25, 59, 110, 76, 93, 127, 42, 32, 33, 34, 39, 36, 37, 38, 35, 40, 57, 31, 74, 108, 125, 91, 14, 48, 49, 114, 119, 52, 53, 118, 115, 56, 41, 79, 26, 124, 109, 11, 94, 64, 65, 70, 67, 68, 69, 66, 71, 88, 73, 43, 126, 28, 13, 111, 58, 80, 81, 22, 19, 84, 85, 18, 23, 72, 89, 123, 46, 12, 29, 63, 106, 96, 97, 98, 103, 100, 101, 102, 99, 104, 121, 95, 10, 44, 61, 27, 78, 112, 113, 50, 55, 116, 117, 54, 51, 120, 105, 15, 90, 60, 45, 75, 30]

@[expose] def c8FourInverse (g : C8FourCode) : C8FourCode :=
  ⟨c8FourInverseIndices[g.index.val]!⟩

instance c8FourCodeOne : One C8FourCode := ⟨⟨0⟩⟩
instance c8FourCodeMul : Mul C8FourCode := ⟨c8FourMultiply⟩
instance c8FourCodeInv : Inv C8FourCode := ⟨c8FourInverse⟩

set_option maxHeartbeats 8000000 in
theorem c8Four_coefficients_injective : Function.Injective c8FourCoefficients := by
  have h : ∀ g h : C8FourCode, c8FourCoefficients g = c8FourCoefficients h → g = h := by
    decide +kernel
  exact h

set_option maxHeartbeats 8000000 in
theorem c8Four_coefficients_mul (g h : C8FourCode) :
    c8FourCoefficients (g * h) =
      cyclicPairCoefficientProduct 2 4 (c8FourCoefficients g) (c8FourCoefficients h) := by
  have hfinite : ∀ g h : C8FourCode,
      c8FourCoefficients (c8FourMultiply g h) =
        cyclicPairCoefficientProduct 2 4 (c8FourCoefficients g) (c8FourCoefficients h) := by
    decide +kernel
  exact hfinite g h

@[expose] def c8FourNativeUnit (g : C8FourCode) : (AddMonoid.End (CyclicPair 2 4))ˣ where
  val := cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients g)
  inv := cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients g⁻¹)
  val_inv := by
    apply cyclicPairEndCoefficients_injective 2 4
    rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
      cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
    have h : ∀ g : C8FourCode,
        cyclicPairCoefficientProduct 2 4 (c8FourCoefficients g)
          (c8FourCoefficients (c8FourInverse g)) = ((1, 0), (0, 1)) := by
      decide +kernel
    exact h g
  inv_val := by
    apply cyclicPairEndCoefficients_injective 2 4
    rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
      cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
    have h : ∀ g : C8FourCode,
        cyclicPairCoefficientProduct 2 4 (c8FourCoefficients (c8FourInverse g))
          (c8FourCoefficients g) = ((1, 0), (0, 1)) := by
      decide +kernel
    exact h g

theorem c8FourNativeUnit_injective : Function.Injective c8FourNativeUnit := by
  intro g h heq
  apply c8Four_coefficients_injective
  have h := congrArg (fun u : (AddMonoid.End (CyclicPair 2 4))ˣ =>
    cyclicPairEndCoefficients 2 4 u.val) heq
  simpa only [c8FourNativeUnit, cyclicPairEndCoefficients_from] using h

theorem c8FourNativeUnit_one : c8FourNativeUnit 1 = 1 := by
  apply Units.ext
  apply cyclicPairEndCoefficients_injective 2 4
  change cyclicPairEndCoefficients 2 4 (cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients 1)) =
    cyclicPairEndCoefficients 2 4 (1 : AddMonoid.End (CyclicPair 2 4))
  rw [cyclicPairEndCoefficients_one]
  rw [cyclicPairEndCoefficients_from]
  decide +kernel

theorem c8FourNativeUnit_mul (g h : C8FourCode) :
    c8FourNativeUnit (g * h) = c8FourNativeUnit g * c8FourNativeUnit h := by
  apply Units.ext
  apply cyclicPairEndCoefficients_injective 2 4
  change cyclicPairEndCoefficients 2 4 (cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients (g * h))) =
    cyclicPairEndCoefficients 2 4
      (cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients g) *
        cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients h))
  rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
    cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_from, c8Four_coefficients_mul]

theorem c8FourNativeUnit_inv (g : C8FourCode) :
    c8FourNativeUnit g⁻¹ = (c8FourNativeUnit g)⁻¹ := by
  apply Units.ext
  rfl

instance c8FourCodeGroup : Group C8FourCode := Group.ofLeftAxioms
  (by
    intro g h k
    apply c8FourNativeUnit_injective
    simp only [c8FourNativeUnit_mul, mul_assoc])
  (by
    intro g
    apply c8FourNativeUnit_injective
    rw [c8FourNativeUnit_mul, c8FourNativeUnit_one, one_mul])
  (by
    intro g
    apply c8FourNativeUnit_injective
    rw [c8FourNativeUnit_mul, c8FourNativeUnit_inv, inv_mul_cancel, c8FourNativeUnit_one])

@[expose] def c8FourNativeHom : C8FourCode →* (AddMonoid.End (CyclicPair 2 4))ˣ where
  toFun := c8FourNativeUnit
  map_one' := c8FourNativeUnit_one
  map_mul' := c8FourNativeUnit_mul

set_option maxHeartbeats 8000000 in
theorem c8Four_unit_coefficients_odd (u : (AddMonoid.End (CyclicPair 2 4))ˣ) :
    (cyclicPairEndCoefficients 2 4 u.val).1.1.val % 2 = 1 ∧
      (cyclicPairEndCoefficients 2 4 u.val).2.2.val % 2 = 1 := by
  have h := congrArg (cyclicPairEndCoefficients 2 4) u.val_inv
  rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_one] at h
  let c := cyclicPairEndCoefficients 2 4 u.val
  let d := cyclicPairEndCoefficients 2 4 u.inv
  have hlong : c.1.1 * d.1.1 + scaledCyclicInclusion 2 4 (c.1.2 * d.2.1) = 1 :=
    congrArg (fun a : CyclicPairCoefficients 2 4 => a.1.1) h
  have hshort : 2 * c.2.1 * d.1.2 + c.2.2 * d.2.2 = 1 :=
    congrArg (fun a : CyclicPairCoefficients 2 4 => a.2.2) h
  have hlongFinite : ∀ a b : ZMod 8, ∀ z : ZMod 4,
      a * b + scaledCyclicInclusion 2 4 z = 1 → a.val % 2 = 1 := by decide +kernel
  have hshortFinite : ∀ a b r s : ZMod 4,
      2 * r * s + a * b = 1 → a.val % 2 = 1 := by decide +kernel
  exact ⟨hlongFinite _ _ _ hlong, hshortFinite _ _ _ _ hshort⟩

theorem c8FourNativeUnit_surjective : Function.Surjective c8FourNativeUnit := by
  intro u
  let c := cyclicPairEndCoefficients 2 4 u.val
  refine ⟨c8FourEncode c, ?_⟩
  apply Units.ext
  apply cyclicPairEndCoefficients_injective 2 4
  change cyclicPairEndCoefficients 2 4
    (cyclicPairEndFromCoefficients 2 4 (c8FourCoefficients (c8FourEncode c))) = c
  rw [cyclicPairEndCoefficients_from]
  have hfinite : ∀ c : CyclicPairCoefficients 2 4,
      c.1.1.val % 2 = 1 → c.2.2.val % 2 = 1 →
        c8FourCoefficients (c8FourEncode c) = c := by decide +kernel
  exact hfinite c (c8Four_unit_coefficients_odd u).1 (c8Four_unit_coefficients_odd u).2

@[expose] noncomputable def c8FourNativeEquiv :
    C8FourCode ≃* (AddMonoid.End (CyclicPair 2 4))ˣ :=
  MulEquiv.ofBijective c8FourNativeHom ⟨c8FourNativeUnit_injective, c8FourNativeUnit_surjective⟩

@[expose] def c8FourApply (g : C8FourCode) (x : CyclicPair 2 4) : CyclicPair 2 4 :=
  let c := c8FourCoefficients g
  (c.1.1 * x.1 + scaledCyclicInclusion 2 4 (c.1.2 * x.2),
    c.2.1 * cyclicReduction 2 4 x.1 + c.2.2 * x.2)

theorem c8FourNativeUnit_apply (g : C8FourCode) (x : CyclicPair 2 4) :
    (c8FourNativeUnit g).val x = c8FourApply g x := rfl

theorem c8Four_code_card : Nat.card C8FourCode = 128 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem c8Four_code_isPGroup : IsPGroup 2 C8FourCode :=
  IsPGroup.of_card (n := 7) c8Four_code_card

end CFSG.LargeEvenClassification.Helpers
