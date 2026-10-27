module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourResidual
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoResidualMap

public section

namespace CFSG.LargeEvenClassification.Helpers

open scoped commutatorElement

abbrev CyclicFourSpace (n : ℕ) := CyclicPair (2 ^ (n + 2)) 4
abbrev CyclicFourAut (n : ℕ) := (AddMonoid.End (CyclicFourSpace n))ˣ

instance cyclicFourEnd_finite (n : ℕ) : Finite (AddMonoid.End (CyclicFourSpace n)) :=
  Finite.of_equiv (CyclicPairCoefficients (2 ^ (n + 2)) 4)
    (cyclicPairEndCoefficientEquiv (2 ^ (n + 2)) 4).symm

theorem cyclicFourScale_zero (n : ℕ) : (2 ^ (n + 2) : ℕ) = (0 : ZMod 4) :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2))

@[expose] def residualRingTwistEquiv {r s : ZMod 4} (h : r = s) : ResidualRing r ≃+* ResidualRing s where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    change residualMultiply r x y = residualMultiply s x y
    rw [h]

@[expose] noncomputable def cyclicFourResidual (n : ℕ) : CyclicFourAut n →* (ResidualRing 0)ˣ :=
  (Units.map (residualRingTwistEquiv (cyclicFourScale_zero n)).toMonoidHom).comp
    (cyclicPairResidualUnits (2 ^ (n + 2)) 4 (by decide))

theorem cyclicFourResidual_val (n : ℕ) (g : CyclicFourAut n) :
    (cyclicFourResidual n g).val =
      ((cyclicReduction (2 ^ (n + 2)) 4 (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.1,
        (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.2),
        ((cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).2.1,
          (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).2.2)) := by
  have hcast : ∀ r : ResidualRing (2 ^ (n + 2) : ℕ),
      residualRingTwistEquiv (cyclicFourScale_zero n) r = r := fun _ => rfl
  change residualRingTwistEquiv (cyclicFourScale_zero n)
    (cyclicPairEndResidualHom (2 ^ (n + 2)) 4 (by decide) g.val) = _
  rw [hcast]
  change ((cyclicPairLargeReduction (2 ^ (n + 2)) 4 (by decide) _,
    cyclicPairSmallReduction 4 (by decide) _),
    (cyclicPairSmallReduction 4 (by decide) _, cyclicPairSmallReduction 4 (by decide) _)) = _
  have hsmall : cyclicPairSmallReduction 4 (by decide) = RingHom.id (ZMod 4) := RingHom.ext_zmod _ _
  rw [hsmall]
  rfl

theorem cyclicFourResidual_kernel (n : ℕ) :
    (cyclicFourResidual n).ker = principalFourSubgroup (AddMonoid.End (CyclicFourSpace n)) := by
  ext g
  change Units.map (residualRingTwistEquiv (cyclicFourScale_zero n)).toMonoidHom
    (cyclicPairResidualUnits (2 ^ (n + 2)) 4 (by decide) g) = 1 ↔ _
  have hmap : ∀ u : (ResidualRing (2 ^ (n + 2) : ℕ))ˣ,
      Units.map (residualRingTwistEquiv (cyclicFourScale_zero n)).toMonoidHom u = 1 ↔ u = 1 := by
    intro u
    constructor
    · intro h
      apply Units.ext
      have hv := congrArg (fun x : (ResidualRing 0)ˣ => x.val) h
      exact hv
    · rintro rfl
      exact map_one _
  rw [hmap]
  exact cyclicPairResidualUnits_kernel _ _ _ g

@[expose] noncomputable def cyclicFourDiagonal (n : ℕ) :
    (ZMod (2 ^ (n + 2) * 4))ˣ × (ZMod 4)ˣ →* CyclicFourAut n where
  toFun d := {
    val := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((d.1.val, 0), (0, d.2.val))
    inv := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((d.1.inv, 0), (0, d.2.inv))
    val_inv := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one,
        cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, add_zero, zero_add,
        d.1.val_inv, d.2.val_inv]
    inv_val := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one,
        cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, add_zero, zero_add,
        d.1.inv_val, d.2.inv_val] }
  map_one' := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 4
      (cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, 0), (0, 1))) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (1 : AddMonoid.End (CyclicFourSpace n))
    rw [cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
  map_mul' d e := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicPairEndFromCoefficients _ _ _) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 4
        (cyclicPairEndFromCoefficients _ _ _ * cyclicPairEndFromCoefficients _ _ _)
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
      cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, add_zero, zero_add]
    rfl

theorem cyclicFourDiagonal_coefficients (n : ℕ)
    (d : (ZMod (2 ^ (n + 2) * 4))ˣ × (ZMod 4)ˣ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourDiagonal n d).val =
      ((d.1.val, 0), (0, d.2.val)) := cyclicPairEndCoefficients_from _ _ _

@[expose] noncomputable def cyclicFourScalar (n : ℕ) :
    (ZMod (2 ^ (n + 2) * 4))ˣ →* CyclicFourAut n :=
  (cyclicFourDiagonal n).comp (MonoidHom.inl _ _)

theorem cyclicFourScalar_coefficients (n : ℕ) (d : (ZMod (2 ^ (n + 2) * 4))ˣ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourScalar n d).val = ((d.val, 0), (0, 1)) :=
  cyclicFourDiagonal_coefficients n (d, 1)

theorem cyclicFourScalar_injective (n : ℕ) : Function.Injective (cyclicFourScalar n) := by
  intro d e h
  apply Units.ext
  have hc := congrArg (fun g : CyclicFourAut n =>
    (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.1) h
  simpa only [cyclicFourScalar_coefficients] using hc

@[expose] noncomputable def cyclicFourUpper (n : ℕ) : Multiplicative (ZMod 4) →* CyclicFourAut n where
  toFun i := {
    val := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, i.toAdd), (0, 1))
    inv := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, -i.toAdd), (0, 1))
    val_inv := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one,
        cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one,
        one_mul, mul_one, one_mul, add_zero, zero_add, neg_add_cancel]
    inv_val := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one,
        cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one,
        one_mul, mul_one, one_mul, add_zero, zero_add, add_neg_cancel] }
  map_one' := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 4
      (cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, 0), (0, 1))) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (1 : AddMonoid.End (CyclicFourSpace n))
    rw [cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
  map_mul' i j := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicPairEndFromCoefficients _ _ _) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 4
        (cyclicPairEndFromCoefficients _ _ _ * cyclicPairEndFromCoefficients _ _ _)
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
      cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one, one_mul, mul_one, add_zero, zero_add]
    exact congrArg (fun b : ZMod 4 => ((1, b), (0, 1))) (add_comm _ _)

@[expose] noncomputable def cyclicFourLower (n : ℕ) : Multiplicative (ZMod 4) →* CyclicFourAut n where
  toFun j := {
    val := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, 0), (j.toAdd, 1))
    inv := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, 0), (-j.toAdd, 1))
    val_inv := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one,
        cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one,
        mul_one, one_mul, add_zero, zero_add, add_neg_cancel]
    inv_val := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one,
        cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one,
        mul_one, one_mul, add_zero, zero_add, neg_add_cancel] }
  map_one' := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 4
      (cyclicPairEndFromCoefficients (2 ^ (n + 2)) 4 ((1, 0), (0, 1))) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (1 : AddMonoid.End (CyclicFourSpace n))
    rw [cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
  map_mul' i j := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicPairEndFromCoefficients _ _ _) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 4
        (cyclicPairEndFromCoefficients _ _ _ * cyclicPairEndFromCoefficients _ _ _)
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
      cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one, mul_one, one_mul, add_zero, zero_add]
    rfl

theorem cyclicFourUpper_coefficients (n : ℕ) (i : Multiplicative (ZMod 4)) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourUpper n i).val = ((1, i.toAdd), (0, 1)) :=
  cyclicPairEndCoefficients_from _ _ _

theorem cyclicFourLower_coefficients (n : ℕ) (j : Multiplicative (ZMod 4)) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourLower n j).val = ((1, 0), (j.toAdd, 1)) :=
  cyclicPairEndCoefficients_from _ _ _

@[expose] noncomputable def cyclicFourU (n : ℕ) : CyclicFourAut n := cyclicFourUpper n (Multiplicative.ofAdd 1)
@[expose] noncomputable def cyclicFourV (n : ℕ) : CyclicFourAut n := cyclicFourLower n (Multiplicative.ofAdd 1)
@[expose] noncomputable def cyclicFourZ (n : ℕ) : CyclicFourAut n := cyclicFourDiagonal n (-1, 1)
@[expose] noncomputable def cyclicFourW (n : ℕ) : CyclicFourAut n := cyclicFourDiagonal n (1, -1)

theorem cyclicFourUpper_power (n : ℕ) (i : ZMod 4) :
    cyclicFourUpper n (Multiplicative.ofAdd i) = cyclicFourU n ^ i.val := by
  rw [cyclicFourU, ← map_pow (cyclicFourUpper n)]
  congr 1
  apply Multiplicative.toAdd.injective
  change i = i.val • (1 : ZMod 4)
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem cyclicFourLower_power (n : ℕ) (j : ZMod 4) :
    cyclicFourLower n (Multiplicative.ofAdd j) = cyclicFourV n ^ j.val := by
  rw [cyclicFourV, ← map_pow (cyclicFourLower n)]
  congr 1
  apply Multiplicative.toAdd.injective
  change j = j.val • (1 : ZMod 4)
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

@[expose] def cyclicFourModFour (n : ℕ) : (ZMod (2 ^ (n + 2) * 4))ˣ →* (ZMod 4)ˣ :=
  Units.map (cyclicReduction (2 ^ (n + 2)) 4).toMonoidHom

theorem cyclicFourModFour_kernel_cyclic (n : ℕ) : IsCyclic (cyclicFourModFour n).ker := by
  exact binary_unit_mod_four_kernel_cyclic_of_eq
    (show 2 ^ (n + 2) * 4 = 2 ^ ((n + 2) + 2) by
      rw [pow_add 2 (n + 2) 2]; norm_num) (dvd_mul_left 4 _)

@[expose] def cyclicFourFive (n : ℕ) : (ZMod (2 ^ (n + 2) * 4))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.mul_right
    ((by decide : Nat.Coprime 5 2).pow_right _) (by decide))

@[expose] noncomputable def cyclicFourC (n : ℕ) : CyclicFourAut n := cyclicFourScalar n (cyclicFourFive n)
@[expose] noncomputable def cyclicFourDelta (n : ℕ) : CyclicFourAut n := cyclicFourC n ^ (2 ^ (n + 1))

theorem cyclicFourFive_order (n : ℕ) : orderOf (cyclicFourFive n) = 2 ^ (n + 2) := by
  rw [← orderOf_units]
  change orderOf (5 : ZMod (2 ^ (n + 2) * 4)) = 2 ^ (n + 2)
  have h : 2 ^ (n + 2) * 4 = 2 ^ ((n + 2) + 2) := by rw [pow_add 2 (n + 2) 2]; norm_num
  rw [h]
  exact ZMod.orderOf_five (n + 2)

theorem cyclicFourC_order (n : ℕ) : orderOf (cyclicFourC n) = 2 ^ (n + 2) :=
  (orderOf_injective (cyclicFourScalar n) (cyclicFourScalar_injective n) _).trans (cyclicFourFive_order n)

theorem cyclicFourFive_mod_four (n : ℕ) : cyclicFourModFour n (cyclicFourFive n) = 1 := by
  apply Units.ext
  change cyclicReduction (2 ^ (n + 2)) 4 ((5 : ℕ) : ZMod (2 ^ (n + 2) * 4)) = 1
  rw [map_natCast]
  decide +kernel

theorem cyclicFourModFour_surjective (n : ℕ) : Function.Surjective (cyclicFourModFour n) :=
  ZMod.unitsMap_surjective (dvd_mul_left 4 (2 ^ (n + 2)))

theorem cyclicFourModFour_kernel_card (n : ℕ) : Nat.card (cyclicFourModFour n).ker = 2 ^ (n + 2) := by
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup (cyclicFourModFour n).ker
  have hsource : Nat.card (ZMod (2 ^ (n + 2) * 4))ˣ = 2 ^ (n + 3) := by
    have h : 2 ^ (n + 2) * 4 = 2 ^ ((n + 3) + 1) := by
      rw [show (n + 3) + 1 = (n + 2) + 2 by omega, pow_add 2 (n + 2) 2]; norm_num
    rw [h]
    exact binary_unit_card (n + 3)
  have hquotient : Nat.card ((ZMod (2 ^ (n + 2) * 4))ˣ ⧸ (cyclicFourModFour n).ker) = 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (cyclicFourModFour n)
      (cyclicFourModFour_surjective n)).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  rw [hsource, hquotient] at hformula
  have hpower : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := pow_succ' _ _
  omega

theorem cyclicFourModFour_kernel_eq_five (n : ℕ) :
    (cyclicFourModFour n).ker = Subgroup.zpowers (cyclicFourFive n) := by
  apply (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (cyclicFourFive_mod_four n)) ?_).symm
  rw [cyclicFourModFour_kernel_card, Nat.card_zpowers, cyclicFourFive_order]

theorem cyclicFourScalar_central (n : ℕ) (d : (ZMod (2 ^ (n + 2) * 4))ˣ)
    (hd : cyclicFourModFour n d = 1) (g : CyclicFourAut n) : Commute (cyclicFourScalar n d) g := by
  have hreduce : cyclicReduction (2 ^ (n + 2)) 4 d.val = 1 := congrArg Units.val hd
  apply Units.ext
  apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
  change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 ((cyclicFourScalar n d).val * g.val) =
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (g.val * (cyclicFourScalar n d).val)
  rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul, cyclicFourScalar_coefficients]
  dsimp only [cyclicPairCoefficientProduct]
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, one_mul, mul_one, hreduce]
  apply Prod.ext
  · apply Prod.ext
    · exact mul_comm _ _
    · rfl
  · apply Prod.ext
    · rfl
    · rfl

theorem cyclicFourResidual_scalar (n : ℕ) (d : (ZMod (2 ^ (n + 2) * 4))ˣ) :
    cyclicFourResidual n (cyclicFourScalar n d) = residualZeroDiagonalSection (cyclicFourModFour n d, 1) := by
  apply Units.ext
  rw [cyclicFourResidual_val, cyclicFourScalar_coefficients]
  rfl

theorem cyclicFourResidual_upper (n : ℕ) (i : Multiplicative (ZMod 4)) :
    cyclicFourResidual n (cyclicFourUpper n i) = residualZeroShear (Multiplicative.ofAdd (i.toAdd, 0)) := by
  apply Units.ext
  rw [cyclicFourResidual_val, cyclicFourUpper_coefficients, map_one]
  rfl

theorem cyclicFourResidual_lower (n : ℕ) (j : Multiplicative (ZMod 4)) :
    cyclicFourResidual n (cyclicFourLower n j) = residualZeroShear (Multiplicative.ofAdd (0, j.toAdd)) := by
  apply Units.ext
  rw [cyclicFourResidual_val, cyclicFourLower_coefficients, map_one]
  rfl

theorem cyclicFourResidual_z (n : ℕ) : cyclicFourResidual n (cyclicFourZ n) = residualZeroZ := by
  apply Units.ext
  rw [cyclicFourResidual_val, cyclicFourZ, cyclicFourDiagonal_coefficients]
  change ((cyclicReduction (2 ^ (n + 2)) 4 (-1), 0), (0, 1)) = ((-1, 0), (0, 1))
  rw [map_neg, map_one]

theorem cyclicFourResidual_w (n : ℕ) : cyclicFourResidual n (cyclicFourW n) = residualZeroW := by
  apply Units.ext
  rw [cyclicFourResidual_val, cyclicFourW, cyclicFourDiagonal_coefficients]
  change ((cyclicReduction (2 ^ (n + 2)) 4 1, 0), (0, -1)) = ((1, 0), (0, -1))
  rw [map_one]

theorem cyclicFourResidual_surjective (n : ℕ) : Function.Surjective (cyclicFourResidual n) := by
  intro r
  obtain ⟨i, j, e, f, hr⟩ := residualZero_generators_normal_form r
  refine ⟨cyclicFourU n ^ i.val * cyclicFourV n ^ j.val * cyclicFourZ n ^ e.val * cyclicFourW n ^ f.val, ?_⟩
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    cyclicFourU, cyclicFourV, cyclicFourResidual_upper, cyclicFourResidual_lower,
    cyclicFourResidual_z, cyclicFourResidual_w]
  exact hr.symm

theorem cyclicFourResidual_kernel_scalar (n : ℕ) :
    (cyclicFourResidual n).ker = Subgroup.zpowers (cyclicFourC n) := by
  apply le_antisymm
  · intro g hg
    have hc := congrArg (fun r : (ResidualRing 0)ˣ => r.val) hg
    rw [cyclicFourResidual_val] at hc
    have hupper : (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.2 = 0 :=
      congrArg (fun r : ResidualRing 0 => r.1.2) hc
    have hlower : (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).2.1 = 0 :=
      congrArg (fun r : ResidualRing 0 => r.2.1) hc
    have hshort : (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).2.2 = 1 :=
      congrArg (fun r : ResidualRing 0 => r.2.2) hc
    have hlong : cyclicReduction (2 ^ (n + 2)) 4
        (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.1 = 1 :=
      congrArg (fun r : ResidualRing 0 => r.1.1) hc
    let d : (ZMod (2 ^ (n + 2) * 4))ˣ := {
      val := (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.1
      inv := (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.inv).1.1
      val_inv := by
        have h := congrArg (fun f => (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 f).1.1) g.val_inv
        rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_one] at h
        simpa only [cyclicPairCoefficientProduct, hupper, zero_mul, map_zero, add_zero] using h
      inv_val := by
        have h := congrArg (fun f => (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 f).1.1) g.inv_val
        rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_one] at h
        simpa only [cyclicPairCoefficientProduct, hlower, mul_zero, map_zero, add_zero] using h }
    have hd : d ∈ Subgroup.zpowers (cyclicFourFive n) := by
      rw [← cyclicFourModFour_kernel_eq_five]
      exact Units.ext hlong
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hgscalar : cyclicFourScalar n d = g := by
      apply Units.ext
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      rw [cyclicFourScalar_coefficients]
      exact Prod.ext (Prod.ext rfl hupper.symm) (Prod.ext hlower.symm hshort.symm)
    rw [← hgscalar, ← hk, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  · apply Subgroup.zpowers_le.mpr
    change cyclicFourResidual n (cyclicFourScalar n (cyclicFourFive n)) = 1
    rw [cyclicFourResidual_scalar, cyclicFourFive_mod_four]
    rfl

theorem cyclicFourPrincipal_eq_scalar (n : ℕ) :
    principalFourSubgroup (AddMonoid.End (CyclicFourSpace n)) = Subgroup.zpowers (cyclicFourC n) :=
  (cyclicFourResidual_kernel n).symm.trans (cyclicFourResidual_kernel_scalar n)

theorem cyclicFourP_central (n : ℕ) :
    Subgroup.zpowers (cyclicFourC n) ≤ Subgroup.center (CyclicFourAut n) := by
  apply Subgroup.zpowers_le.mpr
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact (cyclicFourScalar_central n (cyclicFourFive n) (cyclicFourFive_mod_four n) g).eq.symm

instance cyclicFourP_normal (n : ℕ) : (Subgroup.zpowers (cyclicFourC n)).Normal :=
  subgroup_normal_of_central _ (cyclicFourP_central n)

@[expose] noncomputable def cyclicFourQuotientEquiv (n : ℕ) :
    (CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n)) ≃* (ResidualRing 0)ˣ :=
  (QuotientGroup.congr _ _ (MulEquiv.refl _) (by
    change Subgroup.map (MonoidHom.id _) (Subgroup.zpowers (cyclicFourC n)) = _
    rw [Subgroup.map_id, cyclicFourResidual_kernel_scalar])).trans
      (QuotientGroup.quotientKerEquivOfSurjective (cyclicFourResidual n) (cyclicFourResidual_surjective n))

theorem cyclicFourAut_normal_form (n : ℕ) (g : CyclicFourAut n) :
    ∃ (k : ℤ) (i j : ZMod 4) (e f : ZMod 2), g =
      cyclicFourC n ^ k * cyclicFourU n ^ i.val * cyclicFourV n ^ j.val *
        cyclicFourZ n ^ e.val * cyclicFourW n ^ f.val := by
  obtain ⟨i, j, e, f, hr⟩ := residualZero_generators_normal_form (cyclicFourResidual n g)
  let s := cyclicFourU n ^ i.val * cyclicFourV n ^ j.val * cyclicFourZ n ^ e.val * cyclicFourW n ^ f.val
  have hs : cyclicFourResidual n s = cyclicFourResidual n g := by
    dsimp only [s]
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      cyclicFourU, cyclicFourV, cyclicFourResidual_upper, cyclicFourResidual_lower,
      cyclicFourResidual_z, cyclicFourResidual_w]
    exact hr.symm
  have hker : g * s⁻¹ ∈ Subgroup.zpowers (cyclicFourC n) := by
    rw [← cyclicFourResidual_kernel_scalar]
    change cyclicFourResidual n (g * s⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hker
  refine ⟨k, i, j, e, f, ?_⟩
  have h : g = cyclicFourC n ^ k * s := by rw [hk, mul_assoc, inv_mul_cancel, mul_one]
  simpa only [s, mul_assoc] using h

theorem cyclicFourAut_generators (n : ℕ) :
    Subgroup.closure ({cyclicFourU n, cyclicFourV n, cyclicFourZ n, cyclicFourW n, cyclicFourC n} :
      Set (CyclicFourAut n)) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k, i, j, e, f, rfl⟩ := cyclicFourAut_normal_form n g
  apply Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

theorem cyclicFourAut_card (n : ℕ) : Nat.card (CyclicFourAut n) = 2 ^ (n + 8) := by
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup (cyclicFourResidual n).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (cyclicFourResidual n)
    (cyclicFourResidual_surjective n)).toEquiv, cyclicFourResidual_kernel_scalar,
    Nat.card_zpowers, cyclicFourC_order, residual_unit_card_eq_even (Or.inl rfl)] at hformula
  calc
    _ = 64 * 2 ^ (n + 2) := hformula
    _ = 2 ^ (6 + (n + 2)) := by rw [pow_add 2 6 (n + 2)]; norm_num
    _ = 2 ^ (n + 8) := by congr 1; omega

@[expose] noncomputable def cyclicFourOuter (n : ℕ) :
    CyclicFourAut n →* (ZMod 4)ˣ × (ZMod 4)ˣ := residualZeroDiagonal.comp (cyclicFourResidual n)

@[expose] noncomputable def cyclicFourShearPreimage (n : ℕ) : Subgroup (CyclicFourAut n) :=
  (cyclicFourOuter n).ker

theorem cyclicFourShearPreimage_normal_form (n : ℕ) (g : CyclicFourAut n)
    (hg : g ∈ cyclicFourShearPreimage n) :
    ∃ (k : ℤ) (i j : ZMod 4), g = cyclicFourC n ^ k * cyclicFourU n ^ i.val * cyclicFourV n ^ j.val := by
  have hr : cyclicFourResidual n g ∈ residualZeroShear.range := by
    rw [← residualZeroDiagonal_kernel]
    exact hg
  obtain ⟨x, hx⟩ := hr
  let s := cyclicFourU n ^ x.toAdd.1.val * cyclicFourV n ^ x.toAdd.2.val
  have hs : cyclicFourResidual n s = cyclicFourResidual n g := by
    dsimp only [s]
    rw [map_mul, map_pow, map_pow, cyclicFourU, cyclicFourV,
      cyclicFourResidual_upper, cyclicFourResidual_lower]
    change residualZeroU ^ x.toAdd.1.val * residualZeroV ^ x.toAdd.2.val = _
    rw [← residualZeroShear_powers]
    exact hx
  have hker : g * s⁻¹ ∈ Subgroup.zpowers (cyclicFourC n) := by
    rw [← cyclicFourResidual_kernel_scalar]
    change cyclicFourResidual n (g * s⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hker
  refine ⟨k, x.toAdd.1, x.toAdd.2, ?_⟩
  have h : g = cyclicFourC n ^ k * s := by rw [hk, mul_assoc, inv_mul_cancel, mul_one]
  simpa only [s, mul_assoc] using h

@[expose] def cyclicFourTopUnit (n : ℕ) : (ZMod (2 ^ (n + 2) * 4))ˣ :=
  ZMod.unitOfCoprime (1 + 2 ^ (n + 3)) (by
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      apply Nat.coprime_two_right.mpr
      exact Odd.add_even (by decide : Odd 1) (Even.pow_of_ne_zero (by decide : Even 2) (by omega))
    · change (1 + 2 ^ (n + 3)).Coprime (2 ^ 2)
      apply Nat.Coprime.pow_right (n := 2)
      apply Nat.coprime_two_right.mpr
      exact Odd.add_even (by decide : Odd 1) (Even.pow_of_ne_zero (by decide : Even 2) (by omega)))

theorem cyclicFourFive_half_power (n : ℕ) :
    cyclicFourFive n ^ (2 ^ (n + 1)) = cyclicFourTopUnit n := by
  have hmod : 2 ^ (n + 2) * 4 = 2 ^ ((n + 1) + 2) * 2 := by
    rw [show (n + 1) + 2 = (n + 2) + 1 by omega, pow_succ]
    ring
  let e := Units.mapEquiv (ZMod.ringEquivCongr hmod).toMulEquiv
  apply e.injective
  have hfive : e (cyclicFourFive n) = cyclicTwoFive (n + 1) := by
    apply Units.ext
    change ZMod.ringEquivCongr hmod (5 : ZMod _) = 5
    exact map_ofNat _ _
  have htop : e (cyclicFourTopUnit n) = cyclicTwoTopUnit (n + 1) := by
    apply Units.ext
    change ZMod.ringEquivCongr hmod ((1 + 2 ^ (n + 3) : ℕ) : ZMod _) = _
    rw [map_natCast, cyclicTwoTopUnit_val]
    push_cast
    rw [show n + 1 + 2 = n + 3 by omega]
  rw [map_pow, hfive, cyclicTwoFive_half_power, htop]

theorem cyclicFourDelta_coefficients (n : ℕ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourDelta n).val =
      ((1 + ((2 ^ (n + 3) : ℕ) : ZMod (2 ^ (n + 2) * 4)), 0), (0, 1)) := by
  rw [cyclicFourDelta, cyclicFourC, ← map_pow (cyclicFourScalar n),
    cyclicFourFive_half_power, cyclicFourScalar_coefficients]
  change ((((1 + 2 ^ (n + 3) : ℕ) : ZMod (2 ^ (n + 2) * 4)), 0), (0, 1)) = _
  push_cast
  rfl

theorem cyclicFourDelta_order (n : ℕ) : orderOf (cyclicFourDelta n) = 2 := by
  rw [cyclicFourDelta, orderOf_pow, cyclicFourC_order,
    Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega : n + 1 ≤ n + 2)), pow_succ,
    Nat.mul_div_cancel_left]
  positivity

theorem cyclicFourDelta_square (n : ℕ) : cyclicFourDelta n ^ 2 = 1 := by
  simpa only [cyclicFourDelta_order] using pow_orderOf_eq_one (cyclicFourDelta n)

theorem cyclicFourDelta_ne_one (n : ℕ) : cyclicFourDelta n ≠ 1 := by
  intro h
  have ho := cyclicFourDelta_order n
  rw [h, orderOf_one] at ho
  norm_num at ho

theorem cyclicFourU_fourth (n : ℕ) : cyclicFourU n ^ 4 = 1 := by
  rw [cyclicFourU, ← map_pow (cyclicFourUpper n)]
  have h : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1 := by decide +kernel
  rw [h, map_one]

theorem cyclicFourV_fourth (n : ℕ) : cyclicFourV n ^ 4 = 1 := by
  rw [cyclicFourV, ← map_pow (cyclicFourLower n)]
  have h : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1 := by decide +kernel
  rw [h, map_one]

theorem cyclicFourU_square_coefficients (n : ℕ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourU n ^ 2).val = ((1, 2), (0, 1)) := by
  have h : cyclicFourU n ^ 2 = cyclicFourUpper n (Multiplicative.ofAdd 2) :=
    (cyclicFourUpper_power n 2).symm
  rw [h, cyclicFourUpper_coefficients]
  rfl

theorem cyclicFourV_square_coefficients (n : ℕ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourV n ^ 2).val = ((1, 0), (2, 1)) := by
  have h : cyclicFourV n ^ 2 = cyclicFourLower n (Multiplicative.ofAdd 2) :=
    (cyclicFourLower_power n 2).symm
  rw [h, cyclicFourLower_coefficients]
  rfl

theorem cyclicFour_shear_squares_commute (n : ℕ) : Commute (cyclicFourU n ^ 2) (cyclicFourV n ^ 2) := by
  apply Units.ext
  apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
  change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 ((cyclicFourU n ^ 2).val * (cyclicFourV n ^ 2).val) =
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 ((cyclicFourV n ^ 2).val * (cyclicFourU n ^ 2).val)
  rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul,
    cyclicFourU_square_coefficients, cyclicFourV_square_coefficients]
  simp only [cyclicPairCoefficientProduct, map_one, map_zero, mul_zero, zero_mul,
    one_mul, mul_one, zero_add, add_zero, cyclicFourScale_zero]
  rw [show (2 * 2 : ZMod 4) = 0 by decide +kernel, map_zero, add_zero]

theorem cyclicFourZ_square (n : ℕ) : cyclicFourZ n ^ 2 = 1 := by
  rw [cyclicFourZ, ← map_pow (cyclicFourDiagonal n)]
  have hs : (-1 : (ZMod (2 ^ (n + 2) * 4))ˣ) ^ 2 = 1 := by
    apply Units.ext
    change (-1 : ZMod _) ^ 2 = 1
    ring
  rw [show ((-1, 1) : (ZMod (2 ^ (n + 2) * 4))ˣ × (ZMod 4)ˣ) ^ 2 = 1 from
    Prod.ext (by simpa only [Prod.pow_fst, Prod.fst_one] using hs) (by simp), map_one]

theorem cyclicFourW_square (n : ℕ) : cyclicFourW n ^ 2 = 1 := by
  rw [cyclicFourW, ← map_pow (cyclicFourDiagonal n)]
  have hs : (-1 : (ZMod 4)ˣ) ^ 2 = 1 := by
    apply Units.ext
    change (-1 : ZMod 4) ^ 2 = 1
    ring
  rw [show ((1, -1) : (ZMod (2 ^ (n + 2) * 4))ˣ × (ZMod 4)ˣ) ^ 2 = 1 from
    Prod.ext (by simp) (by simpa only [Prod.pow_snd, Prod.snd_one] using hs), map_one]

@[expose] def binaryInvolutionHom {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G where
  toFun e := g ^ e.toAdd.val
  map_one' := by
    change g ^ (0 : ZMod 2).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' e f := by
    have hc : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide +kernel
    have hproof (e f : ZMod 2) : g ^ (e + f).val = g ^ e.val * g ^ f.val := by
      rcases hc e with rfl | rfl <;> rcases hc f with rfl | rfl <;>
        simp only [zero_add, add_zero, ZMod.val_zero, ZMod.val_one, pow_zero,
          pow_one, one_mul, mul_one, show (1 + 1 : ZMod 2) = 0 by decide +kernel]
      exact hg.symm.trans (pow_two g)
    exact hproof e.toAdd f.toAdd

@[expose] noncomputable def cyclicFourEvenShearHom (n : ℕ) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* CyclicFourAut n :=
  (binaryInvolutionHom (cyclicFourU n ^ 2) (by
    simpa only [← pow_mul, show 2 * 2 = 4 by decide] using cyclicFourU_fourth n)).noncommCoprod
    (binaryInvolutionHom (cyclicFourV n ^ 2) (by
      simpa only [← pow_mul, show 2 * 2 = 4 by decide] using cyclicFourV_fourth n))
    (fun i j => (cyclicFour_shear_squares_commute n).pow_pow i.toAdd.val j.toAdd.val)

@[expose] noncomputable def cyclicFourElementaryHom (n : ℕ) :
    Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* CyclicFourAut n :=
  (binaryInvolutionHom (cyclicFourDelta n) (cyclicFourDelta_square n)).noncommCoprod
    (cyclicFourEvenShearHom n) (by
      intro e x
      have hcentral : cyclicFourDelta n ^ e.toAdd.val ∈ Subgroup.center (CyclicFourAut n) :=
        cyclicFourP_central n (Subgroup.pow_mem _
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) _)
      exact (Subgroup.mem_center_iff.mp hcentral _).symm)

@[expose] noncomputable def cyclicFourE (n : ℕ) : Subgroup (CyclicFourAut n) :=
  (cyclicFourElementaryHom n).range

theorem cyclicFourElementaryHom_spec (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    cyclicFourElementaryHom n x = cyclicFourDelta n ^ x.1.toAdd.val *
      ((cyclicFourU n ^ 2) ^ x.2.1.toAdd.val * (cyclicFourV n ^ 2) ^ x.2.2.toAdd.val) := rfl

theorem cyclicFourE_generators (n : ℕ) : cyclicFourE n =
    Subgroup.closure ({cyclicFourDelta n, cyclicFourU n ^ 2, cyclicFourV n ^ 2} : Set (CyclicFourAut n)) := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    rw [cyclicFourElementaryHom_spec]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨(Multiplicative.ofAdd 1, (1, 1)), ?_⟩
      change cyclicFourDelta n ^ (1 : ZMod 2).val *
        ((cyclicFourU n ^ 2) ^ (0 : ZMod 2).val * (cyclicFourV n ^ 2) ^ (0 : ZMod 2).val) = _
      simp only [ZMod.val_one, ZMod.val_zero, pow_zero, pow_one, mul_one]
    · refine ⟨(1, (Multiplicative.ofAdd 1, 1)), ?_⟩
      change cyclicFourDelta n ^ (0 : ZMod 2).val *
        ((cyclicFourU n ^ 2) ^ (1 : ZMod 2).val * (cyclicFourV n ^ 2) ^ (0 : ZMod 2).val) = _
      simp only [ZMod.val_one, ZMod.val_zero, pow_zero, pow_one, mul_one, one_mul]
    · refine ⟨(1, (1, Multiplicative.ofAdd 1)), ?_⟩
      change cyclicFourDelta n ^ (0 : ZMod 2).val *
        ((cyclicFourU n ^ 2) ^ (0 : ZMod 2).val * (cyclicFourV n ^ 2) ^ (1 : ZMod 2).val) = _
      simp only [ZMod.val_one, ZMod.val_zero, pow_zero, pow_one, one_mul]

theorem cyclicFourElementaryHom_residual (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    cyclicFourResidual n (cyclicFourElementaryHom n x) =
      residualZeroShear (Multiplicative.ofAdd
        (2 * (x.2.1.toAdd.val : ZMod 4), 2 * (x.2.2.toAdd.val : ZMod 4))) := by
  have hδ : cyclicFourResidual n (cyclicFourDelta n) = 1 := by
    apply (cyclicFourResidual_kernel_scalar n).symm.le
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  rw [cyclicFourElementaryHom_spec, map_mul, map_mul, map_pow, map_pow, map_pow,
    hδ, one_pow, one_mul]
  rw [← pow_mul, ← pow_mul, cyclicFourU, cyclicFourV,
    ← map_pow (cyclicFourResidual n),
    ← map_pow (cyclicFourUpper n), ← map_pow (cyclicFourLower n),
    cyclicFourResidual_upper, cyclicFourResidual_lower,
    ← map_mul residualZeroShear]
  congr 1
  apply Multiplicative.toAdd.injective
  change ((2 * x.2.1.toAdd.val) • (1 : ZMod 4), 0) +
    (0, (2 * x.2.2.toAdd.val) • (1 : ZMod 4)) = _
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one]
  · rfl
  · rfl

theorem cyclicFourElementaryHom_injective (n : ℕ) : Function.Injective (cyclicFourElementaryHom n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  have hres := congrArg (cyclicFourResidual n) hx
  rw [cyclicFourElementaryHom_residual, map_one] at hres
  have hb : 2 * (x.2.1.toAdd.val : ZMod 4) = 0 :=
    congrArg (fun r : (ResidualRing 0)ˣ => r.val.1.2) hres
  have hc : 2 * (x.2.2.toAdd.val : ZMod 4) = 0 :=
    congrArg (fun r : (ResidualRing 0)ˣ => r.val.2.1) hres
  have hi : ∀ i : ZMod 2, 2 * (i.val : ZMod 4) = 0 → i = 0 := by decide +kernel
  have hi0 : x.2.1 = 1 := Multiplicative.toAdd.injective (hi _ hb)
  have hj0 : x.2.2 = 1 := Multiplicative.toAdd.injective (hi _ hc)
  have he : x.1 = 1 := by
    have hs : cyclicFourDelta n ^ x.1.toAdd.val = 1 := by
      have hh : cyclicFourElementaryHom n x = 1 := hx
      rw [cyclicFourElementaryHom_spec, hi0, hj0] at hh
      change cyclicFourDelta n ^ x.1.toAdd.val *
        ((cyclicFourU n ^ 2) ^ (0 : ZMod 2).val * (cyclicFourV n ^ 2) ^ (0 : ZMod 2).val) = 1 at hh
      simpa only [ZMod.val_zero, pow_zero, mul_one] using hh
    have hcases : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide +kernel
    rcases hcases x.1.toAdd with h | h
    · exact Multiplicative.toAdd.injective h
    · rw [h, ZMod.val_one, pow_one] at hs
      exact (cyclicFourDelta_ne_one n hs).elim
  exact Prod.ext he (Prod.ext hi0 hj0)

theorem cyclicFourE_card (n : ℕ) : Nat.card (cyclicFourE n) = 8 := by
  change Nat.card (cyclicFourElementaryHom n).range = 8
  rw [← Nat.card_congr (MonoidHom.ofInjective (cyclicFourElementaryHom_injective n)).toEquiv,
    Nat.card_eq_fintype_card]
  decide +kernel

theorem cyclicFourE_elementary (n : ℕ) : CFSG.Open.IsElemAbelian 2 (cyclicFourE n) := by
  constructor
  · apply IsMulCommutative.of_comm
    intro e f
    obtain ⟨x, hx⟩ := e.property
    obtain ⟨y, hy⟩ := f.property
    apply Subtype.ext
    change e.val * f.val = f.val * e.val
    rw [← hx, ← hy, ← map_mul (cyclicFourElementaryHom n), ← map_mul (cyclicFourElementaryHom n)]
    exact congrArg (cyclicFourElementaryHom n) (mul_comm x y)
  · rintro e ⟨x, rfl⟩
    rw [← map_pow]
    have h : x ^ 2 = 1 := by
      apply Prod.ext
      · change x.1 ^ 2 = (1 : Multiplicative (ZMod 2))
        decide +revert +kernel
      · apply Prod.ext
        · change x.2.1 ^ 2 = (1 : Multiplicative (ZMod 2))
          decide +revert +kernel
        · change x.2.2 ^ 2 = (1 : Multiplicative (ZMod 2))
          decide +revert +kernel
    rw [h, map_one]

theorem cyclicFourP_square_one (n : ℕ) (p : CyclicFourAut n)
    (hp : p ∈ Subgroup.zpowers (cyclicFourC n)) (hsq : p ^ 2 = 1) :
    p = 1 ∨ p = cyclicFourDelta n := by
  by_cases h : p = 1
  · exact Or.inl h
  · right
    let P := Subgroup.zpowers (cyclicFourC n)
    have hP : IsPGroup 2 P := IsPGroup.of_card (by
      rw [Nat.card_zpowers, cyclicFourC_order] : Nat.card P = 2 ^ (n + 2))
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let x : P := ⟨p, hp⟩
    let δ : P := ⟨cyclicFourDelta n, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
    have hx : orderOf x = 2 := orderOf_eq_prime_iff.mpr
      ⟨Subtype.ext hsq, fun h₁ => h (congrArg Subtype.val h₁)⟩
    have hδ : orderOf δ = 2 :=
      (orderOf_injective P.subtype Subtype.val_injective δ).symm.trans (cyclicFourDelta_order n)
    exact congrArg Subtype.val (cyclic_two_group_involutions_unique x δ hx hδ)

theorem cyclicFourShearPreimage_square_one (n : ℕ) (g : CyclicFourAut n)
    (hg : g ∈ cyclicFourShearPreimage n) (hsq : g ^ 2 = 1) : g ∈ cyclicFourE n := by
  have hr : cyclicFourResidual n g ∈ residualZeroShear.range := by
    rw [← residualZeroDiagonal_kernel]
    exact hg
  obtain ⟨x, hx⟩ := hr
  have hrsq : residualZeroShear x ^ 2 = 1 := by rw [hx, ← map_pow, hsq, map_one]
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := (residualZeroShear_square x).mp hrsq
  let y := cyclicFourElementaryHom n (1, (Multiplicative.ofAdd i, Multiplicative.ofAdd j))
  have hy : cyclicFourResidual n y = cyclicFourResidual n g := by
    rw [cyclicFourElementaryHom_residual]
    rw [← hx]
    congr 1
    exact Multiplicative.toAdd.injective (Prod.ext hi.symm hj.symm)
  have hyp : y ∈ cyclicFourE n := ⟨_, rfl⟩
  have hy2 : y ^ 2 = 1 := (cyclicFourE_elementary n).2 y hyp
  have hp : g * y⁻¹ ∈ Subgroup.zpowers (cyclicFourC n) := by
    rw [← cyclicFourResidual_kernel_scalar]
    change cyclicFourResidual n (g * y⁻¹) = 1
    rw [map_mul, map_inv, hy, mul_inv_cancel]
  have hc : Commute (g * y⁻¹) y := (Subgroup.mem_center_iff.mp (cyclicFourP_central n hp) y).symm
  have hgform : g = (g * y⁻¹) * y := by group
  have hp2 : (g * y⁻¹) ^ 2 = 1 := by
    have h := hsq
    conv_lhs at h => rw [hgform, hc.mul_pow]
    rwa [hy2, mul_one] at h
  rcases cyclicFourP_square_one n _ hp hp2 with h | h
  · rw [hgform, h, one_mul]
    exact hyp
  · rw [hgform, h]
    exact Subgroup.mul_mem _ (by
      rw [cyclicFourE_generators]
      exact Subgroup.subset_closure (by simp)) hyp

theorem cyclicFourAut_double_diagonals (n : ℕ) (g : CyclicFourAut n) :
    2 * cyclicReduction (2 ^ (n + 2)) 4 (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).1.1 = 2 ∧
      2 * (cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val).2.2 = 2 := by
  have h : ∀ a b : ZMod 4, a * b = 1 ∨ a * b = 3 → 2 * a = 2 ∧ 2 * b = 2 := by
    decide +kernel
  have hd := residual_unit_determinant (cyclicFourResidual n g)
  change (cyclicFourResidual n g).val.1.1 * (cyclicFourResidual n g).val.2.2 -
    0 * (cyclicFourResidual n g).val.1.2 * (cyclicFourResidual n g).val.2.1 = 1 ∨
    (cyclicFourResidual n g).val.1.1 * (cyclicFourResidual n g).val.2.2 -
    0 * (cyclicFourResidual n g).val.1.2 * (cyclicFourResidual n g).val.2.1 = 3 at hd
  simp only [zero_mul, sub_zero] at hd
  have hs := h _ _ hd
  rw [cyclicFourResidual_val] at hs
  exact hs

theorem cyclicFourDelta_inclusion_coefficients (n : ℕ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (cyclicFourDelta n).val =
      ((1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 2, 0), (0, 1)) := by
  rw [cyclicFourDelta_coefficients]
  congr 2
  rw [scaledCyclicInclusion_apply]
  have hv : (2 : ZMod 4).val = 2 := by decide +kernel
  rw [hv, ← Nat.cast_mul, ← pow_succ]

instance cyclicFourD_normal (n : ℕ) : (Subgroup.zpowers (cyclicFourDelta n)).Normal :=
  subgroup_normal_of_central _ ((Subgroup.zpowers_le.mpr
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)).trans (cyclicFourP_central n))

theorem cyclicFourU_square_projected_commute (n : ℕ) (g : CyclicFourAut n) :
    Commute ((QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))) (cyclicFourU n ^ 2))
      ((QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))) g) := by
  let q := QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))
  let a := cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val
  have hd := cyclicFourAut_double_diagonals n g
  change 2 * cyclicReduction (2 ^ (n + 2)) 4 a.1.1 = 2 ∧ 2 * a.2.2 = 2 at hd
  have hdl : cyclicReduction (2 ^ (n + 2)) 4 a.1.1 * 2 = 2 := (mul_comm _ _).trans hd.1
  have hreduce : cyclicReduction (2 ^ (n + 2)) 4
      (scaledCyclicInclusion (2 ^ (n + 2)) 4 2) = 0 := by
    rw [cyclicReduction_inclusion, cyclicFourScale_zero, zero_mul]
  have hcase : ∀ c : ZMod 4, 2 * c = 0 ∨ 2 * c = 2 := by decide +kernel
  rcases hcase a.2.1 with hz | ht
  · have hc : Commute (cyclicFourU n ^ 2) g := by
      apply Units.ext
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 ((cyclicFourU n ^ 2).val * g.val) =
        cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (g.val * (cyclicFourU n ^ 2).val)
      rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul, cyclicFourU_square_coefficients]
      change cyclicPairCoefficientProduct _ _ ((1, 2), (0, 1)) a =
        cyclicPairCoefficientProduct _ _ a ((1, 2), (0, 1))
      simp only [cyclicPairCoefficientProduct, map_one, map_zero, zero_mul, mul_zero,
        one_mul, mul_one, add_zero, zero_add, cyclicFourScale_zero, hz, map_zero]
      rw [hdl, hd.2]
      exact congrArg (fun b : ZMod 4 => ((a.1.1, b), (a.2.1, a.2.2))) (add_comm _ _)
    exact hc.map q
  · have hc : cyclicFourU n ^ 2 * g = cyclicFourDelta n * (g * cyclicFourU n ^ 2) := by
      apply Units.ext
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 ((cyclicFourU n ^ 2).val * g.val) =
        cyclicPairEndCoefficients (2 ^ (n + 2)) 4
          ((cyclicFourDelta n).val * (g.val * (cyclicFourU n ^ 2).val))
      rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul,
        cyclicFourU_square_coefficients, cyclicFourDelta_inclusion_coefficients]
      change cyclicPairCoefficientProduct _ _ ((1, 2), (0, 1)) a =
        cyclicPairCoefficientProduct _ _ ((1 + scaledCyclicInclusion _ _ 2, 0), (0, 1))
          (cyclicPairCoefficientProduct _ _ a ((1, 2), (0, 1)))
      simp only [cyclicPairCoefficientProduct, map_one, map_zero, zero_mul, mul_zero,
        one_mul, mul_one, add_zero, zero_add, cyclicFourScale_zero, ht, map_add, hreduce]
      rw [hdl, hd.2]
      apply Prod.ext
      · apply Prod.ext
        · rw [add_mul, one_mul, mul_comm (scaledCyclicInclusion _ _ 2) a.1.1,
            ← scaledCyclicInclusion_scalar, mul_comm _ 2, hd.1]
        · exact add_comm _ _
      · rfl
    have hδ : q (cyclicFourDelta n) = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
    have h := congrArg q hc
    change q (cyclicFourU n ^ 2) * q g = q g * q (cyclicFourU n ^ 2)
    simpa only [map_mul, hδ, one_mul] using h

theorem cyclicFourV_square_projected_commute (n : ℕ) (g : CyclicFourAut n) :
    Commute ((QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))) (cyclicFourV n ^ 2))
      ((QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))) g) := by
  let q := QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))
  let a := cyclicPairEndCoefficients (2 ^ (n + 2)) 4 g.val
  have hd := cyclicFourAut_double_diagonals n g
  change 2 * cyclicReduction (2 ^ (n + 2)) 4 a.1.1 = 2 ∧ 2 * a.2.2 = 2 at hd
  have hds : a.2.2 * 2 = 2 := (mul_comm _ _).trans hd.2
  have hreduce : cyclicReduction (2 ^ (n + 2)) 4
      (scaledCyclicInclusion (2 ^ (n + 2)) 4 2) = 0 := by
    rw [cyclicReduction_inclusion, cyclicFourScale_zero, zero_mul]
  have hcase : ∀ b : ZMod 4, 2 * b = 0 ∨ 2 * b = 2 := by decide +kernel
  rcases hcase a.1.2 with hz | ht
  · have hc : Commute (cyclicFourV n ^ 2) g := by
      apply Units.ext
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 ((cyclicFourV n ^ 2).val * g.val) =
        cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (g.val * (cyclicFourV n ^ 2).val)
      rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul, cyclicFourV_square_coefficients]
      change cyclicPairCoefficientProduct _ _ ((1, 0), (2, 1)) a =
        cyclicPairCoefficientProduct _ _ a ((1, 0), (2, 1))
      simp only [cyclicPairCoefficientProduct, map_one, map_zero, zero_mul, mul_zero,
        one_mul, mul_one, add_zero, zero_add, cyclicFourScale_zero]
      rw [mul_comm a.1.2 2, hz, map_zero, add_zero, hd.1, hds]
      exact congrArg (fun c : ZMod 4 => ((a.1.1, a.1.2), (c, a.2.2))) (add_comm _ _)
    exact hc.map q
  · have hc : g * cyclicFourV n ^ 2 = cyclicFourDelta n * (cyclicFourV n ^ 2 * g) := by
      apply Units.ext
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 4
      change cyclicPairEndCoefficients (2 ^ (n + 2)) 4 (g.val * (cyclicFourV n ^ 2).val) =
        cyclicPairEndCoefficients (2 ^ (n + 2)) 4
          ((cyclicFourDelta n).val * ((cyclicFourV n ^ 2).val * g.val))
      rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul,
        cyclicFourV_square_coefficients, cyclicFourDelta_inclusion_coefficients]
      change cyclicPairCoefficientProduct _ _ a ((1, 0), (2, 1)) =
        cyclicPairCoefficientProduct _ _ ((1 + scaledCyclicInclusion _ _ 2, 0), (0, 1))
          (cyclicPairCoefficientProduct _ _ ((1, 0), (2, 1)) a)
      simp only [cyclicPairCoefficientProduct, map_one, map_zero, zero_mul, mul_zero,
        one_mul, mul_one, add_zero, zero_add, cyclicFourScale_zero, map_add, hreduce]
      rw [mul_comm a.1.2 2, ht, hd.1, hds]
      apply Prod.ext
      · apply Prod.ext
        · rw [add_mul, one_mul, mul_comm (scaledCyclicInclusion _ _ 2) a.1.1,
            ← scaledCyclicInclusion_scalar, mul_comm _ 2, hd.1]
        · rfl
      · exact Prod.ext (add_comm _ _) rfl
    have hδ : q (cyclicFourDelta n) = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
    have h := congrArg q hc
    exact (show Commute (q g) (q (cyclicFourV n ^ 2)) from by
      change q g * q (cyclicFourV n ^ 2) = q (cyclicFourV n ^ 2) * q g
      simpa only [map_mul, hδ, one_mul] using h).symm

theorem cyclicFourE_commutator_bound (n : ℕ) :
    ⁅cyclicFourE n, ⊤⁆ ≤ Subgroup.zpowers (cyclicFourDelta n) := by
  apply Subgroup.commutator_le.mpr
  intro e he g _
  obtain ⟨x, rfl⟩ := he
  let q := QuotientGroup.mk' (Subgroup.zpowers (cyclicFourDelta n))
  have hδ : q (cyclicFourDelta n) = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  have hc : Commute (q (cyclicFourElementaryHom n x)) (q g) := by
    rw [cyclicFourElementaryHom_spec, map_mul, map_mul, map_pow, map_pow, map_pow,
      hδ, one_pow, one_mul]
    exact ((cyclicFourU_square_projected_commute n g).pow_left _).mul_left
      ((cyclicFourV_square_projected_commute n g).pow_left _)
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅cyclicFourElementaryHom n x, g⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr hc

theorem cyclicFourQuotientEquiv_mk (n : ℕ) (g : CyclicFourAut n) :
    cyclicFourQuotientEquiv n ((QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) g) =
      cyclicFourResidual n g := by
  rfl

@[expose] noncomputable def cyclicFourQuotientOuter (n : ℕ) :
    (CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n)) →* (ZMod 4)ˣ × (ZMod 4)ˣ :=
  residualZeroDiagonal.comp (cyclicFourQuotientEquiv n).toMonoidHom

@[expose] noncomputable def cyclicFourN (n : ℕ) :
    Subgroup (CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n)) :=
  (cyclicFourQuotientOuter n).ker

instance cyclicFourN_normal (n : ℕ) : (cyclicFourN n).Normal :=
  (cyclicFourQuotientOuter n).normal_ker

theorem cyclicFourN_generators (n : ℕ) : cyclicFourN n =
    Subgroup.closure ({(QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) (cyclicFourU n),
      (QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) (cyclicFourV n)} :
        Set (CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n))) := by
  let q := QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hg : g ∈ cyclicFourShearPreimage n := hx
    obtain ⟨k, i, j, rfl⟩ := cyclicFourShearPreimage_normal_form n g hg
    change q _ ∈ _
    rw [map_mul, map_mul, map_pow, map_pow, map_zpow,
      show q (cyclicFourC n) = 1 from (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _),
      one_zpow, one_mul]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change residualZeroDiagonal (cyclicFourResidual n (cyclicFourU n)) = 1
      rw [cyclicFourU, cyclicFourResidual_upper]
      change residualZeroShear _ ∈ residualZeroDiagonal.ker
      rw [residualZeroDiagonal_kernel]
      exact ⟨_, rfl⟩
    · change residualZeroDiagonal (cyclicFourResidual n (cyclicFourV n)) = 1
      rw [cyclicFourV, cyclicFourResidual_lower]
      change residualZeroShear _ ∈ residualZeroDiagonal.ker
      rw [residualZeroDiagonal_kernel]
      exact ⟨_, rfl⟩

@[expose] noncomputable def cyclicFourNResidualEquiv (n : ℕ) :
    cyclicFourN n ≃* residualZeroDiagonal.ker where
  toFun x := ⟨cyclicFourQuotientEquiv n x.val, x.property⟩
  invFun x := ⟨(cyclicFourQuotientEquiv n).symm x.val, by
    change residualZeroDiagonal (cyclicFourQuotientEquiv n ((cyclicFourQuotientEquiv n).symm x.val)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((cyclicFourQuotientEquiv n).symm_apply_apply _)
  right_inv x := Subtype.ext ((cyclicFourQuotientEquiv n).apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul (cyclicFourQuotientEquiv n) x.val y.val)

@[expose] noncomputable def cyclicFourNCoordinates (n : ℕ) :
    cyclicFourN n ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  ((cyclicFourNResidualEquiv n).trans residualZeroShearEquiv.symm).trans
    (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4))

theorem cyclicFourQuotientOuter_surjective (n : ℕ) : Function.Surjective (cyclicFourQuotientOuter n) :=
  residualZeroDiagonal_surjective.comp (cyclicFourQuotientEquiv n).surjective

@[expose] noncomputable def cyclicFourOuterCoordinates (n : ℕ) :
    ((CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n)) ⧸ cyclicFourN n) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientKerEquivOfSurjective (cyclicFourQuotientOuter n)
    (cyclicFourQuotientOuter_surjective n)).trans
      (MulEquiv.prodCongr fourUnitSignEquiv.symm fourUnitSignEquiv.symm)

theorem cyclicFourShearPreimage_eq (n : ℕ) : cyclicFourShearPreimage n =
    (cyclicFourN n).comap (QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) := by
  ext g
  rfl

theorem cyclicFourP_cyclic (n : ℕ) : IsCyclic (Subgroup.zpowers (cyclicFourC n)) := inferInstance

theorem cyclicFourP_card (n : ℕ) : Nat.card (Subgroup.zpowers (cyclicFourC n)) = 2 ^ (n + 2) := by
  rw [Nat.card_zpowers, cyclicFourC_order]

theorem cyclicFourDelta_apply (n : ℕ) (x : CyclicFourSpace n) :
    (cyclicFourDelta n).val x =
      ((1 + ((2 ^ (n + 3) : ℕ) : ZMod (2 ^ (n + 2) * 4))) * x.1, x.2) := by
  rw [cyclicPairEnd_apply, cyclicFourDelta_coefficients]
  simp only [zero_mul, map_zero, add_zero, zero_add, one_mul]

theorem cyclicFourUpper_apply (n : ℕ) (i : Multiplicative (ZMod 4)) (x : CyclicFourSpace n) :
    (cyclicFourUpper n i).val x =
      (x.1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 (i.toAdd * x.2), x.2) := by
  rw [cyclicPairEnd_apply, cyclicFourUpper_coefficients]
  simp only [one_mul, zero_mul, zero_add]

theorem cyclicFourLower_apply (n : ℕ) (j : Multiplicative (ZMod 4)) (x : CyclicFourSpace n) :
    (cyclicFourLower n j).val x =
      (x.1, j.toAdd * cyclicReduction (2 ^ (n + 2)) 4 x.1 + x.2) := by
  rw [cyclicPairEnd_apply, cyclicFourLower_coefficients]
  simp only [one_mul, zero_mul, map_zero, add_zero]

theorem cyclicFourDiagonal_apply (n : ℕ)
    (d : (ZMod (2 ^ (n + 2) * 4))ˣ × (ZMod 4)ˣ) (x : CyclicFourSpace n) :
    (cyclicFourDiagonal n d).val x = (d.1.val * x.1, d.2.val * x.2) := by
  rw [cyclicPairEnd_apply, cyclicFourDiagonal_coefficients]
  simp only [zero_mul, map_zero, add_zero, zero_add]

theorem cyclicFourU_apply (n : ℕ) (x : CyclicFourSpace n) :
    (cyclicFourU n).val x = (x.1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 x.2, x.2) := by
  rw [cyclicFourU, cyclicFourUpper_apply]
  change (x.1 + scaledCyclicInclusion (2 ^ (n + 2)) 4 (1 * x.2), x.2) = _
  rw [one_mul]

theorem cyclicFourV_apply (n : ℕ) (x : CyclicFourSpace n) :
    (cyclicFourV n).val x = (x.1, cyclicReduction (2 ^ (n + 2)) 4 x.1 + x.2) := by
  rw [cyclicFourV, cyclicFourLower_apply]
  change (x.1, 1 * cyclicReduction (2 ^ (n + 2)) 4 x.1 + x.2) = _
  rw [one_mul]

theorem cyclicFourZ_apply (n : ℕ) (x : CyclicFourSpace n) :
    (cyclicFourZ n).val x = (-x.1, x.2) := by
  rw [cyclicFourZ, cyclicFourDiagonal_apply]
  change ((-1 : ZMod (2 ^ (n + 2) * 4)) * x.1, (1 : ZMod 4) * x.2) = _
  rw [neg_one_mul, one_mul]

theorem cyclicFourW_apply (n : ℕ) (x : CyclicFourSpace n) :
    (cyclicFourW n).val x = (x.1, -x.2) := by
  rw [cyclicFourW, cyclicFourDiagonal_apply]
  change ((1 : ZMod (2 ^ (n + 2) * 4)) * x.1, (-1 : ZMod 4) * x.2) = _
  rw [neg_one_mul, one_mul]

theorem cyclicFourC_apply (n : ℕ) (x : CyclicFourSpace n) :
    (cyclicFourC n).val x = (5 * x.1, x.2) := by
  rw [cyclicFourC]
  change (cyclicFourDiagonal n (cyclicFourFive n, 1)).val x = _
  rw [cyclicFourDiagonal_apply]
  change ((5 : ZMod (2 ^ (n + 2) * 4)) * x.1, (1 : ZMod 4) * x.2) = _
  rw [one_mul]

theorem rank_two_cyclic_times_four_automorphism_quotient (n : ℕ) :
    Subgroup.closure ({cyclicFourU n, cyclicFourV n, cyclicFourZ n, cyclicFourW n, cyclicFourC n} :
      Set (CyclicFourAut n)) = ⊤ ∧
    cyclicFourU n ^ 4 = 1 ∧ cyclicFourV n ^ 4 = 1 ∧
    cyclicFourZ n ^ 2 = 1 ∧ cyclicFourW n ^ 2 = 1 ∧
    IsCyclic (Subgroup.zpowers (cyclicFourC n)) ∧
    Nat.card (Subgroup.zpowers (cyclicFourC n)) = 2 ^ (n + 2) ∧
    Subgroup.zpowers (cyclicFourC n) ≤ Subgroup.center (CyclicFourAut n) ∧
    Subgroup.zpowers (cyclicFourC n) = principalFourSubgroup (AddMonoid.End (CyclicFourSpace n)) ∧
    (cyclicFourN n).Normal ∧
    cyclicFourN n = Subgroup.closure
      ({(QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) (cyclicFourU n),
        (QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) (cyclicFourV n)} :
        Set (CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n))) ∧
    Nonempty (cyclicFourN n ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    Nonempty (((CyclicFourAut n ⧸ Subgroup.zpowers (cyclicFourC n)) ⧸ cyclicFourN n) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    cyclicFourShearPreimage n = (cyclicFourN n).comap
      (QuotientGroup.mk' (Subgroup.zpowers (cyclicFourC n))) ∧
    (∀ g : CyclicFourAut n, g ∈ cyclicFourShearPreimage n → g ^ 2 = 1 → g ∈ cyclicFourE n) ∧
    cyclicFourE n = Subgroup.closure
      ({cyclicFourDelta n, cyclicFourU n ^ 2, cyclicFourV n ^ 2} : Set (CyclicFourAut n)) ∧
    CFSG.Open.IsElemAbelian 2 (cyclicFourE n) ∧ Nat.card (cyclicFourE n) = 8 ∧
    ⁅cyclicFourE n, ⊤⁆ ≤ Subgroup.zpowers (cyclicFourDelta n) ∧
    cyclicFourDelta n = cyclicFourC n ^ (2 ^ (n + 1)) ∧
    (∀ x : CyclicFourSpace n, (cyclicFourDelta n).val x =
      ((1 + ((2 ^ (n + 3) : ℕ) : ZMod (2 ^ (n + 2) * 4))) * x.1, x.2)) := by
  exact ⟨cyclicFourAut_generators n, cyclicFourU_fourth n, cyclicFourV_fourth n,
    cyclicFourZ_square n, cyclicFourW_square n, cyclicFourP_cyclic n, cyclicFourP_card n,
    cyclicFourP_central n, (cyclicFourPrincipal_eq_scalar n).symm, inferInstance,
    cyclicFourN_generators n, ⟨cyclicFourNCoordinates n⟩, ⟨cyclicFourOuterCoordinates n⟩,
    cyclicFourShearPreimage_eq n, cyclicFourShearPreimage_square_one n, cyclicFourE_generators n,
    cyclicFourE_elementary n, cyclicFourE_card n, cyclicFourE_commutator_bound n, rfl,
    cyclicFourDelta_apply n⟩

end CFSG.LargeEvenClassification.Helpers
