module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoResidualMap
public import CFSG.LocalAnalysis.LargeEvenClassification.NormObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.RankOneComparable

public section

namespace CFSG.LargeEvenClassification.Helpers

open scoped commutatorElement

abbrev CyclicTwoSpace (n : ℕ) := CyclicPair (2 ^ (n + 2)) 2
abbrev CyclicTwoAut (n : ℕ) := (AddMonoid.End (CyclicTwoSpace n))ˣ

@[expose] def binaryResidualShearHom : BinaryResidualRingˣ →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun u := Multiplicative.ofAdd (binaryResidualUnitCandidate u)
  map_one' := rfl
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change ((u.val * v.val).1.2, (u.val * v.val).2.1) =
      (u.val.1.2 + v.val.1.2, u.val.2.1 + v.val.2.1)
    change (u.val.1.1 * v.val.1.2 + u.val.1.2 * v.val.2.2,
      u.val.2.1 * v.val.1.1 + u.val.2.2 * v.val.2.1) = _
    rw [(binaryResidualUnit_diagonal u).1, (binaryResidualUnit_diagonal u).2,
      (binaryResidualUnit_diagonal v).1, (binaryResidualUnit_diagonal v).2]
    simp only [one_mul, mul_one]
    exact Prod.ext (add_comm _ _) rfl

theorem binaryResidualShearHom_injective : Function.Injective binaryResidualShearHom := by
  intro u v h
  exact binaryResidualUnitCandidate_injective (congrArg Multiplicative.toAdd h)

@[expose] noncomputable def cyclicTwoShearHom (n : ℕ) :
    CyclicTwoAut n →* Multiplicative (ZMod 2 × ZMod 2) :=
  binaryResidualShearHom.comp (cyclicTwoResidualUnits (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)))

theorem cyclicTwoAut_diagonal (n : ℕ) (u : CyclicTwoAut n) :
    cyclicReduction (2 ^ (n + 2)) 2 (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 u.val).1.1 = 1 ∧
      (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 u.val).2.2 = 1 :=
  binaryResidualUnit_diagonal (cyclicTwoResidualUnits (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)) u)

theorem cyclicTwo_unit_reduction (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) :
    cyclicReduction (2 ^ (n + 2)) 2 u.val = 1 := by
  have h := congrArg (cyclicReduction (2 ^ (n + 2)) 2) u.val_inv
  change cyclicReduction (2 ^ (n + 2)) 2 (u.val * u.inv) = cyclicReduction (2 ^ (n + 2)) 2 1 at h
  rw [map_mul, map_one] at h
  have hbinary : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide +kernel
  exact hbinary _ _ h

@[expose] noncomputable def cyclicTwoScalar (n : ℕ) :
    (ZMod (2 ^ (n + 2) * 2))ˣ →* CyclicTwoAut n where
  toFun u := {
    val := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((u.val, 0), (0, 1))
    inv := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((u.inv, 0), (0, 1))
    val_inv := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
      simp only [cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, add_zero,
        zero_add, mul_one]
      rw [u.val_inv]
    inv_val := by
      apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
      simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
      simp only [cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, add_zero,
        zero_add, mul_one]
      rw [u.inv_val] }
  map_one' := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 2
      (cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((1, 0), (0, 1))) = cyclicPairEndCoefficients (2 ^ (n + 2)) 2 1
    rw [cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
  map_mul' u v := by
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    change cyclicPairEndCoefficients (2 ^ (n + 2)) 2
      (cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((u.val * v.val, 0), (0, 1))) =
      cyclicPairEndCoefficients (2 ^ (n + 2)) 2
        (cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((u.val, 0), (0, 1)) *
          cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((v.val, 0), (0, 1)))
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from]
    simp only [cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, add_zero,
      zero_add, mul_one]

theorem cyclicTwoScalar_coefficients (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 2 (cyclicTwoScalar n u).val = ((u.val, 0), (0, 1)) :=
  cyclicPairEndCoefficients_from _ _ _

theorem cyclicTwoScalar_injective (n : ℕ) : Function.Injective (cyclicTwoScalar n) := by
  intro u v h
  apply Units.ext
  have hc := congrArg (fun g : CyclicTwoAut n => (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 g.val).1.1) h
  simpa only [cyclicTwoScalar_coefficients] using hc

theorem cyclicTwoScalar_central (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) (g : CyclicTwoAut n) :
    Commute (cyclicTwoScalar n u) g := by
  apply Units.ext
  apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
  change cyclicPairEndCoefficients (2 ^ (n + 2)) 2 ((cyclicTwoScalar n u).val * g.val) =
    cyclicPairEndCoefficients (2 ^ (n + 2)) 2 (g.val * (cyclicTwoScalar n u).val)
  rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_mul, cyclicTwoScalar_coefficients]
  have hu := cyclicTwo_unit_reduction n u
  dsimp only [cyclicPairCoefficientProduct]
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, one_mul, mul_one, hu]
  exact congrArg (fun z => ((z, (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 g.val).1.2),
    ((cyclicPairEndCoefficients (2 ^ (n + 2)) 2 g.val).2.1,
      (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 g.val).2.2))) (mul_comm _ _)

@[expose] noncomputable def cyclicTwoTau (n : ℕ) : CyclicTwoAut n := {
  val := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((1, 1), (0, 1))
  inv := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((1, 1), (0, 1))
  val_inv := by
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
    simp only [cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one,
      one_mul, add_zero, zero_add]
    rw [show (1 + 1 : ZMod 2) = 0 by decide +kernel]
  inv_val := by
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
    simp only [cyclicPairCoefficientProduct, mul_zero, zero_mul, map_zero, map_one,
      one_mul, add_zero, zero_add]
    rw [show (1 + 1 : ZMod 2) = 0 by decide +kernel] }

@[expose] noncomputable def cyclicTwoRho (n : ℕ) : CyclicTwoAut n := {
  val := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((1, 0), (1, 1))
  inv := cyclicPairEndFromCoefficients (2 ^ (n + 2)) 2 ((1, 0), (1, 1))
  val_inv := by
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
    simp only [cyclicPairCoefficientProduct, mul_zero, map_zero, map_one,
      mul_one, add_zero, zero_add]
    rw [show (1 + 1 : ZMod 2) = 0 by decide +kernel]
  inv_val := by
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    simp only [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from, cyclicPairEndCoefficients_one]
    simp only [cyclicPairCoefficientProduct, mul_zero, map_zero, map_one,
      mul_one, add_zero, zero_add]
    rw [show (1 + 1 : ZMod 2) = 0 by decide +kernel] }

theorem cyclicTwoTau_coefficients (n : ℕ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 2 (cyclicTwoTau n).val = ((1, 1), (0, 1)) :=
  cyclicPairEndCoefficients_from _ _ _

theorem cyclicTwoRho_coefficients (n : ℕ) :
    cyclicPairEndCoefficients (2 ^ (n + 2)) 2 (cyclicTwoRho n).val = ((1, 0), (1, 1)) :=
  cyclicPairEndCoefficients_from _ _ _

theorem cyclicTwoTau_square (n : ℕ) : cyclicTwoTau n ^ 2 = 1 := by
  apply Units.ext
  exact (cyclicTwoTau n).val_inv

theorem cyclicTwoRho_square (n : ℕ) : cyclicTwoRho n ^ 2 = 1 := by
  apply Units.ext
  exact (cyclicTwoRho n).val_inv

theorem cyclicTwoShearHom_spec (n : ℕ) (u : CyclicTwoAut n) :
    (cyclicTwoShearHom n u).toAdd =
      ((cyclicPairEndCoefficients (2 ^ (n + 2)) 2 u.val).1.2,
        (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 u.val).2.1) := rfl

theorem cyclicTwoShearHom_tau (n : ℕ) :
    cyclicTwoShearHom n (cyclicTwoTau n) = Multiplicative.ofAdd (1, 0) := by
  apply Multiplicative.toAdd.injective
  rw [cyclicTwoShearHom_spec, cyclicTwoTau_coefficients]
  rfl

theorem cyclicTwoShearHom_rho (n : ℕ) :
    cyclicTwoShearHom n (cyclicTwoRho n) = Multiplicative.ofAdd (0, 1) := by
  apply Multiplicative.toAdd.injective
  rw [cyclicTwoShearHom_spec, cyclicTwoRho_coefficients]
  rfl

theorem cyclicTwoShearHom_scalar (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) :
    cyclicTwoShearHom n (cyclicTwoScalar n u) = 1 := by
  apply Multiplicative.toAdd.injective
  rw [cyclicTwoShearHom_spec, cyclicTwoScalar_coefficients]
  rfl

theorem cyclicTwoShearHom_kernel (n : ℕ) : (cyclicTwoShearHom n).ker = (cyclicTwoScalar n).range := by
  apply le_antisymm
  · intro g hg
    have hresidual : cyclicTwoResidualUnits (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)) g = 1 := by
      apply binaryResidualShearHom_injective
      exact hg
    let embedding : CyclicTwoAut n →* (AddMonoid.End (CyclicTwoSpace n))ˣ := MonoidHom.id _
    let source : (cyclicTwoActionResidue (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)) embedding).ker :=
      ⟨g, hresidual⟩
    let u := (cyclicTwoActionKernelScalar (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)) embedding).toHomUnits source
    refine ⟨u, ?_⟩
    apply Units.ext
    apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
    rw [cyclicTwoScalar_coefficients]
    obtain ⟨hupper, hlower, hdiag⟩ :=
      cyclicTwoActionKernel_coefficients (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)) embedding source
    apply Prod.ext <;> apply Prod.ext
    · rfl
    · exact hupper.symm
    · exact hlower.symm
    · exact hdiag.symm
  · rintro g ⟨u, rfl⟩
    exact cyclicTwoShearHom_scalar n u

@[expose] def cyclicTwoTopUnit (n : ℕ) : (ZMod (2 ^ (n + 2) * 2))ˣ :=
  ZMod.unitOfCoprime (1 + 2 ^ (n + 2)) (by
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      apply Nat.coprime_two_right.mpr
      exact Odd.add_even (by decide : Odd 1) (Even.pow_of_ne_zero (by decide : Even 2) (by omega))
    · apply Nat.coprime_two_right.mpr
      exact Odd.add_even (by decide : Odd 1) (Even.pow_of_ne_zero (by decide : Even 2) (by omega)))

@[expose] noncomputable def cyclicTwoDelta (n : ℕ) : CyclicTwoAut n := cyclicTwoScalar n (cyclicTwoTopUnit n)

theorem cyclicTwoTopUnit_val (n : ℕ) : (cyclicTwoTopUnit n).val = 1 + (2 ^ (n + 2) : ℕ) := by
  change ((1 + 2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) = _
  rw [Nat.cast_add, Nat.cast_one]

theorem cyclicTwoTopUnit_square (n : ℕ) : cyclicTwoTopUnit n ^ 2 = 1 := by
  apply Units.ext
  change (cyclicTwoTopUnit n).val ^ 2 = 1
  rw [cyclicTwoTopUnit_val]
  have htwo : (2 : ZMod (2 ^ (n + 2) * 2)) * (2 ^ (n + 2) : ℕ) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using
      ZMod.natCast_self (2 ^ (n + 2) * 2)
  have hfour : ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) ^ 2 = 0 := by
    calc
      _ = ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) * 2 * (2 ^ (n + 1) : ℕ) := by
        push_cast
        rw [pow_two, mul_assoc, ← pow_succ']
      _ = 0 := by rw [mul_comm ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) 2, htwo, zero_mul]
  calc
    _ = 1 + 2 * (2 ^ (n + 2) : ℕ) + ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) ^ 2 := by ring
    _ = 1 := by rw [htwo, hfour]; ring

theorem cyclicTwoTopUnit_ne_one (n : ℕ) : cyclicTwoTopUnit n ≠ 1 := by
  intro h
  have hval := congrArg Units.val h
  change (cyclicTwoTopUnit n).val = 1 at hval
  rw [cyclicTwoTopUnit_val] at hval
  have hzero : ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) = 0 := by
    linear_combination hval
  have hle := Nat.le_of_dvd (by positivity : 0 < 2 ^ (n + 2)) ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hpositive : 0 < 2 ^ (n + 2) := by positivity
  omega

theorem cyclicTwoDelta_square (n : ℕ) : cyclicTwoDelta n ^ 2 = 1 := by
  rw [cyclicTwoDelta, ← map_pow, cyclicTwoTopUnit_square, map_one]

theorem cyclicTwoDelta_ne_one (n : ℕ) : cyclicTwoDelta n ≠ 1 := by
  intro h
  exact cyclicTwoTopUnit_ne_one n (cyclicTwoScalar_injective n (h.trans (map_one _).symm))

theorem cyclicTwoTauRho_commutator (n : ℕ) :
    ⁅cyclicTwoTau n, cyclicTwoRho n⁆ = cyclicTwoDelta n := by
  have hτinv : (cyclicTwoTau n)⁻¹ = cyclicTwoTau n := by
    exact (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using cyclicTwoTau_square n)).symm
  have hρinv : (cyclicTwoRho n)⁻¹ = cyclicTwoRho n := by
    exact (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using cyclicTwoRho_square n)).symm
  rw [commutatorElement_def, hτinv, hρinv]
  apply Units.ext
  apply cyclicPairEndCoefficients_injective (2 ^ (n + 2)) 2
  change cyclicPairEndCoefficients (2 ^ (n + 2)) 2
    ((cyclicTwoTau n).val * (cyclicTwoRho n).val * (cyclicTwoTau n).val * (cyclicTwoRho n).val) = _
  simp only [cyclicPairEndCoefficients_mul, cyclicTwoTau_coefficients, cyclicTwoRho_coefficients,
    cyclicTwoDelta, cyclicTwoScalar_coefficients]
  have hscale : (2 ^ (n + 2) : ℕ) = (0 : ZMod 2) := by
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_pow_self 2 (by omega))
  have hdouble : (2 ^ (n + 2) : ℕ) + (2 ^ (n + 2) : ℕ) = (0 : ZMod (2 ^ (n + 2) * 2)) := by
    rw [← Nat.cast_add, ← Nat.mul_two]
    exact ZMod.natCast_self _
  simp only [cyclicPairCoefficientProduct, map_one, map_zero, map_add, mul_zero,
    mul_one, add_zero, zero_add, scaledCyclicInclusion_one, hscale, cyclicTwoTopUnit_val]
  have hreduce : cyclicReduction (2 ^ (n + 2)) 2 (2 ^ (n + 2) : ℕ) = 0 := by
    rw [map_natCast, hscale]
  rw [hreduce]
  norm_num
  constructor
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdouble
  · decide +kernel

instance cyclicTwoEnd_finite (n : ℕ) : Finite (AddMonoid.End (CyclicTwoSpace n)) :=
  Finite.of_equiv (CyclicPairCoefficients (2 ^ (n + 2)) 2)
    (cyclicPairEndCoefficientEquiv (2 ^ (n + 2)) 2).symm

theorem cyclicTwoShearHom_surjective (n : ℕ) : Function.Surjective (cyclicTwoShearHom n) := by
  intro x
  have hcases : ∀ x : ZMod 2 × ZMod 2,
      x = (0, 0) ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = (1, 1) := by decide +kernel
  rcases hcases x.toAdd with h | h | h | h
  · refine ⟨1, ?_⟩
    rw [map_one]
    apply Multiplicative.toAdd.injective
    change (0, 0) = x.toAdd
    exact h.symm
  · exact ⟨cyclicTwoTau n, by apply Multiplicative.toAdd.injective; rw [cyclicTwoShearHom_tau]; exact h.symm⟩
  · exact ⟨cyclicTwoRho n, by apply Multiplicative.toAdd.injective; rw [cyclicTwoShearHom_rho]; exact h.symm⟩
  · refine ⟨cyclicTwoTau n * cyclicTwoRho n, ?_⟩
    rw [map_mul, cyclicTwoShearHom_tau, cyclicTwoShearHom_rho]
    apply Multiplicative.toAdd.injective
    exact h.symm

theorem cyclicTwoAut_normal_form (n : ℕ) (g : CyclicTwoAut n) :
    ∃ (v w : ZMod 2) (u : (ZMod (2 ^ (n + 2) * 2))ˣ),
      g = cyclicTwoTau n ^ v.val * cyclicTwoRho n ^ w.val * cyclicTwoScalar n u := by
  let v := (cyclicTwoShearHom n g).toAdd.1
  let w := (cyclicTwoShearHom n g).toAdd.2
  let lift := cyclicTwoTau n ^ v.val * cyclicTwoRho n ^ w.val
  have hsame : cyclicTwoShearHom n lift = cyclicTwoShearHom n g := by
    rw [map_mul, map_pow, map_pow, cyclicTwoShearHom_tau, cyclicTwoShearHom_rho]
    apply Multiplicative.toAdd.injective
    change v.val • ((1, 0) : ZMod 2 × ZMod 2) + w.val • ((0, 1) : ZMod 2 × ZMod 2) = (v, w)
    apply Prod.ext <;> simp [nsmul_eq_mul]
  have hker : lift⁻¹ * g ∈ (cyclicTwoShearHom n).ker := by
    change cyclicTwoShearHom n (lift⁻¹ * g) = 1
    rw [map_mul, map_inv, hsame]
    apply Multiplicative.toAdd.injective
    change -((cyclicTwoShearHom n g).toAdd) + (cyclicTwoShearHom n g).toAdd = 0
    exact neg_add_cancel _
  rw [cyclicTwoShearHom_kernel] at hker
  obtain ⟨u, hu⟩ := hker
  refine ⟨v, w, u, ?_⟩
  rw [hu]
  exact (mul_inv_cancel_left lift g).symm

theorem cyclicTwoAut_scalar_center (n : ℕ) :
    (cyclicTwoScalar n).range = Subgroup.center (CyclicTwoAut n) := by
  apply le_antisymm
  · rintro g ⟨u, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro h
    exact (cyclicTwoScalar_central n u h).eq.symm
  · intro g hg
    rw [← cyclicTwoShearHom_kernel]
    apply Multiplicative.toAdd.injective
    rw [cyclicTwoShearHom_spec]
    have hτ := Subgroup.mem_center_iff.mp hg (cyclicTwoTau n)
    have hρ := Subgroup.mem_center_iff.mp hg (cyclicTwoRho n)
    have hτcoeff := congrArg (fun u : CyclicTwoAut n =>
      (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 u.val).1.1) hτ
    have hρcoeff := congrArg (fun u : CyclicTwoAut n =>
      (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 u.val).1.1) hρ
    change (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 ((cyclicTwoTau n).val * g.val)).1.1 =
      (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 (g.val * (cyclicTwoTau n).val)).1.1 at hτcoeff
    change (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 ((cyclicTwoRho n).val * g.val)).1.1 =
      (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 (g.val * (cyclicTwoRho n).val)).1.1 at hρcoeff
    simp only [cyclicPairEndCoefficients_mul, cyclicTwoTau_coefficients, cyclicPairCoefficientProduct,
      one_mul, mul_one, mul_zero, map_zero, add_zero] at hτcoeff
    simp only [cyclicPairEndCoefficients_mul, cyclicTwoRho_coefficients, cyclicPairCoefficientProduct,
      one_mul, mul_one, zero_mul, map_zero, add_zero] at hρcoeff
    have hw : (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 g.val).2.1 = 0 := by
      apply scaledCyclicInclusion_injective (2 ^ (n + 2)) 2 (by positivity)
      rw [map_zero]
      exact add_left_cancel (hτcoeff.trans (add_zero _).symm)
    have hv : (cyclicPairEndCoefficients (2 ^ (n + 2)) 2 g.val).1.2 = 0 := by
      apply scaledCyclicInclusion_injective (2 ^ (n + 2)) 2 (by positivity)
      rw [map_zero]
      exact add_left_cancel (hρcoeff.symm.trans (add_zero _).symm)
    exact Prod.ext hv hw

theorem cyclicTwoAut_card (n : ℕ) : Nat.card (CyclicTwoAut n) = 2 ^ (n + 4) := by
  have hkerEquiv := MonoidHom.ofInjective (cyclicTwoScalar_injective n)
  have hker : Nat.card (cyclicTwoShearHom n).ker = 2 ^ (n + 2) := by
    rw [cyclicTwoShearHom_kernel, ← Nat.card_congr hkerEquiv.toEquiv]
    have hmod : 2 ^ (n + 2) * 2 = 2 ^ (n + 3) := (pow_succ 2 (n + 2)).symm
    rw [hmod]
    exact binary_unit_card (n + 2)
  have hquot : Nat.card (CyclicTwoAut n ⧸ (cyclicTwoShearHom n).ker) = 4 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (cyclicTwoShearHom n)
      (cyclicTwoShearHom_surjective n)).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (cyclicTwoShearHom n).ker
  rw [hker, hquot] at hcard
  exact hcard.trans (by
    calc
      4 * 2 ^ (n + 2) = 2 ^ (n + 2) * 2 ^ 2 := by
        norm_num
        exact Nat.mul_comm _ _
      _ = 2 ^ ((n + 2) + 2) := (pow_add _ _ _).symm
      _ = 2 ^ (n + 4) := by congr 1)

@[expose] noncomputable def cyclicTwoUnitEquiv (n : ℕ) :
    (ZMod (2 ^ (n + 2) * 2))ˣ ≃* (ZMod (2 ^ (n + 3)))ˣ :=
  Units.mapEquiv (ZMod.ringEquivCongr (pow_succ 2 (n + 2)).symm).toMulEquiv

@[expose] def cyclicTwoModFour (n : ℕ) : (ZMod (2 ^ (n + 2) * 2))ˣ →* (ZMod 4)ˣ :=
  ZMod.unitsMap (by
    have h : 4 ∣ 2 ^ (n + 2) := by exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2)
    exact h.trans (dvd_mul_right _ _))

theorem binary_unit_mod_four_kernel_cyclic_of_eq {modulus exponent : ℕ}
    (hmodulus : modulus = 2 ^ (exponent + 2)) (hdivides : 4 ∣ modulus) :
    IsCyclic (ZMod.unitsMap hdivides).ker := by
  subst modulus
  exact binary_unit_mod_four_kernel_cyclic exponent

theorem cyclicTwoModFour_kernel_cyclic (n : ℕ) : IsCyclic (cyclicTwoModFour n).ker :=
  binary_unit_mod_four_kernel_cyclic_of_eq (by rw [← pow_succ] : 2 ^ (n + 2) * 2 = 2 ^ ((n + 1) + 2)) _

@[expose] def cyclicTwoFive (n : ℕ) : (ZMod (2 ^ (n + 2) * 2))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.mul_right ((by decide : Nat.Coprime 5 2).pow_right _) (by decide))

@[expose] noncomputable def cyclicTwoC (n : ℕ) : CyclicTwoAut n := cyclicTwoScalar n (cyclicTwoFive n)
@[expose] noncomputable def cyclicTwoZ (n : ℕ) : CyclicTwoAut n := cyclicTwoScalar n (-1)

theorem cyclicTwoFive_order (n : ℕ) : orderOf (cyclicTwoFive n) = 2 ^ (n + 1) := by
  rw [← orderOf_units]
  change orderOf (5 : ZMod (2 ^ (n + 2) * 2)) = 2 ^ (n + 1)
  have h : 2 ^ (n + 2) * 2 = 2 ^ ((n + 1) + 2) := by rw [← pow_succ]
  rw [h]
  exact ZMod.orderOf_five (n + 1)

theorem cyclicTwoC_order (n : ℕ) : orderOf (cyclicTwoC n) = 2 ^ (n + 1) := by
  exact (orderOf_injective (cyclicTwoScalar n) (cyclicTwoScalar_injective n) (cyclicTwoFive n)).trans
    (cyclicTwoFive_order n)

theorem cyclicTwoZ_square (n : ℕ) : cyclicTwoZ n ^ 2 = 1 := by
  rw [cyclicTwoZ, ← map_pow]
  have h : (-1 : (ZMod (2 ^ (n + 2) * 2))ˣ) ^ 2 = 1 := by
    apply Units.ext
    change (-1 : ZMod (2 ^ (n + 2) * 2)) ^ 2 = 1
    ring
  rw [h, map_one]

theorem cyclicTwoTopUnit_mod_four (n : ℕ) : cyclicTwoModFour n (cyclicTwoTopUnit n) = 1 := by
  apply Units.ext
  change (ZMod.castHom (show 4 ∣ 2 ^ (n + 2) * 2 from
    (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans (dvd_mul_right _ _)) (ZMod 4)) (cyclicTwoTopUnit n).val = 1
  rw [cyclicTwoTopUnit_val, map_add, map_one, map_natCast]
  have h : ((2 ^ (n + 2) : ℕ) : ZMod 4) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2))
  rw [h, add_zero]

theorem cyclicTwoFive_mod_four (n : ℕ) : cyclicTwoModFour n (cyclicTwoFive n) = 1 := by
  apply Units.ext
  change (ZMod.castHom (show 4 ∣ 2 ^ (n + 2) * 2 from
    (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans (dvd_mul_right _ _)) (ZMod 4))
      ((5 : ℕ) : ZMod (2 ^ (n + 2) * 2)) = 1
  rw [map_natCast]
  decide +kernel

theorem cyclicTwoFive_half_power (n : ℕ) : cyclicTwoFive n ^ (2 ^ n) = cyclicTwoTopUnit n := by
  let P := (cyclicTwoModFour n).ker
  let : IsCyclic P := cyclicTwoModFour_kernel_cyclic n
  have hPgroup : IsPGroup 2 P := by
    have hmod : 2 ^ (n + 2) * 2 = 2 ^ (n + 3) := (pow_succ _ _).symm
    have hp : IsPGroup 2 (ZMod (2 ^ (n + 2) * 2))ˣ := by
      rw [hmod]
      exact binary_units_isPGroup _
    exact hp.to_subgroup P
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let c : P := ⟨cyclicTwoFive n, cyclicTwoFive_mod_four n⟩
  let δ : P := ⟨cyclicTwoTopUnit n, cyclicTwoTopUnit_mod_four n⟩
  have hc : orderOf (c ^ 2 ^ n) = 2 := by
    have horder : orderOf c = 2 ^ (n + 1) := by
      exact (orderOf_injective P.subtype Subtype.val_injective c).symm.trans (cyclicTwoFive_order n)
    rw [orderOf_pow, horder,
      Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega)), pow_succ, Nat.mul_div_cancel_left]
    positivity
  have hδ : orderOf δ = 2 := orderOf_eq_prime_iff.mpr
    ⟨Subtype.ext (cyclicTwoTopUnit_square n), fun h => cyclicTwoTopUnit_ne_one n (congrArg Subtype.val h)⟩
  exact congrArg Subtype.val (cyclic_two_group_involutions_unique (c ^ 2 ^ n) δ hc hδ)

theorem cyclicTwoC_half_power (n : ℕ) : cyclicTwoC n ^ (2 ^ n) = cyclicTwoDelta n := by
  rw [cyclicTwoC, ← map_pow, cyclicTwoFive_half_power]
  rfl

theorem cyclicTwoModFour_surjective (n : ℕ) : Function.Surjective (cyclicTwoModFour n) :=
  ZMod.unitsMap_surjective _

theorem cyclicTwoModFour_kernel_card (n : ℕ) : Nat.card (cyclicTwoModFour n).ker = 2 ^ (n + 1) := by
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup (cyclicTwoModFour n).ker
  have hsource : Nat.card (ZMod (2 ^ (n + 2) * 2))ˣ = 2 ^ (n + 2) := by
    rw [← pow_succ]
    exact binary_unit_card _
  have hquotient : Nat.card ((ZMod (2 ^ (n + 2) * 2))ˣ ⧸ (cyclicTwoModFour n).ker) = 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (cyclicTwoModFour n)
      (cyclicTwoModFour_surjective n)).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  rw [hsource, hquotient] at hformula
  have hpower : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := pow_succ' _ _
  omega

theorem cyclicTwoModFour_kernel_eq_five (n : ℕ) :
    (cyclicTwoModFour n).ker = Subgroup.zpowers (cyclicTwoFive n) := by
  apply (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (cyclicTwoFive_mod_four n)) ?_).symm
  rw [cyclicTwoModFour_kernel_card, Nat.card_zpowers, cyclicTwoFive_order]

theorem cyclicTwo_scalar_normal_form (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) :
    ∃ (j : ℤ) (e : ZMod 2), u = cyclicTwoFive n ^ j * (-1) ^ e.val := by
  have hcases : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1 := by decide +kernel
  rcases hcases (cyclicTwoModFour n u) with h | h
  · have hmem : u ∈ Subgroup.zpowers (cyclicTwoFive n) := cyclicTwoModFour_kernel_eq_five n ▸ h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨j, 0, by simpa only [ZMod.val_zero, pow_zero, mul_one] using hj.symm⟩
  · have hneg : cyclicTwoModFour n (-1 : (ZMod (2 ^ (n + 2) * 2))ˣ) = -1 := by
      apply Units.ext
      change (ZMod.castHom (show 4 ∣ 2 ^ (n + 2) * 2 from (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans (dvd_mul_right _ _)) (ZMod 4)) (-1 : ZMod (2 ^ (n + 2) * 2)) = -1
      rw [map_neg, map_one]
    have hmem : u * (-1) ∈ Subgroup.zpowers (cyclicTwoFive n) := by
      rw [← cyclicTwoModFour_kernel_eq_five]
      change cyclicTwoModFour n (u * (-1)) = 1
      rw [map_mul, h, hneg]
      apply Units.ext
      change (-1 : ZMod 4) * (-1) = 1
      ring
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨j, 1, ?_⟩
    rw [ZMod.val_one, pow_one, hj]
    have hsq : (-1 : (ZMod (2 ^ (n + 2) * 2))ˣ) * (-1) = 1 := by
      apply Units.ext
      change (-1 : ZMod (2 ^ (n + 2) * 2)) * (-1) = 1
      ring
    rw [mul_assoc, hsq, mul_one]

theorem cyclicTwoAut_generators (n : ℕ) :
    Subgroup.closure ({cyclicTwoTau n, cyclicTwoRho n, cyclicTwoC n, cyclicTwoZ n} : Set (CyclicTwoAut n)) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨v, w, u, rfl⟩ := cyclicTwoAut_normal_form n g
  obtain ⟨j, e, rfl⟩ := cyclicTwo_scalar_normal_form n u
  rw [map_mul, map_zpow, map_pow]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp)
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp)
  · apply Subgroup.mul_mem
    · apply Subgroup.zpow_mem
      exact Subgroup.subset_closure (by simp [cyclicTwoC])
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp [cyclicTwoZ])

theorem cyclicTwoAut_center_generators (n : ℕ) :
    Subgroup.center (CyclicTwoAut n) = Subgroup.zpowers (cyclicTwoC n) ⊔ Subgroup.zpowers (cyclicTwoZ n) := by
  rw [← cyclicTwoAut_scalar_center]
  apply le_antisymm
  · rintro g ⟨u, rfl⟩
    obtain ⟨j, e, rfl⟩ := cyclicTwo_scalar_normal_form n u
    rw [map_mul, map_zpow, map_pow]
    exact (Subgroup.zpowers (cyclicTwoC n) ⊔ Subgroup.zpowers (cyclicTwoZ n)).mul_mem
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · apply sup_le
    · exact Subgroup.zpowers_le.mpr ⟨cyclicTwoFive n, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨-1, rfl⟩

theorem cyclicTwoAut_center_disjoint (n : ℕ) :
    Disjoint (Subgroup.zpowers (cyclicTwoC n)) (Subgroup.zpowers (cyclicTwoZ n)) := by
  apply Subgroup.disjoint_def.mpr
  intro g hc hz
  have hcentralC := Subgroup.zpowers_le.mpr
    (show cyclicTwoC n ∈ (cyclicTwoScalar n).range from ⟨cyclicTwoFive n, rfl⟩)
  obtain ⟨u, hu⟩ := hcentralC hc
  have hCmod : cyclicTwoModFour n u = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
    have heq : cyclicTwoScalar n u = cyclicTwoScalar n (cyclicTwoFive n ^ j) := by
      rw [map_zpow]
      exact hu.trans hj.symm
    rw [cyclicTwoScalar_injective n heq, map_zpow, cyclicTwoFive_mod_four, one_zpow]
  rcases zpowers_involution_cases (cyclicTwoZ n) (cyclicTwoZ_square n) hz with h | h
  · exact h
  · have heq : u = -1 := cyclicTwoScalar_injective n (hu.trans h)
    rw [heq] at hCmod
    have hval := congrArg Units.val hCmod
    change (ZMod.castHom (show 4 ∣ 2 ^ (n + 2) * 2 from (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans (dvd_mul_right _ _)) (ZMod 4)) (-1 : ZMod (2 ^ (n + 2) * 2)) = 1 at hval
    rw [map_neg, map_one] at hval
    have hneq : (-1 : ZMod 4) ≠ 1 := by decide +kernel
    exact False.elim (hneq hval)

theorem cyclicTwo_scalar_projection_commute {Q : Type*} [Group Q] (n : ℕ)
    (projection : CyclicTwoAut n →* Q) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) (g : CyclicTwoAut n) :
    Commute (projection (cyclicTwoScalar n u)) (projection g) := by
  exact (cyclicTwoScalar_central n u g).map projection

theorem cyclicTwo_commutative_image {Q : Type*} [Group Q] (n : ℕ)
    (projection : CyclicTwoAut n →* Q)
    (hshears : Commute (projection (cyclicTwoTau n)) (projection (cyclicTwoRho n)))
    (hsurjective : Function.Surjective projection) : IsMulCommutative Q := by
  apply isMulCommutative_iff.mpr
  intro g h
  obtain ⟨g, rfl⟩ := hsurjective g
  obtain ⟨h, rfl⟩ := hsurjective h
  obtain ⟨v, w, u, rfl⟩ := cyclicTwoAut_normal_form n g
  obtain ⟨v', w', u', rfl⟩ := cyclicTwoAut_normal_form n h
  simp only [map_mul, map_pow]
  have hpairs : Commute
      (projection (cyclicTwoTau n) ^ v.val * projection (cyclicTwoRho n) ^ w.val)
      (projection (cyclicTwoTau n) ^ v'.val * projection (cyclicTwoRho n) ^ w'.val) :=
    (((Commute.refl (projection (cyclicTwoTau n))).pow_pow v.val v'.val).mul_right
      (hshears.pow_pow v.val w'.val)).mul_left
      ((hshears.symm.pow_pow w.val v'.val).mul_right
        ((Commute.refl (projection (cyclicTwoRho n))).pow_pow w.val w'.val))
  have hright := cyclicTwo_scalar_projection_commute n projection u'
    (cyclicTwoTau n ^ v.val * cyclicTwoRho n ^ w.val)
  simp only [map_mul, map_pow] at hright
  have hleft := cyclicTwo_scalar_projection_commute n projection u
    (cyclicTwoTau n ^ v'.val * cyclicTwoRho n ^ w'.val * cyclicTwoScalar n u')
  simp only [map_mul, map_pow] at hleft
  exact ((hpairs.mul_right hright.symm).mul_left hleft).eq

theorem cyclicTwoAut_commutator (n : ℕ) :
    commutator (CyclicTwoAut n) = Subgroup.zpowers (cyclicTwoDelta n) := by
  let D := Subgroup.zpowers (cyclicTwoDelta n)
  have hcentral : D ≤ Subgroup.center (CyclicTwoAut n) := by
    rw [← cyclicTwoAut_scalar_center]
    exact Subgroup.zpowers_le.mpr ⟨cyclicTwoTopUnit n, rfl⟩
  let : D.Normal := subgroup_normal_of_central D hcentral
  let projection := QuotientGroup.mk' D
  have hshears : Commute (projection (cyclicTwoTau n)) (projection (cyclicTwoRho n)) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement, cyclicTwoTauRho_commutator]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  have hcommutative := cyclicTwo_commutative_image n projection hshears (QuotientGroup.mk'_surjective D)
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommutative
  · apply Subgroup.zpowers_le.mpr
    rw [← cyclicTwoTauRho_commutator]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

instance cyclicTwoC_zpowers_normal (n : ℕ) : (Subgroup.zpowers (cyclicTwoC n)).Normal := by
  apply subgroup_normal_of_central
  rw [← cyclicTwoAut_scalar_center]
  exact Subgroup.zpowers_le.mpr ⟨cyclicTwoFive n, rfl⟩

theorem cyclicTwoAut_cyclic_scalar_quotient (n : ℕ) :
    IsMulCommutative (CyclicTwoAut n ⧸ Subgroup.zpowers (cyclicTwoC n)) ∧
      (∀ x : CyclicTwoAut n ⧸ Subgroup.zpowers (cyclicTwoC n), x ^ 2 = 1) ∧
      Nat.card (CyclicTwoAut n ⧸ Subgroup.zpowers (cyclicTwoC n)) = 8 := by
  let P := Subgroup.zpowers (cyclicTwoC n)
  let projection := QuotientGroup.mk' P
  have hderived : commutator (CyclicTwoAut n) ≤ P := by
    rw [cyclicTwoAut_commutator]
    apply Subgroup.zpowers_le.mpr
    rw [← cyclicTwoC_half_power]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hcommutative : IsMulCommutative (CyclicTwoAut n ⧸ P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hderived
  let : CommGroup (CyclicTwoAut n ⧸ P) := {
    (inferInstance : Group (CyclicTwoAut n ⧸ P)) with mul_comm := @mul_comm' _ _ hcommutative }
  have hexponent (x : CyclicTwoAut n ⧸ P) : x ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P x
    obtain ⟨v, w, u, rfl⟩ := cyclicTwoAut_normal_form n g
    obtain ⟨j, e, rfl⟩ := cyclicTwo_scalar_normal_form n u
    have hc : projection (cyclicTwoC n) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
    change projection _ ^ 2 = 1
    simp only [map_mul, map_pow, map_zpow]
    change (projection (cyclicTwoTau n) ^ v.val * projection (cyclicTwoRho n) ^ w.val *
      (projection (cyclicTwoC n) ^ j * projection (cyclicTwoZ n) ^ e.val)) ^ 2 = 1
    rw [hc, one_zpow, one_mul, mul_pow, mul_pow]
    have hτ : projection (cyclicTwoTau n) ^ 2 = 1 := by rw [← map_pow, cyclicTwoTau_square, map_one]
    have hρ : projection (cyclicTwoRho n) ^ 2 = 1 := by rw [← map_pow, cyclicTwoRho_square, map_one]
    have hz : projection (cyclicTwoZ n) ^ 2 = 1 := by rw [← map_pow, cyclicTwoZ_square, map_one]
    have hτv : (projection (cyclicTwoTau n) ^ v.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm v.val 2, pow_mul, hτ, one_pow]
    have hρw : (projection (cyclicTwoRho n) ^ w.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm w.val 2, pow_mul, hρ, one_pow]
    have hze : (projection (cyclicTwoZ n) ^ e.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm e.val 2, pow_mul, hz, one_pow]
    rw [hτv, hρw, hze, mul_one, mul_one]
  have hcard : Nat.card (CyclicTwoAut n ⧸ P) = 8 := by
    have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup P
    have hP : Nat.card P = 2 ^ (n + 1) := by rw [Nat.card_zpowers, cyclicTwoC_order]
    rw [cyclicTwoAut_card, hP] at hformula
    have hpower : 2 ^ (n + 4) = 8 * 2 ^ (n + 1) := by
      calc
        _ = 2 ^ ((n + 1) + 3) := by congr 1
        _ = 2 ^ (n + 1) * 2 ^ 3 := pow_add _ _ _
        _ = 8 * 2 ^ (n + 1) := by norm_num; exact Nat.mul_comm _ _
    have hpos : 0 < 2 ^ (n + 1) := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (hformula.symm.trans hpower)
  exact ⟨hcommutative, hexponent, hcard⟩

theorem cyclicTwoAut_center_quotient (n : ℕ) :
    IsMulCommutative (CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n)) ∧
      (∀ x : CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n), x ^ 2 = 1) ∧
      Nat.card (CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n)) = 4 ∧
      ∀ x : CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n),
        ∃ v w : ZMod 2, x =
          (QuotientGroup.mk' (Subgroup.center (CyclicTwoAut n))) (cyclicTwoTau n) ^ v.val *
          (QuotientGroup.mk' (Subgroup.center (CyclicTwoAut n))) (cyclicTwoRho n) ^ w.val := by
  let Z := Subgroup.center (CyclicTwoAut n)
  have hker : (cyclicTwoShearHom n).ker = Z :=
    (cyclicTwoShearHom_kernel n).trans (cyclicTwoAut_scalar_center n)
  let quotient := QuotientGroup.lift Z (cyclicTwoShearHom n) hker.symm.le
  have hsurjective : Function.Surjective quotient := by
    intro x
    obtain ⟨g, hg⟩ := cyclicTwoShearHom_surjective n x
    exact ⟨QuotientGroup.mk' Z g, hg⟩
  have hinjective : Function.Injective quotient := by
    apply (MonoidHom.ker_eq_bot_iff quotient).mp
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
    apply Subgroup.mem_bot.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hker.le
    exact hx
  have hcommutative : IsMulCommutative (CyclicTwoAut n ⧸ Z) := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply hinjective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hexponent (x : CyclicTwoAut n ⧸ Z) : x ^ 2 = 1 := by
    apply hinjective
    rw [map_pow, map_one]
    have h : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1 := by decide +kernel
    exact h _
  have hcard : Nat.card (CyclicTwoAut n ⧸ Z) = 4 := by
    rw [Nat.card_eq_of_bijective quotient ⟨hinjective, hsurjective⟩, Nat.card_eq_fintype_card]
    decide +kernel
  refine ⟨hcommutative, hexponent, hcard, ?_⟩
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
  obtain ⟨v, w, u, rfl⟩ := cyclicTwoAut_normal_form n g
  refine ⟨v, w, ?_⟩
  simp only [map_mul, map_pow]
  have hu : (QuotientGroup.mk' Z) (cyclicTwoScalar n u) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((cyclicTwoAut_scalar_center n).le ⟨u, rfl⟩)
  rw [hu, mul_one]

theorem cyclicTwoTau_apply (n : ℕ) (x : CyclicTwoSpace n) :
    (cyclicTwoTau n).val x = (x.1 + scaledCyclicInclusion (2 ^ (n + 2)) 2 x.2, x.2) := by
  rw [cyclicPairEnd_apply, cyclicTwoTau_coefficients]
  simp

theorem cyclicTwoRho_apply (n : ℕ) (x : CyclicTwoSpace n) :
    (cyclicTwoRho n).val x = (x.1, cyclicReduction (2 ^ (n + 2)) 2 x.1 + x.2) := by
  rw [cyclicPairEnd_apply, cyclicTwoRho_coefficients]
  simp

theorem cyclicTwoScalar_apply (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ) (x : CyclicTwoSpace n) :
    (cyclicTwoScalar n u).val x = (u.val * x.1, x.2) := by
  rw [cyclicPairEnd_apply, cyclicTwoScalar_coefficients]
  simp

theorem cyclicTwoDelta_apply (n : ℕ) (x : CyclicTwoSpace n) :
    (cyclicTwoDelta n).val x = (1 + 2 ^ (n + 2) : ℕ) • x := by
  rw [cyclicTwoDelta, cyclicTwoScalar_apply, cyclicTwoTopUnit_val]
  apply Prod.ext
  · change (1 + (2 ^ (n + 2) : ℕ)) * x.1 = (1 + 2 ^ (n + 2) : ℕ) • x.1
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  · change x.2 = (1 + 2 ^ (n + 2) : ℕ) • x.2
    rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_pow_self 2 (by omega)), add_zero, one_mul]

theorem rank_two_cyclic_times_two_automorphism_structure (n : ℕ) :
    cyclicTwoTau n ^ 2 = 1 ∧ cyclicTwoRho n ^ 2 = 1 ∧ cyclicTwoZ n ^ 2 = 1 ∧
      orderOf (cyclicTwoC n) = 2 ^ (n + 1) ∧
      cyclicTwoC n ^ (2 ^ n) = cyclicTwoDelta n ∧
      Subgroup.center (CyclicTwoAut n) =
        Subgroup.zpowers (cyclicTwoC n) ⊔ Subgroup.zpowers (cyclicTwoZ n) ∧
      Disjoint (Subgroup.zpowers (cyclicTwoC n)) (Subgroup.zpowers (cyclicTwoZ n)) ∧
      Subgroup.closure ({cyclicTwoTau n, cyclicTwoRho n, cyclicTwoC n, cyclicTwoZ n} : Set (CyclicTwoAut n)) = ⊤ ∧
      Nat.card (CyclicTwoAut n) = 2 ^ (n + 4) ∧
      IsMulCommutative (CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n)) ∧
      Nat.card (CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n)) = 4 ∧
      (∀ x : CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n), x ^ 2 = 1) ∧
      (∀ x : CyclicTwoAut n ⧸ Subgroup.center (CyclicTwoAut n), ∃ v w : ZMod 2, x =
        (QuotientGroup.mk' (Subgroup.center (CyclicTwoAut n))) (cyclicTwoTau n) ^ v.val *
        (QuotientGroup.mk' (Subgroup.center (CyclicTwoAut n))) (cyclicTwoRho n) ^ w.val) ∧
      commutator (CyclicTwoAut n) = Subgroup.zpowers (cyclicTwoDelta n) ∧
      ⁅cyclicTwoTau n, cyclicTwoRho n⁆ = cyclicTwoDelta n ∧
      IsMulCommutative (CyclicTwoAut n ⧸ Subgroup.zpowers (cyclicTwoC n)) ∧
      (∀ x : CyclicTwoAut n ⧸ Subgroup.zpowers (cyclicTwoC n), x ^ 2 = 1) ∧
      Nat.card (CyclicTwoAut n ⧸ Subgroup.zpowers (cyclicTwoC n)) = 8 := by
  obtain ⟨hcenterComm, hcenterExponent, hcenterCard, hcenterBasis⟩ := cyclicTwoAut_center_quotient n
  obtain ⟨hquotientComm, hquotientExponent, hquotientCard⟩ := cyclicTwoAut_cyclic_scalar_quotient n
  exact ⟨cyclicTwoTau_square n, cyclicTwoRho_square n, cyclicTwoZ_square n, cyclicTwoC_order n,
    cyclicTwoC_half_power n, cyclicTwoAut_center_generators n, cyclicTwoAut_center_disjoint n,
    cyclicTwoAut_generators n, cyclicTwoAut_card n, hcenterComm, hcenterCard, hcenterExponent, hcenterBasis,
    cyclicTwoAut_commutator n, cyclicTwoTauRho_commutator n, hquotientComm, hquotientExponent, hquotientCard⟩

end CFSG.LargeEvenClassification.Helpers
