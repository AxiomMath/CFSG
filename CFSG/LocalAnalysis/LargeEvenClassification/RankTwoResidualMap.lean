module

public import CFSG.LocalAnalysis.LargeEvenClassification.PrincipalCongruence
public import CFSG.LocalAnalysis.LargeEvenClassification.ResidualRing
public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoEndCoordinates

public section

namespace CFSG.LargeEvenClassification.Helpers

section Residues

variable (scale modulus : ℕ) [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)]
variable (hfour : 4 ∣ modulus)

@[expose] def cyclicPairSmallReduction : ZMod modulus →+* ZMod 4 := ZMod.castHom hfour (ZMod 4)

@[expose] def cyclicPairLargeReduction : ZMod (scale * modulus) →+* ZMod 4 :=
  ZMod.castHom (hfour.trans (dvd_mul_left modulus scale)) (ZMod 4)

omit [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)] in
theorem cyclicPairLargeReduction_factor (element : ZMod (scale * modulus)) :
    cyclicPairSmallReduction modulus hfour (cyclicReduction scale modulus element) =
      cyclicPairLargeReduction scale modulus hfour element := by
  have hmaps := RingHom.ext_zmod
    ((cyclicPairSmallReduction modulus hfour).comp (cyclicReduction scale modulus))
    (cyclicPairLargeReduction scale modulus hfour)
  exact DFunLike.congr_fun hmaps element

omit [NeZero scale] [NeZero (scale * modulus)] in
theorem cyclicPairLargeReduction_inclusion (element : ZMod modulus) :
    cyclicPairLargeReduction scale modulus hfour (scaledCyclicInclusion scale modulus element) =
      (scale : ZMod 4) * cyclicPairSmallReduction modulus hfour element := by
  rw [scaledCyclicInclusion_apply, map_mul, map_natCast, map_natCast]
  congr 1
  exact ((congrArg (cyclicPairSmallReduction modulus hfour)
    (ZMod.natCast_zmod_val element).symm).trans (map_natCast _ _)).symm

@[expose] def cyclicPairCoefficientResidue (coefficients : CyclicPairCoefficients scale modulus) :
    ResidualRing (scale : ZMod 4) :=
  ((cyclicPairLargeReduction scale modulus hfour coefficients.1.1,
    cyclicPairSmallReduction modulus hfour coefficients.1.2),
    (cyclicPairSmallReduction modulus hfour coefficients.2.1,
      cyclicPairSmallReduction modulus hfour coefficients.2.2))

omit [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)] in
theorem cyclicPairCoefficientResidue_add (first second : CyclicPairCoefficients scale modulus) :
    cyclicPairCoefficientResidue scale modulus hfour (first + second) =
      cyclicPairCoefficientResidue scale modulus hfour first +
        cyclicPairCoefficientResidue scale modulus hfour second := by
  change cyclicPairCoefficientResidue scale modulus hfour (first + second) =
    residualAdd _ _
  apply Prod.ext <;> apply Prod.ext <;> simp only [cyclicPairCoefficientResidue,
    residualAdd, Prod.fst_add, Prod.snd_add, map_add]

omit [NeZero scale] [NeZero (scale * modulus)] in
theorem cyclicPairCoefficientResidue_product (first second : CyclicPairCoefficients scale modulus) :
    cyclicPairCoefficientResidue scale modulus hfour (cyclicPairCoefficientProduct scale modulus first second) =
      cyclicPairCoefficientResidue scale modulus hfour first *
        cyclicPairCoefficientResidue scale modulus hfour second := by
  change cyclicPairCoefficientResidue scale modulus hfour (cyclicPairCoefficientProduct scale modulus first second) =
    residualMultiply _ _ _
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [cyclicPairCoefficientResidue, cyclicPairCoefficientProduct, residualMultiply,
      map_add, map_mul, map_natCast, cyclicPairLargeReduction_inclusion,
      cyclicPairLargeReduction_factor, mul_assoc]

@[expose] noncomputable def cyclicPairEndResidualHom :
    AddMonoid.End (CyclicPair scale modulus) →+* ResidualRing (scale : ZMod 4) where
  toFun := fun operator => cyclicPairCoefficientResidue scale modulus hfour
    (cyclicPairEndCoefficients scale modulus operator)
  map_zero' := by
    rw [cyclicPairEndCoefficients_zero]
    change ((_, _), (_, _)) = ((0, 0), (0, 0))
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
  map_one' := by
    rw [cyclicPairEndCoefficients_one]
    change ((_, _), (_, _)) = ((1, 0), (0, 1))
    simp only [map_zero, map_one]
  map_add' := by
    intro first second
    rw [cyclicPairEndCoefficients_add, cyclicPairCoefficientResidue_add]
  map_mul' := by
    intro first second
    rw [cyclicPairEndCoefficients_mul, cyclicPairCoefficientResidue_product]

omit [NeZero scale] [NeZero (scale * modulus)] in
theorem zmod_four_reduction_zero (element : ZMod modulus) :
    cyclicPairSmallReduction modulus hfour element = 0 ↔
      ∃ source : ZMod modulus, element = 4 • source := by
  constructor
  · intro hzero
    have hcast : (element.val : ZMod 4) = 0 := by
      calc
        _ = cyclicPairSmallReduction modulus hfour (element.val : ZMod modulus) :=
          (map_natCast _ _).symm
        _ = 0 := by rw [ZMod.natCast_zmod_val, hzero]
    have hdivides : 4 ∣ element.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    refine ⟨(element.val / 4 : ℕ), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdivides,
      ZMod.natCast_zmod_val]
  · rintro ⟨source, rfl⟩
    rw [map_nsmul, nsmul_eq_mul]
    have hfourZero : (4 : ZMod 4) = 0 := by decide
    rw [Nat.cast_ofNat, hfourZero, zero_mul]

theorem cyclicPairEndResidualHom_zero (operator : AddMonoid.End (CyclicPair scale modulus)) :
    cyclicPairEndResidualHom scale modulus hfour operator = 0 ↔
      ∃ source : AddMonoid.End (CyclicPair scale modulus), operator = 4 • source := by
  constructor
  · intro hzero
    let coefficients := cyclicPairEndCoefficients scale modulus operator
    have hcoordinates : cyclicPairCoefficientResidue scale modulus hfour coefficients = ((0, 0), (0, 0)) :=
      hzero
    have hfirstA : cyclicPairLargeReduction scale modulus hfour coefficients.1.1 = 0 :=
      congrArg (fun entry : ResidualRing (scale : ZMod 4) => entry.1.1) hcoordinates
    have hfirstB : cyclicPairSmallReduction modulus hfour coefficients.1.2 = 0 :=
      congrArg (fun entry : ResidualRing (scale : ZMod 4) => entry.1.2) hcoordinates
    have hsecondC : cyclicPairSmallReduction modulus hfour coefficients.2.1 = 0 :=
      congrArg (fun entry : ResidualRing (scale : ZMod 4) => entry.2.1) hcoordinates
    have hsecondD : cyclicPairSmallReduction modulus hfour coefficients.2.2 = 0 :=
      congrArg (fun entry : ResidualRing (scale : ZMod 4) => entry.2.2) hcoordinates
    have hfirstReduction : cyclicPairSmallReduction (scale * modulus)
        (hfour.trans (dvd_mul_left modulus scale)) coefficients.1.1 = 0 := hfirstA
    obtain ⟨rootA, hrootA⟩ := (zmod_four_reduction_zero (scale * modulus)
      (hfour.trans (dvd_mul_left modulus scale)) coefficients.1.1).mp hfirstReduction
    obtain ⟨rootB, hrootB⟩ := (zmod_four_reduction_zero modulus hfour coefficients.1.2).mp hfirstB
    obtain ⟨rootC, hrootC⟩ := (zmod_four_reduction_zero modulus hfour coefficients.2.1).mp hsecondC
    obtain ⟨rootD, hrootD⟩ := (zmod_four_reduction_zero modulus hfour coefficients.2.2).mp hsecondD
    refine ⟨cyclicPairEndFromCoefficients scale modulus ((rootA, rootB), (rootC, rootD)), ?_⟩
    apply cyclicPairEndCoefficients_injective scale modulus
    rw [cyclicPairEndCoefficients_nsmul, cyclicPairEndCoefficients_from]
    change coefficients = 4 • ((rootA, rootB), (rootC, rootD))
    apply Prod.ext <;> apply Prod.ext
    · exact hrootA
    · exact hrootB
    · exact hrootC
    · exact hrootD
  · rintro ⟨source, rfl⟩
    rw [map_nsmul, nsmul_eq_mul]
    have hfourZero : (4 : ResidualRing (scale : ZMod 4)) = 0 := by
      change ((4, 0), (0, 4)) = ((0, 0), (0, 0))
      decide
    rw [Nat.cast_ofNat, hfourZero, zero_mul]

@[expose] noncomputable def cyclicPairResidualUnits :
    (AddMonoid.End (CyclicPair scale modulus))ˣ →* (ResidualRing (scale : ZMod 4))ˣ :=
  Units.map (cyclicPairEndResidualHom scale modulus hfour).toMonoidHom

theorem cyclicPairResidualUnits_kernel (unit : (AddMonoid.End (CyclicPair scale modulus))ˣ) :
    cyclicPairResidualUnits scale modulus hfour unit = 1 ↔
      unit ∈ principalFourSubgroup (AddMonoid.End (CyclicPair scale modulus)) := by
  have hval : cyclicPairResidualUnits scale modulus hfour unit = 1 ↔
      cyclicPairEndResidualHom scale modulus hfour unit.val = 1 := by
    constructor
    · exact fun heq => congrArg Units.val heq
    · intro heq
      exact Units.ext heq
  rw [hval]
  constructor
  · intro hone
    have hzero : cyclicPairEndResidualHom scale modulus hfour (unit.val - 1) = 0 := by
      rw [map_sub, map_one, hone, sub_self]
    obtain ⟨source, hsource⟩ := (cyclicPairEndResidualHom_zero scale modulus hfour _).mp hzero
    change ∃ source, unit.val = 1 + 4 * source
    refine ⟨source, ?_⟩
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hsource
    exact (sub_eq_iff_eq_add.mp hsource).trans (add_comm _ _)
  · rintro ⟨source, hsource⟩
    have hzero : cyclicPairEndResidualHom scale modulus hfour (4 • source) = 0 :=
      (cyclicPairEndResidualHom_zero scale modulus hfour _).mpr ⟨source, rfl⟩
    rw [hsource, map_add, map_one]
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hzero
    rw [hzero, add_zero]

end Residues

end CFSG.LargeEvenClassification.Helpers
