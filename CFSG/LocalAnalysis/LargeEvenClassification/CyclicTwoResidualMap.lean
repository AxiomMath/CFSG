module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoAction
public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoEndCoordinates
public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryResidualRing

public section

namespace CFSG.LargeEvenClassification.Helpers

section Residue

variable (scale : ℕ) [NeZero scale] [NeZero (scale * 2)] (heven : 2 ∣ scale)

@[expose] def cyclicTwoCoefficientResidue (coefficients : CyclicPairCoefficients scale 2) : BinaryResidualRing :=
  ((cyclicReduction scale 2 coefficients.1.1, coefficients.1.2), (coefficients.2.1, coefficients.2.2))

omit [NeZero scale] [NeZero (scale * 2)] in
theorem cyclicTwoCoefficientResidue_add (first second : CyclicPairCoefficients scale 2) :
    cyclicTwoCoefficientResidue scale (first + second) =
      cyclicTwoCoefficientResidue scale first + cyclicTwoCoefficientResidue scale second := by
  change cyclicTwoCoefficientResidue scale (first + second) = binaryResidualAddition _ _
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [cyclicTwoCoefficientResidue, binaryResidualAddition, Prod.fst_add, Prod.snd_add, map_add]

include heven in
omit [NeZero scale] [NeZero (scale * 2)] in
theorem cyclicTwoCoefficientResidue_product (first second : CyclicPairCoefficients scale 2) :
    cyclicTwoCoefficientResidue scale (cyclicPairCoefficientProduct scale 2 first second) =
      cyclicTwoCoefficientResidue scale first * cyclicTwoCoefficientResidue scale second := by
  have hscaleZero : (scale : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr heven
  change cyclicTwoCoefficientResidue scale (cyclicPairCoefficientProduct scale 2 first second) =
    binaryResidualMultiply _ _
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [cyclicTwoCoefficientResidue, cyclicPairCoefficientProduct, binaryResidualMultiply,
      map_add, map_mul, cyclicReduction_inclusion, hscaleZero, zero_mul, add_zero, zero_add]

@[expose] noncomputable def cyclicTwoEndResidualHom : AddMonoid.End (CyclicPair scale 2) →+* BinaryResidualRing where
  toFun := fun operator => cyclicTwoCoefficientResidue scale (cyclicPairEndCoefficients scale 2 operator)
  map_zero' := by
    rw [cyclicPairEndCoefficients_zero]
    change ((_, _), (_, _)) = ((0, 0), (0, 0))
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
  map_one' := by
    rw [cyclicPairEndCoefficients_one]
    change ((cyclicReduction scale 2 1, 0), (0, 1)) = ((1, 0), (0, 1))
    rw [map_one]
  map_add' := by
    intro first second
    rw [cyclicPairEndCoefficients_add, cyclicTwoCoefficientResidue_add]
  map_mul' := by
    intro first second
    rw [cyclicPairEndCoefficients_mul, cyclicTwoCoefficientResidue_product scale heven]

@[expose] noncomputable def cyclicTwoResidualUnits :
    (AddMonoid.End (CyclicPair scale 2))ˣ →* BinaryResidualRingˣ :=
  Units.map (cyclicTwoEndResidualHom scale heven).toMonoidHom

universe actingUniverse

variable {Acting : Type actingUniverse} [Group Acting]
variable (embedding : Acting →* (AddMonoid.End (CyclicPair scale 2))ˣ)

@[expose] noncomputable def cyclicTwoActionResidue : Acting →* BinaryResidualRingˣ :=
  (cyclicTwoResidualUnits scale heven).comp embedding

theorem cyclicTwoActionKernel_coefficients (element : (cyclicTwoActionResidue scale heven embedding).ker) :
    (cyclicPairEndCoefficients scale 2 (embedding element.val).val).1.2 = 0 ∧
      (cyclicPairEndCoefficients scale 2 (embedding element.val).val).2.1 = 0 ∧
      (cyclicPairEndCoefficients scale 2 (embedding element.val).val).2.2 = 1 := by
  have heq := congrArg Units.val element.property
  change cyclicTwoCoefficientResidue scale (cyclicPairEndCoefficients scale 2 (embedding element.val).val) =
    ((1, 0), (0, 1)) at heq
  exact ⟨congrArg (fun entry : BinaryResidualRing => entry.1.2) heq,
    congrArg (fun entry : BinaryResidualRing => entry.2.1) heq,
    congrArg (fun entry : BinaryResidualRing => entry.2.2) heq⟩

@[expose] noncomputable def cyclicTwoActionKernelScalar :
    (cyclicTwoActionResidue scale heven embedding).ker →* ZMod (scale * 2) where
  toFun := fun element => (cyclicPairEndCoefficients scale 2 (embedding element.val).val).1.1
  map_one' := by
    rw [show embedding ((1 : (cyclicTwoActionResidue scale heven embedding).ker) : Acting) = 1 from map_one embedding]
    change (cyclicPairEndCoefficients scale 2 1).1.1 = 1
    rw [cyclicPairEndCoefficients_one]
  map_mul' := by
    intro first second
    change (cyclicPairEndCoefficients scale 2 (embedding (first.val * second.val)).val).1.1 = _
    rw [map_mul]
    change (cyclicPairEndCoefficients scale 2 ((embedding first.val).val * (embedding second.val).val)).1.1 = _
    rw [cyclicPairEndCoefficients_mul]
    change _ * _ + scaledCyclicInclusion scale 2
      ((cyclicPairEndCoefficients scale 2 (embedding first.val).val).1.2 * _) = _
    rw [(cyclicTwoActionKernel_coefficients scale heven embedding first).1, zero_mul, map_zero, add_zero]

include embedding in
theorem cyclicTwoActionKernelScalar_injective (hinjective : Function.Injective embedding) :
    Function.Injective (cyclicTwoActionKernelScalar scale heven embedding).toHomUnits := by
  intro first second heq
  apply Subtype.ext
  apply hinjective
  apply Units.ext
  apply cyclicPairEndCoefficients_injective scale 2
  apply Prod.ext <;> apply Prod.ext
  · exact congrArg Units.val heq
  · exact (cyclicTwoActionKernel_coefficients scale heven embedding first).1.trans
      (cyclicTwoActionKernel_coefficients scale heven embedding second).1.symm
  · exact (cyclicTwoActionKernel_coefficients scale heven embedding first).2.1.trans
      (cyclicTwoActionKernel_coefficients scale heven embedding second).2.1.symm
  · exact (cyclicTwoActionKernel_coefficients scale heven embedding first).2.2.trans
      (cyclicTwoActionKernel_coefficients scale heven embedding second).2.2.symm

theorem two_group_card_le_four_rank {Small : Type*} [Group Small] [Finite Small]
    (hcard : Nat.card Small ≤ 4) : pGeneratorRank 2 Small ≤ 2 := by
  have hquotientCard := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini Small))
    (QuotientGroup.mk'_surjective (frattini Small))
  unfold pGeneratorRank
  exact (Nat.log_mono_right (hquotientCard.trans hcard)).trans (by decide)

include heven embedding in
theorem cyclicTwoAction_four_generator_rank [Finite Acting] (hpgroup : IsPGroup 2 Acting)
    (hinjective : Function.Injective embedding) (exponent : ℕ) (hscale : scale * 2 = 2 ^ exponent) :
    pGeneratorRank 2 Acting ≤ 4 := by
  let residual := cyclicTwoActionResidue scale heven embedding
  let Kernel := residual.ker
  have hkernelInjective := cyclicTwoActionKernelScalar_injective scale heven embedding hinjective
  let scalar := (cyclicTwoActionKernelScalar scale heven embedding).toHomUnits
  let transported := (Units.map (ZMod.ringEquivCongr hscale).toMonoidHom).comp scalar
  have htransported : Function.Injective transported := by
    intro first second heq
    apply hkernelInjective
    apply Units.ext
    apply (ZMod.ringEquivCongr hscale).injective
    exact congrArg Units.val heq
  have hkernelRank : pGeneratorRank 2 Kernel ≤ 2 :=
    two_group_embedding_binary_units_rank exponent transported htransported
  have himageCard : Nat.card residual.range ≤ 4 :=
    (Nat.card_le_card_of_injective residual.range.subtype Subtype.val_injective).trans
      binaryResidualUnit_card_le
  have himageRank := two_group_card_le_four_rank himageCard
  have hquotientRank : pGeneratorRank 2 (Acting ⧸ Kernel) = pGeneratorRank 2 residual.range :=
    pGeneratorRank_mulEquiv Nat.prime_two (hpgroup.to_quotient Kernel)
      (QuotientGroup.quotientKerEquivRange residual)
  have hextension := pGeneratorRank_extension_le Nat.prime_two hpgroup Kernel
  rw [hquotientRank] at hextension
  omega

end Residue

end CFSG.LargeEvenClassification.Helpers
