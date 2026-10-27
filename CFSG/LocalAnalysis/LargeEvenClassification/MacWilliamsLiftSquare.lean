module

public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryCoordinateRoots

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

section NormalQuotient

variable {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
variable (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
variable (hcommutative : IsMulCommutative Normal)

include hpgroup in
theorem normal_frattini_projection_kernel :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)).comp Normal.subtype).ker =
      frattini Normal := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
    normalPowerSubgroup_eq_frattini_image Nat.prime_two hpgroup,
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]

noncomputable def normalFrattiniEmbedding :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    (Normal ⧸ frattini Normal) →*
      (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2) := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  exact QuotientGroup.lift (frattini Normal)
    ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)).comp Normal.subtype)
    (normal_frattini_projection_kernel hpgroup Normal hcommutative).symm.le

theorem normalFrattiniEmbedding_apply (element : Normal) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    normalFrattiniEmbedding hpgroup Normal hcommutative
      ((QuotientGroup.mk' (frattini Normal)) element) =
        (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (element : Ambient) := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  rfl

theorem normalFrattiniEmbedding_injective :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    Function.Injective (normalFrattiniEmbedding hpgroup Normal hcommutative) := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  unfold normalFrattiniEmbedding
  exact (QuotientGroup.injective_lift_iff _ _
    (normal_frattini_projection_kernel hpgroup Normal hcommutative).symm.le).mpr
    (normal_frattini_projection_kernel hpgroup Normal hcommutative).symm

noncomputable def normalFrattiniEquivImage :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    (Normal ⧸ frattini Normal) ≃*
      Normal.map (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  let projection := QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)
  have hkernel : frattini Normal = (projection.subgroupMap Normal).ker := by
    rw [← normal_frattini_projection_kernel hpgroup Normal hcommutative]
    ext element
    change projection element = 1 ↔ projection.subgroupMap Normal element = 1
    constructor
    · exact fun heq => Subtype.ext heq
    · exact fun heq => congrArg Subtype.val heq
  exact QuotientGroup.liftEquiv _ (projection.subgroupMap_surjective Normal) hkernel

theorem normalFrattiniEquivImage_embedding (coset : Normal ⧸ frattini Normal) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    (normalFrattiniEquivImage hpgroup Normal hcommutative coset :
      Ambient ⧸ normalPowerSubgroup Normal hcommutative 2) =
        normalFrattiniEmbedding hpgroup Normal hcommutative coset := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (frattini Normal) coset
  rw [normalFrattiniEmbedding_apply]
  rfl

end NormalQuotient

section Conjugation

variable {Ambient : Type groupUniverse} [Group Ambient]
variable (Normal : Subgroup Ambient) [Normal.Normal]

@[expose] def normalFrattiniConjugation : Ambient →* MulAut (Normal ⧸ frattini Normal) where
  toFun := fun conjugator => QuotientGroup.congr (frattini Normal) (frattini Normal)
    (MulAut.conjNormal (H := Normal) conjugator)
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : (frattini Normal).Characteristic) _)
  map_one' := by
    apply MulEquiv.ext
    intro coset
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (frattini Normal) coset
    change (QuotientGroup.mk' (frattini Normal)) (MulAut.conjNormal (H := Normal) 1 element) =
      (QuotientGroup.mk' (frattini Normal)) element
    rw [map_one]
    rfl
  map_mul' := by
    intro first second
    apply MulEquiv.ext
    intro coset
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (frattini Normal) coset
    change (QuotientGroup.mk' (frattini Normal))
      (MulAut.conjNormal (H := Normal) (first * second) element) =
        (QuotientGroup.mk' (frattini Normal))
          (MulAut.conjNormal (H := Normal) first (MulAut.conjNormal (H := Normal) second element))
    rw [map_mul]
    rfl

theorem normalFrattiniConjugation_apply (conjugator : Ambient) (element : Normal) :
    normalFrattiniConjugation Normal conjugator ((QuotientGroup.mk' (frattini Normal)) element) =
      (QuotientGroup.mk' (frattini Normal)) (MulAut.conjNormal (H := Normal) conjugator element) := rfl

end Conjugation

section QuotientConjugation

variable {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
variable (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
variable (hcommutative : IsMulCommutative Normal)

theorem normalFrattiniEmbedding_conjugation (conjugator : Ambient)
    (coset : Normal ⧸ frattini Normal) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    normalFrattiniEmbedding hpgroup Normal hcommutative
      (normalFrattiniConjugation Normal conjugator coset) =
        (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) conjugator *
          normalFrattiniEmbedding hpgroup Normal hcommutative coset *
            ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) conjugator)⁻¹ := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (frattini Normal) coset
  rw [normalFrattiniConjugation_apply, normalFrattiniEmbedding_apply,
    normalFrattiniEmbedding_apply, MulAut.conjNormal_apply, map_mul, map_mul, map_inv]

end QuotientConjugation

section LiftSquare

variable {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
variable (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
variable (hcommutative : IsMulCommutative Normal)
variable (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)

include hselfCentralizing in
omit [Finite Ambient] in
theorem conjugation_involution_lift_square_mem (lift : Ambient)
    (hinvolution : MulAut.conjNormal (H := Normal) lift ^ 2 = 1) : lift ^ 2 ∈ Normal := by
  have hkernel : (MulAut.conjNormal (H := Normal)).ker = Normal :=
    (conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing
  apply hkernel.le
  change MulAut.conjNormal (H := Normal) (lift ^ 2) = 1
  rw [map_pow, hinvolution]

include hselfCentralizing in
theorem conjugation_square_map_in_normal_frattini
    (Involutions : Subgroup (MulAut Normal))
    (helementary : CFSG.Open.IsElemAbelian 2 Involutions)
    (hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal)) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ∀ squareMap : Involutions →* (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2),
      Function.Injective squareMap →
      (∀ lift : Ambient, ∀ automorphism : Involutions,
        MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
          squareMap automorphism =
            (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (lift ^ 2)) →
      ∃ normalSquareMap : Involutions →* (Normal ⧸ frattini Normal),
        Function.Injective normalSquareMap ∧
        (∀ automorphism : Involutions,
          normalFrattiniEmbedding hpgroup Normal hcommutative (normalSquareMap automorphism) =
            squareMap automorphism) ∧
        ∀ lift : Ambient, ∀ automorphism : Involutions,
          MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
            ∃ square : Normal, (square : Ambient) = lift ^ 2 ∧
              normalSquareMap automorphism = (QuotientGroup.mk' (frattini Normal)) square := by
  dsimp only
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  let projection := QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)
  intro squareMap hinjective hsquares
  have himage : ∀ automorphism : Involutions, squareMap automorphism ∈ Normal.map projection := by
    intro automorphism
    obtain ⟨lift, hlift⟩ := hlifts automorphism
    rw [hsquares lift automorphism hlift]
    exact Subgroup.mem_map.mpr ⟨lift ^ 2,
      conjugation_involution_lift_square_mem Normal hselfCentralizing lift
        (by rw [hlift]; exact helementary.2 automorphism automorphism.property), rfl⟩
  let imageMap := squareMap.codRestrict (Normal.map projection) himage
  let equivalence := normalFrattiniEquivImage hpgroup Normal hcommutative
  let normalSquareMap := equivalence.symm.toMonoidHom.comp imageMap
  have hembedding : ∀ automorphism : Involutions,
      normalFrattiniEmbedding hpgroup Normal hcommutative (normalSquareMap automorphism) =
        squareMap automorphism := by
    intro automorphism
    rw [← normalFrattiniEquivImage_embedding]
    change (equivalence (equivalence.symm (imageMap automorphism)) :
      Ambient ⧸ normalPowerSubgroup Normal hcommutative 2) = squareMap automorphism
    rw [equivalence.apply_symm_apply]
    rfl
  refine ⟨normalSquareMap, ?_, hembedding, ?_⟩
  · intro first second heq
    apply hinjective
    rw [← hembedding first, ← hembedding second, heq]
  · intro lift automorphism hlift
    let square : Normal := ⟨lift ^ 2,
      conjugation_involution_lift_square_mem Normal hselfCentralizing lift
        (by rw [hlift]; exact helementary.2 automorphism automorphism.property)⟩
    refine ⟨square, rfl, ?_⟩
    apply normalFrattiniEmbedding_injective hpgroup Normal hcommutative
    rw [hembedding, normalFrattiniEmbedding_apply, hsquares lift automorphism hlift]

omit [Finite Ambient] in
theorem normal_frattini_lift_square_equivariant
    (Involutions : Subgroup (MulAut Normal))
    (hstable : ∀ conjugator : Ambient, ∀ automorphism : MulAut Normal,
      automorphism ∈ Involutions →
        MulAut.conjNormal (H := Normal) conjugator * automorphism *
          (MulAut.conjNormal (H := Normal) conjugator)⁻¹ ∈ Involutions)
    (hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal))
    (normalSquareMap : Involutions →* (Normal ⧸ frattini Normal))
    (hsquares : ∀ lift : Ambient, ∀ automorphism : Involutions,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
        ∃ square : Normal, (square : Ambient) = lift ^ 2 ∧
          normalSquareMap automorphism = (QuotientGroup.mk' (frattini Normal)) square)
    (conjugator : Ambient) (automorphism : Involutions) :
    normalSquareMap
      (invariantSubgroupConjugation (MulAut.conjNormal (H := Normal)) Involutions hstable
        conjugator automorphism) =
      normalFrattiniConjugation Normal conjugator (normalSquareMap automorphism) := by
  obtain ⟨lift, hlift⟩ := hlifts automorphism
  have hconjugateLift : MulAut.conjNormal (H := Normal) (conjugator * lift * conjugator⁻¹) =
      (invariantSubgroupConjugation (MulAut.conjNormal (H := Normal)) Involutions hstable
        conjugator automorphism : MulAut Normal) := by
    rw [map_mul, map_mul, map_inv, hlift]
    rfl
  obtain ⟨square, hsquare, hcoset⟩ := hsquares lift automorphism hlift
  obtain ⟨conjugateSquare, hconjugateSquare, hconjugateCoset⟩ :=
    hsquares (conjugator * lift * conjugator⁻¹) _ hconjugateLift
  rw [hcoset, hconjugateCoset, normalFrattiniConjugation_apply]
  congr 1
  apply Subtype.ext
  rw [hconjugateSquare, MulAut.conjNormal_apply, hsquare]
  simp only [pow_two]
  group

end LiftSquare

section DeepDifference

variable {Abelian : Type groupUniverse} [CommGroup Abelian] [Finite Abelian]
variable (hpgroup : IsPGroup 2 Abelian)

include hpgroup in
theorem deep_involution_difference_square_one (automorphism : MulAut Abelian)
    (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (hinvolution : automorphism ^ 2 = 1) (element : Abelian) :
    (automorphism element * element⁻¹) ^ 2 = 1 := by
  obtain ⟨exponent, hcharacteristic⟩ := pGroup_addEnd_binary_characteristic hpgroup
  let unit := abelianAutomorphismUnits Abelian automorphism
  have hsquare : unit.val ^ 2 = 1 := by
    have heq := congrArg Units.val (show unit ^ 2 = 1 from by
      dsimp [unit]
      rw [← map_pow, hinvolution, map_one])
    exact heq
  have hdouble := (principal_square_eq_iff_double_sub hcharacteristic unit.val 1 hdeep
    ⟨0, by simp⟩).mp hsquare
  have helement := congrArg (fun operator : AddMonoid.End (Additive Abelian) =>
    operator (Additive.ofMul element)) hdouble
  change 2 • (Additive.ofMul (automorphism element) - Additive.ofMul element) = 0 at helement
  have hresult := congrArg Additive.toMul helement
  simpa only [toMul_nsmul, toMul_sub, toMul_ofMul, toMul_zero, div_eq_mul_inv] using hresult

include hpgroup in
theorem deep_involution_fixes_squares (automorphism : MulAut Abelian)
    (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (hinvolution : automorphism ^ 2 = 1) (element : Abelian) :
    automorphism (element ^ 2) = element ^ 2 := by
  have hzero := deep_involution_difference_square_one hpgroup automorphism hdeep hinvolution element
  rw [mul_pow, inv_pow, mul_inv_eq_one] at hzero
  rw [map_pow, hzero]

end DeepDifference

section DifferenceHom

variable {Abelian : Type groupUniverse} [CommGroup Abelian] [Finite Abelian]
variable (hpgroup : IsPGroup 2 Abelian)

@[expose] def abelianAutomorphismDifference (automorphism : MulAut Abelian) : Abelian →* Abelian where
  toFun := fun element => automorphism element * element⁻¹
  map_one' := by simp
  map_mul' := by
    intro first second
    rw [map_mul, mul_inv]
    ac_rfl

include hpgroup in
theorem deep_involution_difference_kills_frattini (automorphism : MulAut Abelian)
    (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (hinvolution : automorphism ^ 2 = 1) :
    frattini Abelian ≤ (abelianAutomorphismDifference automorphism).ker := by
  rw [commutative_frattini_eq_power_range Nat.prime_two hpgroup]
  rintro element ⟨source, rfl⟩
  change automorphism (source ^ 2) * (source ^ 2)⁻¹ = 1
  rw [deep_involution_fixes_squares hpgroup automorphism hdeep hinvolution, mul_inv_cancel]

@[expose] noncomputable def deepInvolutionDifference (automorphism : MulAut Abelian)
    (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (hinvolution : automorphism ^ 2 = 1) :
    (Abelian ⧸ frattini Abelian) →* (powMonoidHom 2 : Abelian →* Abelian).ker := by
  let difference := (abelianAutomorphismDifference automorphism).codRestrict
    (powMonoidHom 2 : Abelian →* Abelian).ker
    (deep_involution_difference_square_one hpgroup automorphism hdeep hinvolution)
  have hkernel : frattini Abelian ≤ difference.ker := by
    intro element helement
    apply Subtype.ext
    exact deep_involution_difference_kills_frattini hpgroup automorphism hdeep hinvolution helement
  exact QuotientGroup.lift (frattini Abelian) difference hkernel

theorem deepInvolutionDifference_apply (automorphism : MulAut Abelian)
    (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (hinvolution : automorphism ^ 2 = 1) (element : Abelian) :
    (deepInvolutionDifference hpgroup automorphism hdeep hinvolution
      ((QuotientGroup.mk' (frattini Abelian)) element) : Abelian) =
        automorphism element * element⁻¹ := rfl

end DifferenceHom

section Singularity

variable {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
variable (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
variable (hcommutative : IsMulCommutative Normal)

omit [Finite Ambient] in
theorem lift_square_fixed_by_conjugation (lift : Ambient) (square : Normal)
    (hsquare : (square : Ambient) = lift ^ 2) :
    MulAut.conjNormal (H := Normal) lift square = square := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, hsquare]
  simp only [pow_two]
  group

theorem deep_involution_difference_singular
    (hquotientNontrivial : Nontrivial (Normal ⧸ frattini Normal))
    (Involutions : Subgroup (MulAut Normal))
    (hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal))
    (normalSquareMap : Involutions →* (Normal ⧸ frattini Normal))
    (hinjective : Function.Injective normalSquareMap)
    (hsquares : ∀ lift : Ambient, ∀ automorphism : Involutions,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
        ∃ square : Normal, (square : Ambient) = lift ^ 2 ∧
          normalSquareMap automorphism = (QuotientGroup.mk' (frattini Normal)) square) :
    let _ : CommGroup Normal := { (inferInstance : Group Normal) with
      mul_comm := @mul_comm' Normal _ hcommutative }
    ∀ hshape : ∀ automorphism : Involutions,
      automorphism.val ∈ deepAbelianAutomorphisms Normal ∧ automorphism.val ^ 2 = 1,
    ∀ automorphism : Involutions,
      ¬Function.Injective (deepInvolutionDifference (hpgroup.to_subgroup Normal)
        automorphism.val (hshape automorphism).1 (hshape automorphism).2) := by
  dsimp only
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  intro hshape automorphism hnotSingular
  let : Nontrivial (Normal ⧸ frattini Normal) := hquotientNontrivial
  by_cases hone : automorphism = 1
  · subst automorphism
    have hzero : ∀ coset : Normal ⧸ frattini Normal,
        deepInvolutionDifference (hpgroup.to_subgroup Normal) (1 : MulAut Normal)
          (hshape 1).1 (hshape 1).2 coset = 1 := by
      intro coset
      obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (frattini Normal) coset
      apply Subtype.ext
      rw [deepInvolutionDifference_apply]
      simp
    obtain ⟨coset, hcoset⟩ := exists_ne (1 : Normal ⧸ frattini Normal)
    exact hcoset (hnotSingular ((hzero coset).trans (hzero 1).symm))
  · have hcoset : normalSquareMap automorphism ≠ 1 := by
      intro heq
      apply hone
      apply hinjective
      rw [heq, map_one]
    obtain ⟨lift, hlift⟩ := hlifts automorphism
    obtain ⟨square, hsquare, hclass⟩ := hsquares lift automorphism hlift
    have hfixed : automorphism.val square = square := by
      rw [← hlift]
      exact lift_square_fixed_by_conjugation Normal lift square hsquare
    have hkilled : deepInvolutionDifference (hpgroup.to_subgroup Normal) automorphism.val
        (hshape automorphism).1 (hshape automorphism).2 (normalSquareMap automorphism) = 1 := by
      apply Subtype.ext
      rw [hclass, deepInvolutionDifference_apply, hfixed, mul_inv_cancel]
      rfl
    exact hcoset (hnotSingular (hkilled.trans (map_one _).symm))

end Singularity

section RankTwo

variable {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
variable (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
variable (hcommutative : IsMulCommutative Normal)

include hpgroup hcommutative in
omit [Normal.Normal] in
theorem binary_rank_two_frattini_quotient_card {upper lower : ℕ}
    (hupper : 0 < upper) (hlower : 0 < lower)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) :
    Nat.card (Normal ⧸ frattini Normal) = 4 := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  rw [commutative_frattini_card_eq_power_kernel Nat.prime_two (hpgroup.to_subgroup Normal)]
  have hcard := binary_rank_two_square_kernel_card Normal hcommutative hupper hlower coordinates
  change Nat.card ((powMonoidHom 2 : Normal →* Normal).ker.map Normal.subtype) = 4 at hcard
  rwa [Subgroup.card_map_of_injective Subtype.val_injective] at hcard

theorem exists_rank_two_deep_lift_square_injection
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnoEight : ∀ Eight : Subgroup Ambient, Eight.Normal →
      CFSG.Open.IsElemAbelian 2 Eight → Nat.card Eight ≠ 8)
    {upper lower : ℕ} (hordered : lower ≤ upper) (hlower : 3 ≤ lower)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) :
    let _ : CommGroup Normal := { (inferInstance : Group Normal) with
      mul_comm := @mul_comm' Normal _ hcommutative }
    ∃ (Involutions : Subgroup (MulAut Normal))
      (_ : CFSG.Open.IsElemAbelian 2 Involutions)
      (hshape : ∀ automorphism : MulAut Normal, automorphism ∈ Involutions ↔
        automorphism ∈ deepAbelianAutomorphisms Normal ∧ automorphism ^ 2 = 1 ∧
          automorphism ∈ (MulAut.conjNormal (H := Normal)).range)
      (hstable : ∀ conjugator : Ambient, ∀ automorphism : MulAut Normal,
        automorphism ∈ Involutions →
          MulAut.conjNormal (H := Normal) conjugator * automorphism *
            (MulAut.conjNormal (H := Normal) conjugator)⁻¹ ∈ Involutions),
        ∃ squareMap : Involutions →* (Normal ⧸ frattini Normal),
          Function.Injective squareMap ∧
          (∀ lift : Ambient, ∀ automorphism : Involutions,
            MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
              ∃ square : Normal, (square : Ambient) = lift ^ 2 ∧
                squareMap automorphism = (QuotientGroup.mk' (frattini Normal)) square) ∧
          (∀ conjugator : Ambient, ∀ automorphism : Involutions,
            squareMap (invariantSubgroupConjugation (MulAut.conjNormal (H := Normal))
              Involutions hstable conjugator automorphism) =
                normalFrattiniConjugation Normal conjugator (squareMap automorphism)) ∧
          Nat.log 2 (Nat.card Involutions) ≤ 2 ∧
          ∀ automorphism : Involutions,
            ¬Function.Injective (deepInvolutionDifference (hpgroup.to_subgroup Normal)
              automorphism.val ((hshape _).mp automorphism.property).1
                ((hshape _).mp automorphism.property).2.1) := by
  dsimp only
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  have hroot := binary_rank_two_power_root Normal hcommutative (by omega) (by omega) coordinates
  have hkernelCard := binary_rank_two_square_kernel_card Normal hcommutative (by omega) (by omega)
    coordinates
  let _ := normalPowerSubgroup_normal Normal hcommutative 2
  obtain ⟨Involutions, helementary, hshape, ambientSquareMap, hinjective, hsquares⟩ :=
    exists_deep_conjugation_square_injection hpgroup Normal hcommutative hselfCentralizing
      hnoEight hkernelCard hroot
  have hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) := by
    intro automorphism
    exact ((hshape _).mp automorphism.property).2.2
  have hstable : ∀ conjugator : Ambient, ∀ automorphism : MulAut Normal,
      automorphism ∈ Involutions → MulAut.conjNormal (H := Normal) conjugator * automorphism *
        (MulAut.conjNormal (H := Normal) conjugator)⁻¹ ∈ Involutions := by
    intro conjugator automorphism hmem
    rcases (hshape _).mp hmem with ⟨hdeep, hinvolution, lift, hlift⟩
    apply (hshape _).mpr
    refine ⟨(deepAbelianAutomorphisms_normal Normal).conj_mem automorphism hdeep _, ?_, ?_⟩
    · simp only [pow_two] at hinvolution ⊢
      calc
        _ = MulAut.conjNormal (H := Normal) conjugator *
            (automorphism * automorphism) * (MulAut.conjNormal (H := Normal) conjugator)⁻¹ := by group
        _ = 1 := by rw [hinvolution]; group
    · refine ⟨conjugator * lift * conjugator⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, hlift]
  obtain ⟨squareMap, hsquareInjective, hembedding, hnormalSquares⟩ :=
    conjugation_square_map_in_normal_frattini hpgroup Normal hcommutative hselfCentralizing
      Involutions helementary hlifts ambientSquareMap hinjective hsquares
  have hcard := binary_rank_two_frattini_quotient_card hpgroup Normal hcommutative
    (by omega) (by omega) coordinates
  have hquotientNontrivial : Nontrivial (Normal ⧸ frattini Normal) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcard]
    decide
  have hsize := Nat.card_le_card_of_injective squareMap hsquareInjective
  rw [hcard] at hsize
  have hrank : Nat.log 2 (Nat.card Involutions) ≤ 2 := by
    have hlog := Nat.log_mono_right (b := 2) hsize
    exact hlog.trans (by decide)
  refine ⟨Involutions, helementary, hshape, hstable, squareMap, hsquareInjective,
    hnormalSquares, ?_, hrank, ?_⟩
  · exact normal_frattini_lift_square_equivariant Normal Involutions hstable hlifts
      squareMap hnormalSquares
  · exact deep_involution_difference_singular hpgroup Normal hcommutative hquotientNontrivial
      Involutions hlifts squareMap hsquareInjective hnormalSquares
      (fun automorphism => ⟨((hshape _).mp automorphism.property).1,
        ((hshape _).mp automorphism.property).2.1⟩)

end RankTwo

end CFSG.LargeEvenClassification.Helpers
