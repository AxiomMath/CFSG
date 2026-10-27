module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank
public import CFSG.LocalAnalysis.LargeEvenClassification.LiftSquareMap
public import CFSG.LocalAnalysis.LargeEvenClassification.DeepLiftCommutation
public import CFSG.LocalAnalysis.LargeEvenClassification.LiftSquareInjection
public import CFSG.LocalAnalysis.LargeEvenClassification.PrincipalNorm

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def deepAbelianAutomorphisms (Abelian : Type groupUniverse) [CommGroup Abelian] :
    Subgroup (MulAut Abelian) :=
  (principalFourSubgroup (AddMonoid.End (Additive Abelian))).comap
    (abelianAutomorphismUnits Abelian)

theorem deepAbelianAutomorphisms_normal (Abelian : Type groupUniverse) [CommGroup Abelian] :
    (deepAbelianAutomorphisms Abelian).Normal := by
  let : (principalFourSubgroup (AddMonoid.End (Additive Abelian))).Normal :=
    principal_four_normal _
  exact Subgroup.Normal.comap inferInstance (abelianAutomorphismUnits Abelian)

theorem deepAbelianAutomorphisms_power_difference {Abelian : Type groupUniverse} [CommGroup Abelian]
    (automorphism : MulAut Abelian) (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (element : Abelian) : ∃ source : Abelian, automorphism element * element⁻¹ = source ^ 4 := by
  obtain ⟨operator, hoperator⟩ := hdeep
  have haction := congrArg (fun endomorphism : AddMonoid.End (Additive Abelian) =>
    endomorphism (Additive.ofMul element)) hoperator
  change Additive.ofMul (automorphism element) = Additive.ofMul element +
    4 • operator (Additive.ofMul element) at haction
  refine ⟨(operator (Additive.ofMul element)).toMul, ?_⟩
  have heq := congrArg Additive.toMul haction
  change automorphism element = element * (operator (Additive.ofMul element)).toMul ^ 4 at heq
  rw [heq, mul_comm element]
  group

theorem deepAbelianAutomorphisms_involutions {Abelian : Type groupUniverse} [CommGroup Abelian]
    [Finite Abelian] (hpgroup : IsPGroup 2 Abelian) :
    ∃ Involutions : Subgroup (MulAut Abelian), Involutions.Normal ∧ IsElemAbelian 2 Involutions ∧
      ∀ automorphism : MulAut Abelian, automorphism ∈ Involutions ↔
        automorphism ∈ deepAbelianAutomorphisms Abelian ∧ automorphism ^ 2 = 1 := by
  obtain ⟨exponent, hcharacteristic⟩ := pGroup_addEnd_binary_characteristic hpgroup
  let Deep := deepAbelianAutomorphisms Abelian
  let : Deep.Normal := deepAbelianAutomorphisms_normal Abelian
  have hcommute : ∀ first ∈ Deep, ∀ second ∈ Deep,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second := by
    intro first hfirst second hsecond hsquare _
    apply abelianAutomorphismUnits_injective Abelian
    rw [map_mul, map_mul]
    exact principal_involution_central hcharacteristic
      ((abelianAutomorphismUnits Abelian) first) ((abelianAutomorphismUnits Abelian) second)
      hfirst hsecond (by rw [← map_pow, hsquare, map_one])
  let Involutions := normalSquareOneSubgroup Deep hcommute
  exact ⟨Involutions, normalSquareOneSubgroup_normal Deep hcommute,
    normalSquareOneSubgroup_elementary Deep hcommute, fun _ => Iff.rfl⟩

theorem exists_deep_conjugation_square_injection {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnoEight : ∀ Eight : Subgroup Ambient, Eight.Normal → IsElemAbelian 2 Eight → Nat.card Eight ≠ 8)
    (hcard : Nat.card (normalElementarySquareKernel Normal hcommutative) = 4)
    (hroot : ∀ element : Normal,
      (element : Ambient) ^ 2 ∈ normalPowerSubgroup Normal hcommutative 4 →
        (element : Ambient) ∈ normalPowerSubgroup Normal hcommutative 2) :
    let _ : CommGroup Normal := { (inferInstance : Group Normal) with
      mul_comm := @mul_comm' Normal _ hcommutative }
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ∃ Involutions : Subgroup (MulAut Normal), IsElemAbelian 2 Involutions ∧
      (∀ automorphism : MulAut Normal, automorphism ∈ Involutions ↔
        automorphism ∈ deepAbelianAutomorphisms Normal ∧ automorphism ^ 2 = 1 ∧
          automorphism ∈ (MulAut.conjNormal (H := Normal)).range) ∧
      ∃ squareMap : Involutions →* (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2),
        Function.Injective squareMap ∧
        ∀ lift : Ambient, ∀ automorphism : Involutions,
          MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
            squareMap automorphism =
              (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (lift ^ 2) := by
  dsimp only
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let Power := normalPowerSubgroup Normal hcommutative 2
  let : Power.Normal := normalPowerSubgroup_normal Normal hcommutative 2
  let action : Ambient →* MulAut Normal := MulAut.conjNormal
  obtain ⟨Full, hfullNormal, hfullElementary, hfullShape⟩ :=
    deepAbelianAutomorphisms_involutions (hpgroup.to_subgroup Normal)
  let Involutions := Full ⊓ action.range
  have helementary : IsElemAbelian 2 Involutions :=
    elementary_subgroup_of_le Full Involutions hfullElementary inf_le_left
  have hshape : ∀ automorphism : MulAut Normal, automorphism ∈ Involutions ↔
      automorphism ∈ deepAbelianAutomorphisms Normal ∧ automorphism ^ 2 = 1 ∧
        automorphism ∈ action.range := by
    intro automorphism
    change (automorphism ∈ Full ∧ automorphism ∈ action.range) ↔ _
    rw [hfullShape]
    tauto
  have hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      action lift = (automorphism : MulAut Normal) := by
    intro automorphism
    exact automorphism.property.2
  have hstable : ∀ conjugator : Ambient, ∀ automorphism : MulAut Normal,
      automorphism ∈ Involutions → action conjugator * automorphism * (action conjugator)⁻¹ ∈
        Involutions := by
    intro conjugator automorphism helement
    exact ⟨hfullNormal.conj_mem automorphism helement.1 (action conjugator),
      action.range.mul_mem (action.range.mul_mem ⟨conjugator, rfl⟩ helement.2)
        (action.range.inv_mem ⟨conjugator, rfl⟩)⟩
  have hdeepLift : ∀ lift : Ambient, action lift ∈ Involutions → ∀ element : Normal,
      lift * (element : Ambient) * lift⁻¹ * (element : Ambient)⁻¹ ∈
        normalPowerSubgroup Normal hcommutative 4 := by
    intro lift hlift element
    obtain ⟨source, hsource⟩ := deepAbelianAutomorphisms_power_difference (action lift)
      ((hshape _).mp hlift).1 element
    apply (normalPowerSubgroup_mem Normal hcommutative 4 _).mpr
    refine ⟨source, ?_⟩
    have heq := congrArg (fun entry : Normal => (entry : Ambient)) hsource
    change (MulAut.conjNormal (H := Normal) lift element : Ambient) * (element : Ambient)⁻¹ =
      (source : Ambient) ^ 4 at heq
    rw [MulAut.conjNormal_apply] at heq
    exact heq.symm
  have hquotientCommute : ∀ first second : Ambient,
      action first ∈ Involutions → action second ∈ Involutions →
        Commute ((QuotientGroup.mk' Power) first) ((QuotientGroup.mk' Power) second) := by
    intro first second hfirst hsecond
    apply deep_lifts_commute_mod_squares Normal hcommutative hselfCentralizing first second
      ((hshape _).mp hfirst).2.1
    · exact congrArg (fun entry : Involutions => (entry : MulAut Normal))
        (@mul_comm' Involutions _ helementary.1 ⟨_, hfirst⟩ ⟨_, hsecond⟩)
    · exact hdeepLift first hfirst
    · exact hdeepLift second hsecond
    · exact hroot
  obtain ⟨squareMap, hsquares⟩ := exists_conjugation_lift_square Normal hcommutative
    hselfCentralizing Involutions hlifts hquotientCommute
  refine ⟨Involutions, helementary, hshape, squareMap, ?_, hsquares⟩
  apply conjugation_lift_square_injective hpgroup Normal hcommutative hselfCentralizing hnoEight
    hcard Involutions hstable helementary hlifts _ _ squareMap hsquares
  · intro automorphism
    exact (abelian_principal_norm (hpgroup.to_subgroup Normal) automorphism
      ((hshape _).mp automorphism.property).1).1
  · intro automorphism
    exact (abelian_principal_norm (hpgroup.to_subgroup Normal) automorphism
      ((hshape _).mp automorphism.property).1).2

theorem conjugation_square_injection_card_bound {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal) (hselfCentralizing :
      Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnormalRank : pGeneratorRank 2 Normal ≤ 2) (Involutions : Subgroup (MulAut Normal))
    (helementary : IsElemAbelian 2 Involutions)
    (hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal)) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ∀ squareMap : Involutions →* (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2),
      Function.Injective squareMap →
      (∀ lift : Ambient, ∀ automorphism : Involutions,
        MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
          squareMap automorphism =
            (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (lift ^ 2)) →
      Nat.card Involutions ≤ 4 := by
  dsimp only
  let Power := normalPowerSubgroup Normal hcommutative 2
  let : Power.Normal := normalPowerSubgroup_normal Normal hcommutative 2
  intro squareMap hinjective hsquares
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let projection := QuotientGroup.mk' Power
  let Image := Normal.map projection
  have himageComm : IsMulCommutative Image := by
    apply isMulCommutative_iff.mpr
    intro first second
    obtain ⟨firstSource, hfirst⟩ := projection.subgroupMap_surjective Normal first
    obtain ⟨secondSource, hsecond⟩ := projection.subgroupMap_surjective Normal second
    rw [← hfirst, ← hsecond, ← map_mul, ← map_mul, mul_comm firstSource]
  let : CommGroup Image := { (inferInstance : Group Image) with
    mul_comm := @mul_comm' Image _ himageComm }
  have hexponent : ∀ element : Image, element ^ 2 = 1 := by
    intro element
    obtain ⟨source, rfl⟩ := projection.subgroupMap_surjective Normal element
    apply Subtype.ext
    change (projection (source : Ambient)) ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      ((normalPowerSubgroup_mem Normal hcommutative 2 _).mpr ⟨source, rfl⟩)
  have hpImage := (hpgroup.to_subgroup Normal).of_surjective (projection.subgroupMap Normal)
    (projection.subgroupMap_surjective Normal)
  have himageRank := (pGeneratorRank_surjective_le Nat.prime_two (hpgroup.to_subgroup Normal)
    (projection.subgroupMap Normal) (projection.subgroupMap_surjective Normal)).trans hnormalRank
  obtain ⟨rank, hcard⟩ := hpImage.exists_card_eq
  rw [elementary_pGeneratorRank_eq_log_card Nat.prime_two hexponent, hcard,
    Nat.log_pow (by decide : 1 < 2)] at himageRank
  have himageCard : Nat.card Image ≤ 4 := by
    rw [hcard]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) himageRank).trans (by decide)
  have hmapImage : ∀ automorphism : Involutions, squareMap automorphism ∈ Image := by
    intro automorphism
    obtain ⟨lift, hlift⟩ := hlifts automorphism
    have hsquare : lift ^ 2 ∈ Normal := by
      have hkernel : (MulAut.conjNormal (H := Normal)).ker = Normal :=
        (conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing
      apply hkernel.le
      change MulAut.conjNormal (H := Normal) (lift ^ 2) = 1
      rw [map_pow, hlift]
      exact helementary.2 automorphism automorphism.property
    rw [hsquares lift automorphism hlift]
    exact Subgroup.mem_map.mpr ⟨lift ^ 2, hsquare, rfl⟩
  let injection := squareMap.codRestrict Image hmapImage
  have hinjection : Function.Injective injection := by
    intro first second heq
    exact hinjective (congrArg (fun entry : Image => (entry : Ambient ⧸ Power)) heq)
  exact (Nat.card_le_card_of_injective injection hinjection).trans himageCard

theorem deep_abelian_action_generator_bound {Abelian : Type groupUniverse} [CommGroup Abelian]
    [Finite Abelian] (hpabelian : IsPGroup 2 Abelian) (Action : Subgroup (MulAut Abelian))
    (hpaction : IsPGroup 2 Action) (Involutions : Subgroup (MulAut Abelian))
    (hshape : ∀ automorphism : MulAut Abelian, automorphism ∈ Involutions ↔
      automorphism ∈ deepAbelianAutomorphisms Abelian ∧ automorphism ^ 2 = 1 ∧
        automorphism ∈ Action) :
    pGeneratorRank 2 ((deepAbelianAutomorphisms Abelian).comap Action.subtype) ≤
      Nat.log 2 (Nat.card Involutions) := by
  let Deep := (deepAbelianAutomorphisms Abelian).comap Action.subtype
  let embedding := (abelianAutomorphismUnits Abelian).comp
    (Action.subtype.comp Deep.subtype)
  have hinjective : Function.Injective embedding :=
    (abelianAutomorphismUnits_injective Abelian).comp
      (Subtype.val_injective.comp Subtype.val_injective)
  let equivalence := MonoidHom.ofInjective hinjective
  let : Finite embedding.range := Finite.of_surjective embedding.rangeRestrict
    embedding.rangeRestrict_surjective
  have hpDeep := hpaction.to_subgroup Deep
  have hpImage := hpDeep.of_surjective embedding.rangeRestrict embedding.rangeRestrict_surjective
  obtain ⟨exponent, hcharacteristic⟩ := pGroup_addEnd_binary_characteristic hpabelian
  have hprincipal : ∀ element : embedding.range,
      ∃ entry : AddMonoid.End (Additive Abelian), element.val.val = 1 + 4 * entry := by
    intro element
    obtain ⟨source, heq⟩ := element.property
    have hsource := source.property
    change ∃ entry : AddMonoid.End (Additive Abelian), (embedding source).val = 1 + 4 * entry
      at hsource
    rw [heq] at hsource
    exact hsource
  let RingInvolutions := principalInvolutionSubgroup hcharacteristic embedding.range hprincipal
  have hbound := principal_pGeneratorRank_le_involutions hcharacteristic embedding.range
    hpImage hprincipal
  have hringCard : Nat.card RingInvolutions = Nat.card Involutions := by
    let forward : RingInvolutions → Involutions := fun element =>
      ⟨(equivalence.symm element.val).val.val, by
        apply (hshape _).mpr
        refine ⟨(equivalence.symm element.val).property, ?_,
          (equivalence.symm element.val).val.property⟩
        have hsquare : (equivalence.symm element.val) ^ 2 = 1 := by
          apply equivalence.injective
          rw [map_pow, equivalence.apply_symm_apply, map_one]
          exact element.property
        exact congrArg (fun entry : Deep => (entry.val : MulAut Abelian)) hsquare⟩
    have hforwardInjective : Function.Injective forward := by
      intro first second heq
      apply Subtype.ext
      apply equivalence.symm.injective
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun entry : Involutions => (entry : MulAut Abelian)) heq
    have hforwardSurjective : Function.Surjective forward := by
      intro automorphism
      have hproperties := (hshape _).mp automorphism.property
      let source : Deep := ⟨⟨automorphism, hproperties.2.2⟩, hproperties.1⟩
      have hsquare : source ^ 2 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact hproperties.2.1
      refine ⟨⟨equivalence source, ?_⟩, ?_⟩
      · change (equivalence source) ^ 2 = 1
        rw [← map_pow, hsquare, map_one]
      · apply Subtype.ext
        change (equivalence.symm (equivalence source)).val.val = automorphism.val
        rw [equivalence.symm_apply_apply]
    exact Nat.card_congr (Equiv.ofBijective forward ⟨hforwardInjective, hforwardSurjective⟩)
  change pGeneratorRank 2 embedding.range ≤ Nat.log 2 (Nat.card RingInvolutions) at hbound
  rw [hringCard] at hbound
  rw [pGeneratorRank_mulEquiv Nat.prime_two hpDeep equivalence]
  exact hbound

end CFSG.LargeEvenClassification.Helpers
