module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction

public section

open CFSG.Open
open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem nonzero_vector_has_surjective_additive_functional
    {coefficient : Type u} {space : Type v}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    (member : space) (hnonzero : member ≠ 0) :
    ∃ hom : space →+ coefficient, hom member = 1 ∧ Function.Surjective hom := by
  obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_eq_one coefficient hnonzero
  refine ⟨functional.toAddMonoidHom, hfunctional, ?_⟩
  intro value
  refine ⟨value • member, ?_⟩
  change functional (value • member) = value
  rw [map_smul, hfunctional, smul_eq_mul, mul_one]

theorem prime_card_group_frattini_eq_bot
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hcard : Nat.card source = prime) :
    frattini source = ⊥ := by
  let : Fact (Nat.card source).Prime := ⟨hcard ▸ Fact.out⟩
  have hbotCoatom : IsCoatom (⊥ : Subgroup source) := by
    refine ⟨?_, ?_⟩
    · intro hequal
      have hcards := congrArg (fun subgroup : Subgroup source => Nat.card subgroup) hequal
      rw [Subgroup.card_bot, Subgroup.card_top, hcard] at hcards
      exact (Fact.out : prime.Prime).ne_one hcards.symm
    · intro subgroup hlarge
      exact (subgroup.eq_bot_or_eq_top_of_prime_card).resolve_left (ne_of_gt hlarge)
  exact bot_unique (frattini_le_coatom hbotCoatom)

theorem elementary_group_frattini_eq_bot
    {source : Type u} [CommGroup source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hpow : ∀ member : source, member ^ prime = 1) :
    frattini source = ⊥ := by
  let : Module (ZMod prime) (Additive source) :=
    AddCommGroup.zmodModule (n := prime) (G := Additive source) fun member => by
    change Additive.ofMul (member.toMul ^ prime) = 0
    rw [hpow]
    rfl
  apply (Subgroup.eq_bot_iff_forall (frattini source)).mpr
  intro member hmember
  by_contra hnonidentity
  have hnonzero : (Additive.ofMul member : Additive source) ≠ 0 := hnonidentity
  obtain ⟨functional, hfunctional, hfunctionalSurjective⟩ :=
    nonzero_vector_has_surjective_additive_functional (coefficient := ZMod prime)
      (Additive.ofMul member) hnonzero
  let hom : source →* Multiplicative (ZMod prime) :=
    { toFun := fun element => Multiplicative.ofAdd (functional (Additive.ofMul element))
      map_one' := by exact congrArg Multiplicative.ofAdd functional.map_zero
      map_mul' := fun first second => congrArg Multiplicative.ofAdd
        (functional.map_add (Additive.ofMul first) (Additive.ofMul second)) }
  have hsurjective : Function.Surjective hom := by
    intro value
    obtain ⟨lift, hlift⟩ := hfunctionalSurjective value.toAdd
    exact ⟨lift.toMul, congrArg Multiplicative.ofAdd hlift⟩
  have hfrattini := frattini_le_comap_frattini_of_surjective hsurjective hmember
  rw [prime_card_group_frattini_eq_bot prime (by simp)] at hfrattini
  have hzero : functional (Additive.ofMul member) = 0 := Subgroup.mem_bot.mp hfrattini
  rw [hfunctional] at hzero
  exact one_ne_zero hzero

theorem frattini_le_normal_of_elementary_quotient
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (normal : Subgroup source) [normal.Normal]
    (helementary : IsElemAbelian prime (⊤ : Subgroup (source ⧸ normal))) :
    frattini source ≤ normal := by
  let : IsMulCommutative (source ⧸ normal) := IsMulCommutative.of_comm fun first second =>
    congrArg Subtype.val ((isMulCommutative_iff.mp helementary.1)
      (⟨first, Subgroup.mem_top _⟩ : (⊤ : Subgroup (source ⧸ normal)))
      ⟨second, Subgroup.mem_top _⟩)
  let : CommGroup (source ⧸ normal) := IsMulCommutative.instCommGroup
  have hfrattini : frattini (source ⧸ normal) = ⊥ := elementary_group_frattini_eq_bot prime
    (fun member => helementary.2 member (Subgroup.mem_top member))
  have hcontained := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective normal)
  rw [hfrattini, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hcontained
  exact hcontained

theorem pGroup_normal_subgroup_meets_center
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnontrivial : normal ≠ ⊥) :
    normal ⊓ Subgroup.center source ≠ ⊥ := by
  let : Nontrivial normal := normal.nontrivial_iff_ne_bot.mpr hnontrivial
  let : MulDistribMulAction source normal :=
    MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
  have hnormalGroup : IsPGroup prime normal := hgroup.to_subgroup normal
  have hcard : prime ∣ Nat.card normal := hnormalGroup.card_eq_or_dvd.resolve_left
    (fun hcardOne => hnontrivial (normal.eq_bot_iff_card.mpr hcardOne))
  have hfixedOne : (1 : normal) ∈ MulAction.fixedPoints source normal := fun scalar => smul_one scalar
  obtain ⟨member, hfixed, hnonidentity⟩ :=
    hgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point normal hcard hfixedOne
  intro hbot
  have hcentral : (member : source) ∈ Subgroup.center source := by
    apply Subgroup.mem_center_iff.mpr
    intro scalar
    have hequal := congrArg Subtype.val (hfixed scalar)
    change scalar * (member : source) * scalar⁻¹ = member at hequal
    have hcommute := congrArg (fun value : source => value * scalar) hequal
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute
  have hidentity := Subgroup.mem_bot.mp
    (hbot ▸ (show (member : source) ∈ normal ⊓ Subgroup.center source from ⟨member.property, hcentral⟩))
  exact hnonidentity (Subtype.ext hidentity.symm)

@[expose] noncomputable def centralPrimeTorsion (prime : ℕ) (source : Type u) [Group source] : Subgroup source :=
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  ((powMonoidHom prime : Subgroup.center source →* Subgroup.center source).ker).map
    (Subgroup.center source).subtype

theorem mem_centralPrimeTorsion
    {source : Type u} [Group source] (prime : ℕ) (member : source) :
    member ∈ centralPrimeTorsion prime source ↔
      member ∈ Subgroup.center source ∧ member ^ prime = 1 := by
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    exact ⟨lift.property, congrArg Subtype.val hlift⟩
  · rintro ⟨hcentral, hpow⟩
    exact ⟨⟨member, hcentral⟩, Subtype.ext hpow, rfl⟩

theorem centralPrimeTorsion_characteristic
    {source : Type u} [Group source] (prime : ℕ) :
    (centralPrimeTorsion prime source).Characteristic := by
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  let : (powMonoidHom prime : Subgroup.center source →* Subgroup.center source).ker.Characteristic :=
    power_kernel_characteristic prime
  exact Subgroup.characteristic_of_characteristic_of_characteristic

theorem centralPrimeTorsion_elementary
    {source : Type u} [Group source] (prime : ℕ) :
    IsElemAbelian prime (centralPrimeTorsion prime source) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro first second
    apply Subtype.ext
    change (first : source) * (second : source) = (second : source) * (first : source)
    exact (Subgroup.mem_center_iff.mp
      ((mem_centralPrimeTorsion prime (first : source)).mp first.property).1 (second : source)).symm
  · intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).2

theorem pGroup_normal_subgroup_meets_centralPrimeTorsion
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnontrivial : normal ≠ ⊥) :
    normal ⊓ centralPrimeTorsion prime source ≠ ⊥ := by
  let intersection := normal ⊓ Subgroup.center source
  have hnontrivialIntersection : intersection ≠ ⊥ :=
    pGroup_normal_subgroup_meets_center prime hgroup normal hnontrivial
  have hintersectionGroup : IsPGroup prime intersection := hgroup.to_subgroup intersection
  have hcard : prime ∣ Nat.card intersection := hintersectionGroup.card_eq_or_dvd.resolve_left
    (fun hcardOne => hnontrivialIntersection (intersection.eq_bot_iff_card.mpr hcardOne))
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' prime hcard
  have hpow : (member : source) ^ prime = 1 := by
    exact congrArg Subtype.val (horder ▸ pow_orderOf_eq_one member)
  intro hbot
  have hidentity : (member : source) = 1 := Subgroup.mem_bot.mp
    (hbot ▸ (show (member : source) ∈ normal ⊓ centralPrimeTorsion prime source from
      ⟨member.property.1, (mem_centralPrimeTorsion prime (member : source)).mpr
        ⟨member.property.2, hpow⟩⟩))
  have hmemberIdentity : member = 1 := Subtype.ext hidentity
  rw [hmemberIdentity, orderOf_one] at horder
  exact (Fact.out : prime.Prime).ne_one horder.symm

theorem subgroup_center_image_eq_inf_centralizer
    {source : Type u} [Group source] (subgroup : Subgroup source) :
    (Subgroup.center subgroup).map subgroup.subtype =
      subgroup ⊓ Subgroup.centralizer (subgroup : Set source) := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    refine ⟨lift.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro other hother
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hlift (⟨other, hother⟩ : subgroup))
  · rintro ⟨hmember, hcentral⟩
    refine ⟨⟨member, hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcentral other other.property

theorem subgroup_quotient_map_le_center_of_commutator_le
    {source : Type u} [Group source] (normal subgroup : Subgroup source) [normal.Normal]
    (hcommutator : ⁅(⊤ : Subgroup source), subgroup⁆ ≤ normal) :
    subgroup.map (QuotientGroup.mk' normal) ≤ Subgroup.center (source ⧸ normal) := by
  rintro member ⟨lift, hlift, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro other
  obtain ⟨otherLift, rfl⟩ := QuotientGroup.mk'_surjective normal other
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top otherLift) hlift))

theorem subgroup_commutator_le_of_quotient_map_le_center
    {source : Type u} [Group source] (normal subgroup : Subgroup source) [normal.Normal]
    (hcentral : subgroup.map (QuotientGroup.mk' normal) ≤ Subgroup.center (source ⧸ normal)) :
    ⁅(⊤ : Subgroup source), subgroup⁆ ≤ normal := by
  apply Subgroup.commutator_le.mpr
  intro first _ second hsecond
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' normal) ⁅first, second⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact Subgroup.mem_center_iff.mp
    (hcentral (Subgroup.mem_map_of_mem _ hsecond)) ((QuotientGroup.mk' normal) first)

theorem pGroup_has_characteristic_critical_subgroup
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source) :
    ∃ critical : Subgroup source, critical.Characteristic ∧
      (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
      ⁅(⊤ : Subgroup source), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
      Subgroup.centralizer (critical : Set source) = (Subgroup.center critical).map critical.subtype := by
  classical
  let admissible := fun subgroup : Subgroup source => subgroup.Characteristic ∧
    (∀ member ∈ subgroup, member ^ prime ∈ (Subgroup.center subgroup).map subgroup.subtype) ∧
      ⁅(⊤ : Subgroup source), subgroup⁆ ≤ (Subgroup.center subgroup).map subgroup.subtype
  have hbot : admissible ⊥ := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro member hmember
      rw [Subgroup.mem_bot.mp hmember, one_pow]
      exact Subgroup.one_mem _
    · simp
  obtain ⟨critical, _, hmaximal⟩ := Finite.exists_le_maximal hbot
  let : critical.Characteristic := hmaximal.1.1
  let center := (Subgroup.center critical).map critical.subtype
  let centralizer := Subgroup.centralizer (critical : Set source)
  let : center.Characteristic := Subgroup.characteristic_of_characteristic_of_characteristic
  let : centralizer.Characteristic := inferInstance
  let quotientHom := QuotientGroup.mk' center
  have hcenterCritical : center ≤ critical := Subgroup.map_subtype_le _
  have hcriticalCentralizer : critical ⊓ centralizer = center :=
    (subgroup_center_image_eq_inf_centralizer critical).symm
  have hcenterCentralizer : center ≤ centralizer := by rw [← hcriticalCentralizer]; exact inf_le_right
  have hcriticalImageCentral : critical.map quotientHom ≤ Subgroup.center (source ⧸ center) :=
    subgroup_quotient_map_le_center_of_commutator_le center critical hmaximal.1.2.2
  have hcriticalImageElementary : IsElemAbelian prime (critical.map quotientHom) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro first second
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hcriticalImageCentral first.property) second).symm
    · rintro member ⟨lift, hlift, rfl⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hmaximal.1.2.1 lift hlift)
  have hcentralizerEq : centralizer = center := by
    by_contra hneq
    have himageNontrivial : centralizer.map quotientHom ≠ ⊥ := by
      intro hbotImage
      have hcontained : centralizer ≤ center := by
        have hkernel := (centralizer.map_eq_bot_iff).mp hbotImage
        rwa [QuotientGroup.ker_mk'] at hkernel
      exact hneq (le_antisymm hcontained hcenterCentralizer)
    let : (centralizer.map quotientHom).Normal :=
      (inferInstance : centralizer.Normal).map quotientHom (QuotientGroup.mk'_surjective center)
    let torsion := centralPrimeTorsion prime (source ⧸ center)
    let extension := centralizer ⊓ torsion.comap quotientHom
    let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
    let : (torsion.comap quotientHom).Characteristic :=
      Subgroup.Characteristic.comap_quotient_mk (inferInstance : torsion.Characteristic)
    let : extension.Characteristic := inferInstance
    have hcenterExtension : center ≤ extension := by
      refine le_inf hcenterCentralizer ?_
      intro member hmember
      change quotientHom member ∈ torsion
      have hquotientOne : quotientHom member = 1 := (QuotientGroup.eq_one_iff member).mpr hmember
      rw [hquotientOne]
      exact torsion.one_mem
    have hextensionNontrivial : ¬ extension ≤ center := by
      have hnontrivial := pGroup_normal_subgroup_meets_centralPrimeTorsion prime
        (hgroup.to_quotient center) (centralizer.map quotientHom) himageNontrivial
      intro hcontained
      apply hnontrivial
      apply (Subgroup.eq_bot_iff_forall _).mpr
      rintro member ⟨⟨lift, hlift, rfl⟩, htorsion⟩
      exact (QuotientGroup.eq_one_iff lift).mpr (hcontained ⟨hlift, htorsion⟩)
    have hextensionCentral : extension ≤ centralizer := inf_le_left
    have hextensionImage : extension.map quotientHom ≤ torsion :=
      Subgroup.map_le_iff_le_comap.mpr inf_le_right
    have hextensionImageCentral : extension.map quotientHom ≤ Subgroup.center (source ⧸ center) := by
      intro member hmember
      exact ((mem_centralPrimeTorsion prime member).mp (hextensionImage hmember)).1
    have hextensionImageElementary : IsElemAbelian prime (extension.map quotientHom) := by
      have helementary := centralPrimeTorsion_elementary (source := source ⧸ center) prime
      refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
      · intro first second
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hextensionImageCentral first.property) second).symm
      · intro member hmember
        exact helementary.2 member (hextensionImage hmember)
    let larger := critical ⊔ extension
    let : larger.Characteristic := inferInstance
    have hcenterLarger : center ≤ larger := hcenterCritical.trans le_sup_left
    have hcenterLargerCentral : center ≤ (Subgroup.center larger).map larger.subtype := by
      rw [subgroup_center_image_eq_inf_centralizer]
      refine le_inf hcenterLarger ?_
      apply Subgroup.le_centralizer_iff.mpr
      apply sup_le
      · exact Subgroup.le_centralizer_iff.mp hcenterCentralizer
      · exact hextensionCentral.trans (Subgroup.centralizer_le
          (show (center : Set source) ⊆ (critical : Set source) from hcenterCritical))
    have hlargerImageCentral : larger.map quotientHom ≤ Subgroup.center (source ⧸ center) := by
      rw [Subgroup.map_sup]
      exact sup_le hcriticalImageCentral hextensionImageCentral
    have hlargerImageElementary : IsElemAbelian prime (larger.map quotientHom) := by
      rw [Subgroup.map_sup]
      exact elementary_abelian_sup_of_commuting prime hcriticalImageElementary hextensionImageElementary
        (Subgroup.le_centralizer_iff.mpr (hextensionImageCentral.trans (Subgroup.center_le_centralizer _)))
    have hlargerAdmissible : admissible larger := by
      refine ⟨inferInstance, ?_, ?_⟩
      · intro member hmember
        apply hcenterLargerCentral
        apply (QuotientGroup.eq_one_iff _).mp
        change quotientHom (member ^ prime) = 1
        rw [map_pow]
        exact hlargerImageElementary.2 _ (Subgroup.mem_map_of_mem _ hmember)
      · exact (subgroup_commutator_le_of_quotient_map_le_center center larger hlargerImageCentral).trans
          hcenterLargerCentral
    have hlargerLe : larger ≤ critical := hmaximal.2 hlargerAdmissible le_sup_left
    have hextensionCritical : extension ≤ critical := le_sup_right.trans hlargerLe
    apply hextensionNontrivial
    rw [← hcriticalCentralizer]
    exact le_inf hextensionCritical hextensionCentral
  refine ⟨critical, inferInstance, ?_, hmaximal.1.2.2, hcentralizerEq⟩
  let centerLocal := center.subgroupOf critical
  have hcenterLocalEq : centerLocal = Subgroup.center critical :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hcommutatorLocal : commutator critical ≤ centerLocal := by
    apply (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp
    rw [map_commutator_eq, critical.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hcenterCritical]
    exact (Subgroup.commutator_mono le_top le_rfl).trans hmaximal.1.2.2
  let : IsMulCommutative (critical ⧸ centerLocal) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  have hquotientElementary : IsElemAbelian prime (⊤ : Subgroup (critical ⧸ centerLocal)) := by
    refine ⟨inferInstance, ?_⟩
    intro member _
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective centerLocal member
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hmaximal.1.2.1 lift lift.property)
  exact Subgroup.map_le_iff_le_comap.mpr (frattini_le_normal_of_elementary_quotient prime centerLocal
    hquotientElementary)

theorem coprime_pGroup_action_trivial_of_fixed_selfcentralizing_normal
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (normal : Subgroup source) [normal.Normal]
    (hcoprime : ¬ prime ∣ Nat.card normal)
    (hcentralizer : Subgroup.centralizer (normal : Set source) ≤ normal)
    (hfixedNormal : ∀ scalar : acting, ∀ member ∈ normal, scalar • member = member) :
    ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  have hinvariant : ∀ scalar : acting, ∀ member ∈ normal, scalar • member ∈ normal := by
    intro scalar member hmember
    rw [hfixedNormal scalar member hmember]
    exact hmember
  let : MulDistribMulAction acting (source ⧸ normal) :=
    invariant_quotient_mulDistribMulAction normal hinvariant
  let quotientHom := QuotientGroup.mk' normal
  have hquotientFixed : ∀ scalar : acting, ∀ member : source, quotientHom (scalar • member) = quotientHom member := by
    intro scalar member
    apply QuotientGroup.eq.mpr
    apply hcentralizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hconjugate := (inferInstance : normal.Normal).conj_mem other hother member
    have hfixConjugate := hfixedNormal scalar _ hconjugate
    rw [smul_mul', smul_mul', smul_inv', hfixedNormal scalar other hother] at hfixConjugate
    have hequal := congrArg (fun value : source => (scalar • member)⁻¹ * value * member) hfixConjugate
    have hcommute : other * ((scalar • member)⁻¹ * member) =
        ((scalar • member)⁻¹ * member) * other := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using hequal
    exact hcommute
  have hkernelCoprime : ¬ prime ∣ Nat.card quotientHom.ker := by
    rw [QuotientGroup.ker_mk']
    exact hcoprime
  intro scalar member
  obtain ⟨lift, hlift, hfixedLift⟩ := fixedPoint_lifts_of_prime_coprime_kernel prime hacting quotientHom
    (QuotientGroup.mk'_surjective normal) (fun _ _ => rfl) hkernelCoprime
    (quotientHom member) (fun other => hquotientFixed other member)
  have hdifference : lift⁻¹ * member ∈ normal := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientHom (lift⁻¹ * member) = 1
    rw [map_mul, map_inv, hlift, inv_mul_cancel]
  calc
    scalar • member = scalar • (lift * (lift⁻¹ * member)) := by rw [mul_inv_cancel_left]
    _ = (scalar • lift) * (scalar • (lift⁻¹ * member)) := smul_mul' _ _ _
    _ = lift * (lift⁻¹ * member) := by rw [hfixedLift, hfixedNormal scalar _ hdifference]
    _ = member := mul_inv_cancel_left _ _

theorem coprime_pGroup_action_trivial_of_fixed_critical_subgroup
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (actingPrime sourcePrime : ℕ) [Fact actingPrime.Prime] [Fact sourcePrime.Prime]
    (hdistinct : actingPrime ≠ sourcePrime) (hacting : IsPGroup actingPrime acting)
    (hsource : IsPGroup sourcePrime source) (critical : Subgroup source) [critical.Normal]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hfixed : ∀ scalar : acting, ∀ member ∈ critical, scalar • member = member) :
    ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  have hcoprime : ¬ actingPrime ∣ Nat.card critical := by
    obtain ⟨exponent, hcard⟩ := (hsource.to_subgroup critical).exists_card_eq
    rw [hcard]
    exact (Fact.out : actingPrime.Prime).coprime_iff_not_dvd.mp
      (by simpa only [pow_one] using Nat.coprime_pow_primes 1 exponent Fact.out Fact.out hdistinct)
  exact coprime_pGroup_action_trivial_of_fixed_selfcentralizing_normal actingPrime hacting critical
    hcoprime hcritical hfixed

@[expose, instance_reducible]
noncomputable def characteristic_subgroup_mulDistribMulAction
    {acting : Type u} {source : Type v} [Group acting] [Group source]
    [MulDistribMulAction acting source] (subgroup : Subgroup source) [subgroup.Characteristic] :
    MulDistribMulAction acting subgroup where
  smul scalar member := ⟨scalar • (member : source),
    (Subgroup.characteristic_iff_map_le.mp (inferInstance : subgroup.Characteristic)
      (MulDistribMulAction.toMulEquiv source scalar))
        (Subgroup.mem_map_of_mem _ member.property)⟩
  one_smul member := Subtype.ext (one_smul acting (member : source))
  mul_smul first second member := Subtype.ext (mul_smul first second (member : source))
  smul_one scalar := Subtype.ext (smul_one scalar)
  smul_mul scalar first second := Subtype.ext (smul_mul' scalar (first : source) (second : source))

theorem faithful_coprime_pGroup_action_on_selfcentralizing_normal
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (normal : Subgroup source) [normal.Normal] [MulDistribMulAction acting normal]
    (hcoprime : ¬ prime ∣ Nat.card normal)
    (hcentralizer : Subgroup.centralizer (normal : Set source) ≤ normal)
    (hequivariant : ∀ scalar : acting, ∀ member : normal,
      ((scalar • member : normal) : source) = scalar • (member : source))
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    Function.Injective (MulDistribMulAction.toMulAut acting normal) := by
  let hom := MulDistribMulAction.toMulAut acting normal
  apply hom.ker_eq_bot_iff.mp
  apply (Subgroup.eq_bot_iff_forall hom.ker).mpr
  intro scalar hscalar
  have hfixedNormal : ∀ kernelScalar : hom.ker, ∀ member ∈ normal,
      kernelScalar • member = member := by
    intro kernelScalar member hmember
    have hequal := congrArg (fun equivalence : MulAut normal => equivalence (⟨member, hmember⟩ : normal))
      (show hom kernelScalar = 1 from kernelScalar.property)
    have hambient := congrArg Subtype.val hequal
    change (((kernelScalar : acting) • (⟨member, hmember⟩ : normal) : normal) : source) = member at hambient
    rw [hequivariant] at hambient
    exact hambient
  have htrivial := coprime_pGroup_action_trivial_of_fixed_selfcentralizing_normal
    (acting := hom.ker) prime (hacting.to_subgroup hom.ker) normal hcoprime hcentralizer hfixedNormal
  apply hfaithful
  ext member
  change scalar • member = (1 : acting) • member
  rw [one_smul]
  exact htrivial (⟨scalar, hscalar⟩ : hom.ker) member

theorem faithful_coprime_pGroup_action_on_characteristic_critical_subgroup
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (actingPrime sourcePrime : ℕ) [Fact actingPrime.Prime] [Fact sourcePrime.Prime]
    (hdistinct : actingPrime ≠ sourcePrime) (hacting : IsPGroup actingPrime acting)
    (hsource : IsPGroup sourcePrime source) (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
    Function.Injective (MulDistribMulAction.toMulAut acting critical) := by
  let : MulDistribMulAction acting critical := characteristic_subgroup_mulDistribMulAction critical
  have hcoprime : ¬ actingPrime ∣ Nat.card critical := by
    obtain ⟨exponent, hcard⟩ := (hsource.to_subgroup critical).exists_card_eq
    rw [hcard]
    exact (Fact.out : actingPrime.Prime).coprime_iff_not_dvd.mp
      (by simpa only [pow_one] using Nat.coprime_pow_primes 1 exponent Fact.out Fact.out hdistinct)
  exact faithful_coprime_pGroup_action_on_selfcentralizing_normal actingPrime hacting critical
    hcoprime hcritical (fun _ _ => rfl) hfaithful

theorem coprime_pGroup_action_trivial_of_fixed_kernel_and_quotient
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (normal : Subgroup source) [normal.Normal] [MulDistribMulAction acting (source ⧸ normal)]
    (hcoprime : ¬ prime ∣ Nat.card normal)
    (hequivariant : ∀ scalar : acting, ∀ member : source,
      (QuotientGroup.mk' normal) (scalar • member) = scalar • (QuotientGroup.mk' normal) member)
    (hfixedNormal : ∀ scalar : acting, ∀ member ∈ normal, scalar • member = member)
    (hfixedQuotient : ∀ scalar : acting, ∀ member : source ⧸ normal, scalar • member = member) :
    ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  let quotientHom := QuotientGroup.mk' normal
  have hkernelCoprime : ¬ prime ∣ Nat.card quotientHom.ker := by
    rw [QuotientGroup.ker_mk']
    exact hcoprime
  intro scalar member
  obtain ⟨lift, hlift, hfixedLift⟩ := fixedPoint_lifts_of_prime_coprime_kernel prime hacting quotientHom
    (QuotientGroup.mk'_surjective normal) hequivariant hkernelCoprime
    (quotientHom member) (fun other => hfixedQuotient other _)
  have hdifference : lift⁻¹ * member ∈ normal := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientHom (lift⁻¹ * member) = 1
    rw [map_mul, map_inv, hlift, inv_mul_cancel]
  calc
    scalar • member = scalar • (lift * (lift⁻¹ * member)) := by rw [mul_inv_cancel_left]
    _ = (scalar • lift) * (scalar • (lift⁻¹ * member)) := smul_mul' _ _ _
    _ = lift * (lift⁻¹ * member) := by rw [hfixedLift, hfixedNormal scalar _ hdifference]
    _ = member := mul_inv_cancel_left _ _

theorem odd_pGroup_action_on_cyclic_twoGroup_trivial
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [IsCyclic source]
    [MulDistribMulAction acting source]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hacting : IsPGroup prime acting) (hsource : IsPGroup 2 source) :
    ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  let hom := MulDistribMulAction.toMulAut acting source
  have himage : IsPGroup prime hom.range := hacting.of_surjective hom.rangeRestrict hom.rangeRestrict_surjective
  have htrivial := odd_pGroup_eq_one_of_injective_to_cyclic_twoGroup_mulAut prime hprime hodd
    himage hsource hom.range.subtype Subtype.val_injective
  intro scalar member
  have hequal : hom scalar = 1 := congrArg Subtype.val (htrivial (⟨hom scalar, ⟨scalar, rfl⟩⟩ : hom.range))
  exact congrArg (fun equivalence : MulAut source => equivalence member) hequal

theorem faithful_odd_pGroup_action_on_cyclic_center_quotient
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hacting : IsPGroup prime acting) (hsource : IsPGroup 2 source)
    (hcenter : IsCyclic (Subgroup.center source))
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
    Function.Injective (MulDistribMulAction.toMulAut acting (source ⧸ Subgroup.center source)) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : IsCyclic (Subgroup.center source) := hcenter
  let : MulDistribMulAction acting (Subgroup.center source) :=
    characteristic_subgroup_mulDistribMulAction (acting := acting) (Subgroup.center source)
  let : MulDistribMulAction acting (source ⧸ Subgroup.center source) :=
    characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
  let hom := MulDistribMulAction.toMulAut acting (source ⧸ Subgroup.center source)
  apply hom.ker_eq_bot_iff.mp
  apply (Subgroup.eq_bot_iff_forall hom.ker).mpr
  intro scalar hscalar
  have hfixedCenter : ∀ kernelScalar : hom.ker, ∀ member ∈ Subgroup.center source,
      kernelScalar • member = member := by
    intro kernelScalar member hmember
    have hfixed := odd_pGroup_action_on_cyclic_twoGroup_trivial
      (acting := hom.ker) (source := Subgroup.center source) prime hprime hodd
      (hacting.to_subgroup hom.ker) (hsource.to_subgroup (Subgroup.center source))
      kernelScalar (⟨member, hmember⟩ : Subgroup.center source)
    exact congrArg Subtype.val hfixed
  have hfixedQuotient : ∀ kernelScalar : hom.ker, ∀ member : source ⧸ Subgroup.center source,
      kernelScalar • member = member := by
    intro kernelScalar member
    exact congrArg (fun equivalence : MulAut (source ⧸ Subgroup.center source) => equivalence member)
      (show hom kernelScalar = 1 from kernelScalar.property)
  have hcoprime : ¬ prime ∣ Nat.card (Subgroup.center source) := by
    obtain ⟨exponent, hcard⟩ := (hsource.to_subgroup (Subgroup.center source)).exists_card_eq
    rw [hcard]
    exact hprime.coprime_iff_not_dvd.mp
      (by simpa only [pow_one] using Nat.coprime_pow_primes 1 exponent hprime (by norm_num) hodd)
  have htrivial := coprime_pGroup_action_trivial_of_fixed_kernel_and_quotient
    (acting := hom.ker) prime (hacting.to_subgroup hom.ker) (Subgroup.center source)
    hcoprime (fun _ _ => rfl) hfixedCenter hfixedQuotient
  apply hfaithful
  ext member
  change scalar • member = (1 : acting) • member
  rw [one_smul]
  exact htrivial (⟨scalar, hscalar⟩ : hom.ker) member

theorem odd_pGroup_has_faithful_critical_subgroup_action
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hacting : IsPGroup prime acting) (hsource : IsPGroup 2 source)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    ∃ critical : Subgroup source, ∃ hcharacteristic : critical.Characteristic, letI := hcharacteristic
      (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
      ⁅(⊤ : Subgroup source), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
      Subgroup.centralizer (critical : Set source) = (Subgroup.center critical).map critical.subtype ∧
      letI := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
      Function.Injective (MulDistribMulAction.toMulAut acting critical) ∧
      (letI := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini critical);
        Function.Injective (MulDistribMulAction.toMulAut acting (critical ⧸ frattini critical))) ∧
      (IsCyclic (Subgroup.center critical) →
        letI := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center critical);
        Function.Injective (MulDistribMulAction.toMulAut acting (critical ⧸ Subgroup.center critical))) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨critical, hcharacteristic, hfrattini, hcommutator, hcentralizer⟩ :=
    pGroup_has_characteristic_critical_subgroup 2 hsource
  let : critical.Characteristic := hcharacteristic
  let : MulDistribMulAction acting critical := characteristic_subgroup_mulDistribMulAction critical
  have hcriticalCentralizer : Subgroup.centralizer (critical : Set source) ≤ critical := by
    rw [hcentralizer]
    exact Subgroup.map_subtype_le _
  have hcriticalAction := faithful_coprime_pGroup_action_on_characteristic_critical_subgroup
    prime 2 hodd hacting hsource critical hcriticalCentralizer hfaithful
  have hfrattiniCoprime : ¬ prime ∣ Nat.card (frattini critical) := by
    obtain ⟨exponent, hcard⟩ := ((hsource.to_subgroup critical).to_subgroup (frattini critical)).exists_card_eq
    rw [hcard]
    exact hprime.coprime_iff_not_dvd.mp
      (by simpa only [pow_one] using Nat.coprime_pow_primes 1 exponent hprime (by norm_num) hodd)
  refine ⟨critical, hcharacteristic, hfrattini, hcommutator, hcentralizer, hcriticalAction,
    faithful_coprime_pGroup_action_on_frattini_quotient prime hacting hfrattiniCoprime hcriticalAction, ?_⟩
  intro hcenter
  exact faithful_odd_pGroup_action_on_cyclic_center_quotient prime hprime hodd hacting
    (hsource.to_subgroup critical) hcenter hcriticalAction

theorem characteristic_critical_subgroup_nontrivial
    {source : Type u} [Group source] (critical : Subgroup source)
    (hsource : Nontrivial source)
    (hcentralizer : Subgroup.centralizer (critical : Set source) ≤ critical) : critical ≠ ⊥ := by
  let : Nontrivial source := hsource
  intro hbot
  have hcentralizerTop : Subgroup.centralizer (critical : Set source) = ⊤ := by
    apply Subgroup.centralizer_eq_top_iff_subset.mpr
    rw [hbot]
    intro member hmember
    rw [Subgroup.mem_bot.mp hmember]
    exact Subgroup.one_mem _
  rw [hcentralizerTop, hbot] at hcentralizer
  have hequal : (⊤ : Subgroup source) = ⊥ := le_antisymm hcentralizer bot_le
  exact top_ne_bot hequal

theorem critical_center_quotient_elementary
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (critical : Subgroup source)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype) :
    IsElemAbelian prime (⊤ : Subgroup (critical ⧸ Subgroup.center critical)) := by
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutator : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini prime (hsource.to_subgroup critical)).trans hfrattiniLocal
  let : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  refine ⟨inferInstance, ?_⟩
  intro member _
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center critical) member
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (hfrattiniLocal (pGroup_pow_mem_frattini prime (hsource.to_subgroup critical) lift))

theorem commutator_pow_two_eq_one_of_squares_central
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source)
    (first second : source) : ⁅first, second⁆ ^ 2 = 1 := by
  have hcentral : ⁅first, second⁆ ∈ Subgroup.center source :=
    hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second))
  have hcommute := Subgroup.mem_center_iff.mp hcentral first
  have hsquareCommute := Subgroup.mem_center_iff.mp (hsquares first) second
  have hsquareCommutator : ⁅first * first, second⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    simpa only [pow_two] using hsquareCommute.symm
  rw [commutatorElement_mul_left_eq_conj_mul] at hsquareCommutator
  have hconjugate : first * ⁅first, second⁆ * first⁻¹ = ⁅first, second⁆ := by
    rw [hcommute, mul_inv_cancel_right]
  rw [hconjugate] at hsquareCommutator
  simpa only [pow_two] using hsquareCommutator

theorem critical_twoGroup_commutators_in_centralTwoTorsion
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source) (critical : Subgroup source)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype) :
    ∀ first second : critical, ⁅first, second⁆ ∈ centralPrimeTorsion 2 critical := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutator : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini 2 (hsource.to_subgroup critical)).trans hfrattiniLocal
  have hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini 2 (hsource.to_subgroup critical) member)
  intro first second
  exact (mem_centralPrimeTorsion 2 _).mpr
    ⟨hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second)),
      commutator_pow_two_eq_one_of_squares_central hcommutator hsquares first second⟩

theorem critical_twoGroup_commutator_le_centralTwoTorsion
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source) (critical : Subgroup source)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype) :
    commutator critical ≤ centralPrimeTorsion 2 critical := by
  change ⁅(⊤ : Subgroup critical), (⊤ : Subgroup critical)⁆ ≤ centralPrimeTorsion 2 critical
  exact Subgroup.commutator_le.mpr fun first _ second _ =>
    critical_twoGroup_commutators_in_centralTwoTorsion hsource critical hfrattini first second

theorem centralPrimeTorsion_card_eq_prime_of_cyclic_center
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hcenter : IsCyclic (Subgroup.center source)) (hnontrivial : Nontrivial source) :
    Nat.card (centralPrimeTorsion prime source) = prime := by
  let : Nontrivial source := hnontrivial
  let : IsCyclic (Subgroup.center source) := hcenter
  have htorsionCenter : centralPrimeTorsion prime source ≤ Subgroup.center source := by
    intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).1
  let : IsCyclic (centralPrimeTorsion prime source) := Subgroup.isCyclic_of_le htorsionCenter
  have htorsionPow : ∀ member : centralPrimeTorsion prime source, member ^ prime = 1 := by
    intro member
    apply Subtype.ext
    exact ((mem_centralPrimeTorsion prime (member : source)).mp member.property).2
  have hcard := cyclic_group_of_prime_exponent_card_eq_one_or_prime prime htorsionPow
  apply hcard.resolve_left
  intro hcardOne
  have hnontrivialTop : (⊤ : Subgroup source) ≠ ⊥ := top_ne_bot
  have hnontrivialTorsion := pGroup_normal_subgroup_meets_centralPrimeTorsion
    prime hsource ⊤ hnontrivialTop
  apply hnontrivialTorsion
  rw [top_inf_eq]
  exact (centralPrimeTorsion prime source).eq_bot_iff_card.mpr hcardOne

theorem critical_twoGroup_cyclic_center_commutator_eq_centralTwoTorsion
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source) (critical : Subgroup source)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnoncommutative : ¬ IsMulCommutative critical) :
    commutator critical = centralPrimeTorsion 2 critical ∧ Nat.card (commutator critical) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hnontrivial : Nontrivial critical := by
    by_contra htrivial
    have hsubsingleton : Subsingleton critical := not_nontrivial_iff_subsingleton.mp htrivial
    let : Subsingleton critical := hsubsingleton
    exact hnoncommutative (IsMulCommutative.of_comm fun first second => Subsingleton.elim _ _)
  have htorsionCard := centralPrimeTorsion_card_eq_prime_of_cyclic_center 2
    (hsource.to_subgroup critical) hcenter hnontrivial
  have hcommutatorLe := critical_twoGroup_commutator_le_centralTwoTorsion hsource critical hfrattini
  let torsion := centralPrimeTorsion 2 critical
  let : Fact (Nat.card torsion).Prime := ⟨htorsionCard ▸ (by norm_num : Nat.Prime 2)⟩
  let commutatorLocal := (commutator critical).subgroupOf torsion
  have hcommutatorNontrivial : commutator critical ≠ ⊥ := fun hbot =>
    hnoncommutative ((commutator_eq_bot_iff critical).mp hbot)
  have hlocalNontrivial : commutatorLocal ≠ ⊥ := by
    intro hbot
    have hmap := Subgroup.map_subgroupOf_eq_of_le hcommutatorLe
    change commutatorLocal.map torsion.subtype = commutator critical at hmap
    rw [hbot, Subgroup.map_bot] at hmap
    exact hcommutatorNontrivial hmap.symm
  have hlocalTop : commutatorLocal = ⊤ := commutatorLocal.eq_bot_or_eq_top_of_prime_card.resolve_left hlocalNontrivial
  have hequal : commutator critical = torsion := by
    calc
      commutator critical = commutatorLocal.map torsion.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hcommutatorLe).symm
      _ = (⊤ : Subgroup torsion).map torsion.subtype := by rw [hlocalTop]
      _ = torsion := by rw [← MonoidHom.range_eq_map, torsion.range_subtype]
  exact ⟨hequal, hequal ▸ htorsionCard⟩

theorem class_two_center_quotient_commutator_pairing
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source) :
    letI : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
    ∃ pairing : (source ⧸ Subgroup.center source) →*
        (source ⧸ Subgroup.center source) →* Subgroup.center source,
      (∀ first second : source,
        (pairing ((QuotientGroup.mk' (Subgroup.center source)) first)
          ((QuotientGroup.mk' (Subgroup.center source)) second) : source) = ⁅first, second⁆) ∧
      (∀ member : source ⧸ Subgroup.center source, pairing member member = 1) ∧
      (∀ member : source ⧸ Subgroup.center source,
        (∀ other : source ⧸ Subgroup.center source, pairing member other = 1) → member = 1) := by
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  have hcentral : ∀ first second : source, ⁅first, second⁆ ∈ Subgroup.center source :=
    fun first second => hcommutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second))
  have hconjugate : ∀ first second scalar : source, scalar * ⁅first, second⁆ * scalar⁻¹ = ⁅first, second⁆ := by
    intro first second scalar
    rw [Subgroup.mem_center_iff.mp (hcentral first second) scalar, mul_inv_cancel_right]
  let base : source →* source →* Subgroup.center source :=
    { toFun := fun first =>
        { toFun := fun second => ⟨⁅first, second⁆, hcentral first second⟩
          map_one' := by apply Subtype.ext; simp
          map_mul' := fun second third => by
            apply Subtype.ext
            change ⁅first, second * third⁆ = ⁅first, second⁆ * ⁅first, third⁆
            rw [commutatorElement_mul_right_eq_mul_conj]
            calc
              _ = ⁅first, second⁆ * (second * ⁅first, third⁆ * second⁻¹) := by group
              _ = _ := by rw [hconjugate] }
      map_one' := by apply MonoidHom.ext; intro second; apply Subtype.ext; simp
      map_mul' := fun first second => by
        apply MonoidHom.ext
        intro third
        apply Subtype.ext
        change ⁅first * second, third⁆ = ⁅first, third⁆ * ⁅second, third⁆
        rw [commutatorElement_mul_left_eq_conj_mul, hconjugate,
          Subgroup.mem_center_iff.mp (hcentral second third) ⁅first, third⁆] }
  have hrightKernel : ∀ first : source, Subgroup.center source ≤ (base first).ker := by
    intro first second hsecond
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact Subgroup.mem_center_iff.mp hsecond first
  let rightLift : source →* (source ⧸ Subgroup.center source) →* Subgroup.center source :=
    { toFun := fun first => QuotientGroup.lift (Subgroup.center source) (base first) (hrightKernel first)
      map_one' := by
        apply MonoidHom.ext
        intro second
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
        change (QuotientGroup.lift (Subgroup.center source) (base 1) (hrightKernel 1))
          ((QuotientGroup.mk' (Subgroup.center source)) lift) = 1
        exact (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel 1) lift).trans
          (by rw [map_one, MonoidHom.one_apply])
      map_mul' := fun first second => by
        apply MonoidHom.ext
        intro third
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) third
        change (QuotientGroup.lift (Subgroup.center source) (base (first * second))
          (hrightKernel (first * second))) ((QuotientGroup.mk' (Subgroup.center source)) lift) =
          (QuotientGroup.lift (Subgroup.center source) (base first) (hrightKernel first))
            ((QuotientGroup.mk' (Subgroup.center source)) lift) *
          (QuotientGroup.lift (Subgroup.center source) (base second) (hrightKernel second))
            ((QuotientGroup.mk' (Subgroup.center source)) lift)
        exact (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel (first * second)) lift).trans
          ((by rw [map_mul, MonoidHom.mul_apply] : base (first * second) lift =
            base first lift * base second lift).trans (congrArg₂ (fun first second : Subgroup.center source =>
              first * second)
              (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel first) lift).symm
              (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel second) lift).symm)) }
  have hleftKernel : Subgroup.center source ≤ rightLift.ker := by
    intro first hfirst
    apply MonoidHom.ext
    intro second
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
    change (QuotientGroup.lift (Subgroup.center source) (base first) (hrightKernel first))
      ((QuotientGroup.mk' (Subgroup.center source)) lift) = 1
    apply (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel first) lift).trans
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hfirst lift).symm
  let pairing := QuotientGroup.lift (Subgroup.center source) rightLift hleftKernel
  have hpairing : ∀ first second : source,
      (pairing ((QuotientGroup.mk' (Subgroup.center source)) first)
        ((QuotientGroup.mk' (Subgroup.center source)) second) : source) = ⁅first, second⁆ := by
    intro first second
    have hleft : pairing ((QuotientGroup.mk' (Subgroup.center source)) first) = rightLift first :=
      QuotientGroup.lift_mk' (Subgroup.center source) hleftKernel first
    have hright : rightLift first ((QuotientGroup.mk' (Subgroup.center source)) second) = base first second :=
      QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel first) second
    rw [hleft, hright]
    rfl
  refine ⟨pairing, hpairing, ?_, ?_⟩
  · intro member
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) member
    apply Subtype.ext
    rw [hpairing, commutatorElement_self]
    rfl
  · intro member hradical
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) member
    apply (QuotientGroup.eq_one_iff lift).mpr
    apply Subgroup.mem_center_iff.mpr
    intro other
    have hequal := congrArg Subtype.val (hradical ((QuotientGroup.mk' (Subgroup.center source)) other))
    rw [hpairing] at hequal
    exact (commutatorElement_eq_one_iff_mul_comm.mp hequal).symm

theorem multiplicative_pairing_has_zmod_bilinear_map
    {source : Type u} {target : Type v} [CommGroup source] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] [Module (ZMod prime) (Additive target)]
    (pairing : source →* source →* target) :
    ∃ bilinear : Additive source →ₗ[ZMod prime] Additive source →ₗ[ZMod prime] Additive target,
      ∀ first second : source,
        bilinear (Additive.ofMul first) (Additive.ofMul second) = Additive.ofMul (pairing first second) := by
  let additive : Additive source →+ (Additive source →+ Additive target) :=
    { toFun := fun first => MonoidHom.toAdditive (pairing first.toMul)
      map_zero' := by
        apply AddMonoidHom.ext
        intro second
        change Additive.ofMul ((pairing 1) second.toMul) = 0
        rw [map_one, MonoidHom.one_apply]
        rfl
      map_add' := fun first second => by
        apply AddMonoidHom.ext
        intro third
        change Additive.ofMul ((pairing (first.toMul * second.toMul)) third.toMul) =
          Additive.ofMul (pairing first.toMul third.toMul) +
            Additive.ofMul (pairing second.toMul third.toMul)
        rw [map_mul, MonoidHom.mul_apply]
        rfl }
  let additiveLinear : Additive source →+ (Additive source →ₗ[ZMod prime] Additive target) :=
    (AddMonoidHom.toZModLinearMapEquiv prime).toAddMonoidHom.comp additive
  exact ⟨AddMonoidHom.toZModLinearMap prime additiveLinear, fun _ _ => rfl⟩

theorem class_two_binary_center_quotient_torsion_pairing
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source) :
    letI : IsMulCommutative (centralPrimeTorsion 2 source) := (centralPrimeTorsion_elementary 2).1
    letI : CommGroup (centralPrimeTorsion 2 source) := IsMulCommutative.instCommGroup
    ∃ pairing : (source ⧸ Subgroup.center source) →*
        (source ⧸ Subgroup.center source) →* centralPrimeTorsion 2 source,
      (∀ first second : source,
        (pairing ((QuotientGroup.mk' (Subgroup.center source)) first)
          ((QuotientGroup.mk' (Subgroup.center source)) second) : source) = ⁅first, second⁆) ∧
      (∀ member : source ⧸ Subgroup.center source, pairing member member = 1) ∧
      (∀ member : source ⧸ Subgroup.center source,
        (∀ other : source ⧸ Subgroup.center source, pairing member other = 1) → member = 1) := by
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  let : IsMulCommutative (centralPrimeTorsion 2 source) := (centralPrimeTorsion_elementary 2).1
  let : CommGroup (centralPrimeTorsion 2 source) := IsMulCommutative.instCommGroup
  obtain ⟨base, hbase, halt, hradical⟩ := class_two_center_quotient_commutator_pairing hcommutator
  have hbaseTorsion : ∀ first second : source ⧸ Subgroup.center source,
      (base first second : source) ∈ centralPrimeTorsion 2 source := by
    intro first second
    obtain ⟨firstLift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) first
    obtain ⟨secondLift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
    rw [hbase]
    exact (mem_centralPrimeTorsion 2 _).mpr
      ⟨hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top firstLift) (Subgroup.mem_top secondLift)),
        commutator_pow_two_eq_one_of_squares_central hcommutator hsquares firstLift secondLift⟩
  let pairing : (source ⧸ Subgroup.center source) →*
      (source ⧸ Subgroup.center source) →* centralPrimeTorsion 2 source :=
    { toFun := fun first => ((Subgroup.center source).subtype.comp (base first)).codRestrict
        (centralPrimeTorsion 2 source) (hbaseTorsion first)
      map_one' := by
        apply MonoidHom.ext
        intro second
        apply Subtype.ext
        change (base 1 second : source) = 1
        rw [map_one, MonoidHom.one_apply]
        rfl
      map_mul' := fun first second => by
        apply MonoidHom.ext
        intro third
        apply Subtype.ext
        change (base (first * second) third : source) =
          (base first third : source) * (base second third : source)
        rw [map_mul, MonoidHom.mul_apply]
        rfl }
  refine ⟨pairing, hbase, ?_, ?_⟩
  · intro member
    apply Subtype.ext
    change (base member member : source) = 1
    rw [halt]
    rfl
  · intro member hfixed
    apply hradical
    intro other
    apply Subtype.ext
    have hequal := congrArg Subtype.val (hfixed other)
    exact hequal

theorem prime_card_zmod_module_has_linear_equiv
    {space : Type u} [AddCommGroup space] [Finite space]
    (prime : ℕ) [Fact prime.Prime] [Module (ZMod prime) space]
    (hcard : Nat.card space = prime) :
    Nonempty (space ≃ₗ[ZMod prime] ZMod prime) := by
  let : Nontrivial space := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [hcard]; exact (Fact.out : prime.Prime).one_lt)
  obtain ⟨member, hnonzero⟩ := exists_ne (0 : space)
  obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_eq_one (ZMod prime) hnonzero
  have hsurjective : Function.Surjective functional := by
    intro value
    refine ⟨value • member, ?_⟩
    rw [map_smul, hfunctional, smul_eq_mul, mul_one]
  have hbijective : Function.Bijective functional :=
    (Nat.bijective_iff_surjective_and_card functional).mpr
      ⟨hsurjective, by simpa only [Nat.card_eq_fintype_card, ZMod.card] using hcard⟩
  exact ⟨LinearEquiv.ofBijective functional hbijective⟩

theorem multiplicative_pairing_has_nondegenerate_alternating_form
    {source : Type u} {target : Type v} [CommGroup source] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] [Module (ZMod prime) (Additive target)]
    (coordinate : Additive target ≃ₗ[ZMod prime] ZMod prime)
    (pairing : source →* source →* target)
    (halt : ∀ member : source, pairing member member = 1)
    (hradical : ∀ member : source, (∀ other : source, pairing member other = 1) → member = 1) :
    ∃ form : LinearMap.BilinForm (ZMod prime) (Additive source),
      form.IsAlt ∧ form.Nondegenerate ∧
        ∀ first second : source,
          form (Additive.ofMul first) (Additive.ofMul second) =
            coordinate (Additive.ofMul (pairing first second)) := by
  obtain ⟨bilinear, hbilinear⟩ := multiplicative_pairing_has_zmod_bilinear_map prime pairing
  let form : LinearMap.BilinForm (ZMod prime) (Additive source) :=
    ((LinearMap.llcomp (ZMod prime) (Additive source) (Additive target) (ZMod prime))
      coordinate.toLinearMap).comp bilinear
  have happly : ∀ first second : source,
      form (Additive.ofMul first) (Additive.ofMul second) =
        coordinate (Additive.ofMul (pairing first second)) := by
    intro first second
    change coordinate (bilinear (Additive.ofMul first) (Additive.ofMul second)) = _
    rw [hbilinear]
  have halternating : form.IsAlt := by
    intro member
    change form (Additive.ofMul member.toMul) (Additive.ofMul member.toMul) = 0
    rw [happly, halt]
    exact coordinate.map_zero
  have hleft : ∀ member : Additive source,
      (∀ other : Additive source, form member other = 0) → member = 0 := by
    intro member hfixed
    change member.toMul = 1
    apply hradical
    intro other
    have hequal := hfixed (Additive.ofMul other)
    change form (Additive.ofMul member.toMul) (Additive.ofMul other) = 0 at hequal
    rw [happly] at hequal
    exact coordinate.injective (hequal.trans coordinate.map_zero.symm)
  refine ⟨form, halternating, ⟨hleft, ?_⟩, happly⟩
  intro member hfixed
  apply hleft
  intro other
  exact halternating.eq_iff.mpr (hfixed other)

theorem class_two_center_quotient_pow_two_eq_one
    {source : Type u} [Group source]
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source)
    (member : source ⧸ Subgroup.center source) : member ^ 2 = 1 := by
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) member
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (lift ^ 2)).mpr (hsquares lift)

@[expose, instance_reducible]
def class_two_binary_center_quotient_module
    {source : Type u} [Group source] [IsMulCommutative (source ⧸ Subgroup.center source)]
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source) :
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    Module (ZMod 2) (Additive (source ⧸ Subgroup.center source)) := by
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  exact AddCommGroup.zmodModule (n := 2) (G := Additive (source ⧸ Subgroup.center source)) fun member => by
    change Additive.ofMul (member.toMul ^ 2) = 0
    rw [class_two_center_quotient_pow_two_eq_one hsquares]
    rfl

@[instance_reducible]
noncomputable def centralPrimeTorsion_zmod_module
    {source : Type u} [Group source] (prime : ℕ) :
    letI : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
    letI : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
    Module (ZMod prime) (Additive (centralPrimeTorsion prime source)) := by
  let : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
  let : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
  exact AddCommGroup.zmodModule fun member => by
    change member.toMul ^ prime = 1
    apply Subtype.ext
    exact (centralPrimeTorsion_elementary (source := source) prime).2
      member.toMul member.toMul.property

theorem cyclic_center_binary_quotient_has_nondegenerate_alternating_form
    {source : Type u} [Group source] [Finite source]
    [Fact (Nat.Prime 2)] (hsource : IsPGroup 2 source)
    (hcenter : IsCyclic (Subgroup.center source)) (hnontrivial : Nontrivial source)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (source ⧸ Subgroup.center source)),
      form.IsAlt ∧ form.Nondegenerate ∧
        ∃ coordinate : centralPrimeTorsion 2 source ≃* Multiplicative (ZMod 2),
          ∀ first second : source,
            form (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center source)) first))
              (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center source)) second)) =
                (coordinate ⟨⁅first, second⁆,
                  (mem_centralPrimeTorsion 2 _).mpr
                    ⟨hcommutator (Subgroup.commutator_mem_commutator
                        (Subgroup.mem_top first) (Subgroup.mem_top second)),
                      commutator_pow_two_eq_one_of_squares_central hcommutator hsquares first second⟩⟩).toAdd := by
  let : IsMulCommutative (source ⧸ Subgroup.center source) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  let : IsMulCommutative (centralPrimeTorsion 2 source) := (centralPrimeTorsion_elementary 2).1
  let : CommGroup (centralPrimeTorsion 2 source) := IsMulCommutative.instCommGroup
  let := centralPrimeTorsion_zmod_module (source := source) 2
  have hcard : Nat.card (Additive (centralPrimeTorsion 2 source)) = 2 :=
    (Nat.card_congr (Additive.ofMul : centralPrimeTorsion 2 source ≃
      Additive (centralPrimeTorsion 2 source))).symm.trans
        (centralPrimeTorsion_card_eq_prime_of_cyclic_center 2 hsource hcenter hnontrivial)
  obtain ⟨coordinate⟩ := prime_card_zmod_module_has_linear_equiv 2 hcard
  obtain ⟨pairing, hpairing, halt, hradical⟩ :=
    class_two_binary_center_quotient_torsion_pairing hcommutator hsquares
  obtain ⟨form, hformAlt, hformNondegenerate, hform⟩ :=
    multiplicative_pairing_has_nondegenerate_alternating_form 2 coordinate pairing halt hradical
  let multiplicativeCoordinate : centralPrimeTorsion 2 source ≃* Multiplicative (ZMod 2) :=
    MulEquiv.trans (MulEquiv.multiplicativeAdditive (centralPrimeTorsion 2 source)).symm
      (AddEquiv.toMultiplicative coordinate.toAddEquiv)
  refine ⟨form, hformAlt, hformNondegenerate, multiplicativeCoordinate, ?_⟩
  intro first second
  rw [hform]
  apply congrArg coordinate
  apply congrArg Additive.ofMul
  apply Subtype.ext
  exact hpairing first second

theorem cyclic_center_quotient_action_kernel_isPGroup
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (hsource : IsPGroup 2 source) (hcenter : IsCyclic (Subgroup.center source))
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
    IsPGroup 2 (MulDistribMulAction.toMulAut acting (source ⧸ Subgroup.center source)).ker := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
  let hom := MulDistribMulAction.toMulAut acting (source ⧸ Subgroup.center source)
  apply (isPGroup_iff_primeFactors_card_subset (by norm_num : 2 ≠ 0)).mpr
  intro prime hprimeFactor
  obtain ⟨hprime, hdivides, _⟩ := Nat.mem_primeFactors.mp hprimeFactor
  by_cases hequal : prime = 2
  · rw [hequal]
    norm_num
  let : Fact prime.Prime := ⟨hprime⟩
  let sylow : Sylow prime hom.ker := Classical.choice inferInstance
  have hfaithfulSylow : Function.Injective (MulDistribMulAction.toMulAut (sylow : Subgroup hom.ker) source) := by
    intro first second hequalAction
    apply Subtype.ext
    apply Subtype.ext
    apply hfaithful
    ext member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequalAction
  have hquotientFaithful := faithful_odd_pGroup_action_on_cyclic_center_quotient
    prime hprime hequal sylow.isPGroup' hsource hcenter hfaithfulSylow
  have hscalarTrivial : ∀ scalar : (sylow : Subgroup hom.ker), scalar = 1 := by
    intro scalar
    apply hquotientFaithful
    ext member
    have hequalAction : hom ((scalar : hom.ker) : acting) = 1 := (scalar : hom.ker).property
    have hfixed := congrArg
      (fun equivalence : MulAut (source ⧸ Subgroup.center source) => equivalence member) hequalAction
    change scalar • member = (1 : (sylow : Subgroup hom.ker)) • member
    rw [one_smul]
    exact hfixed
  have hcard : Nat.card (sylow : Subgroup hom.ker) = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, hscalarTrivial⟩
  have hprimeDivides := sylow.dvd_card_of_dvd_card hdivides
  rw [hcard] at hprimeDivides
  exact (hprime.ne_one (Nat.dvd_one.mp hprimeDivides)).elim

theorem pGroup_of_kernel_and_range
    {source : Type u} {target : Type v} [Group source] [Group target]
    (prime : ℕ) (hom : source →* target)
    (hkernel : IsPGroup prime hom.ker) (hrange : IsPGroup prime hom.range) :
    IsPGroup prime source := by
  have hkernelRestrict : IsPGroup prime hom.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkernel
  have htop : IsPGroup prime (⊤ : Subgroup source) := by
    have hgroup := (hrange.to_subgroup ⊤).comap_of_ker_isPGroup hom.rangeRestrict hkernelRestrict
    rw [Subgroup.comap_top] at hgroup
    exact hgroup
  exact htop.of_equiv Subgroup.topEquiv

theorem faithful_critical_restriction_action_kernel_isPGroup
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
    IsPGroup prime (MulDistribMulAction.toMulAut acting critical).ker := by
  let := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
  let hom := MulDistribMulAction.toMulAut acting critical
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : prime.Prime).ne_zero).mpr
  intro actingPrime hfactor
  obtain ⟨hactingPrime, hdivides, _⟩ := Nat.mem_primeFactors.mp hfactor
  by_cases hequal : actingPrime = prime
  · rw [hequal]
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : prime.Prime).ne_zero⟩
  let : Fact actingPrime.Prime := ⟨hactingPrime⟩
  let sylow : Sylow actingPrime hom.ker := Classical.choice inferInstance
  have hfaithfulSylow : Function.Injective (MulDistribMulAction.toMulAut (sylow : Subgroup hom.ker) source) := by
    intro first second hequalAction
    apply Subtype.ext
    apply Subtype.ext
    apply hfaithful
    ext member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequalAction
  have hcriticalFaithful := faithful_coprime_pGroup_action_on_characteristic_critical_subgroup
    actingPrime prime hequal sylow.isPGroup' hsource critical hcritical hfaithfulSylow
  have hscalarTrivial : ∀ scalar : (sylow : Subgroup hom.ker), scalar = 1 := by
    intro scalar
    apply hcriticalFaithful
    ext member
    have hequalAction : hom ((scalar : hom.ker) : acting) = 1 := (scalar : hom.ker).property
    have hfixed := congrArg (fun equivalence : MulAut critical => equivalence member) hequalAction
    change ((scalar • member : critical) : source) =
      (((1 : (sylow : Subgroup hom.ker)) • member : critical) : source)
    rw [one_smul]
    exact congrArg Subtype.val hfixed
  have hcard : Nat.card (sylow : Subgroup hom.ker) = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, hscalarTrivial⟩
  have hprimeDivides := sylow.dvd_card_of_dvd_card hdivides
  rw [hcard] at hprimeDivides
  exact (hactingPrime.ne_one (Nat.dvd_one.mp hprimeDivides)).elim

theorem pGroup_composite_hom_kernel
    {first : Type u} {second : Type v} {third : Type*}
    [Group first] [Group second] [Group third]
    (prime : ℕ) (firstHom : first →* second) (secondHom : second →* third)
    (hfirstKernel : IsPGroup prime firstHom.ker) (hsecondKernel : IsPGroup prime secondHom.ker) :
    IsPGroup prime (secondHom.comp firstHom).ker := by
  exact hsecondKernel.comap_of_ker_isPGroup firstHom hfirstKernel

theorem critical_restriction_action_kernel_isPGroup
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hkernel : IsPGroup prime (MulDistribMulAction.toMulAut acting source).ker) :
    letI := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
    IsPGroup prime (MulDistribMulAction.toMulAut acting critical).ker := by
  let sourceHom := MulDistribMulAction.toMulAut acting source
  let : MulDistribMulAction sourceHom.range source := inferInstance
  have hfaithfulRange : Function.Injective (MulDistribMulAction.toMulAut sourceHom.range source) := by
    intro first second hequal
    apply Subtype.ext
    apply MulEquiv.ext
    intro member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequal
  let := characteristic_subgroup_mulDistribMulAction (acting := sourceHom.range) critical
  let rangeHom := MulDistribMulAction.toMulAut sourceHom.range critical
  have hrangeKernel : IsPGroup prime rangeHom.ker :=
    faithful_critical_restriction_action_kernel_isPGroup prime hsource critical hcritical hfaithfulRange
  let := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
  have hcompose : rangeHom.comp sourceHom.rangeRestrict = MulDistribMulAction.toMulAut acting critical := by
    apply MonoidHom.ext
    intro scalar
    apply MulEquiv.ext
    intro member
    apply Subtype.ext
    rfl
  rw [← hcompose]
  apply pGroup_composite_hom_kernel prime sourceHom.rangeRestrict rangeHom
  · rw [MonoidHom.ker_rangeRestrict]
    exact hkernel
  · exact hrangeKernel

theorem cyclic_center_quotient_action_kernel_isPGroup_of_source_kernel
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (hsource : IsPGroup 2 source) (hcenter : IsCyclic (Subgroup.center source))
    (hkernel : IsPGroup 2 (MulDistribMulAction.toMulAut acting source).ker) :
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
    IsPGroup 2 (MulDistribMulAction.toMulAut acting (source ⧸ Subgroup.center source)).ker := by
  let sourceHom := MulDistribMulAction.toMulAut acting source
  let : MulDistribMulAction sourceHom.range source := inferInstance
  have hfaithfulRange : Function.Injective (MulDistribMulAction.toMulAut sourceHom.range source) := by
    intro first second hequal
    apply Subtype.ext
    apply MulEquiv.ext
    intro member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequal
  let := characteristic_quotient_mulDistribMulAction (acting := sourceHom.range) (Subgroup.center source)
  let rangeHom := MulDistribMulAction.toMulAut sourceHom.range (source ⧸ Subgroup.center source)
  have hrangeKernel : IsPGroup 2 rangeHom.ker :=
    cyclic_center_quotient_action_kernel_isPGroup hsource hcenter hfaithfulRange
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
  have hcompose : rangeHom.comp sourceHom.rangeRestrict =
      MulDistribMulAction.toMulAut acting (source ⧸ Subgroup.center source) := by
    apply MonoidHom.ext
    intro scalar
    apply MulEquiv.ext
    intro member
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) member
    rfl
  rw [← hcompose]
  apply pGroup_composite_hom_kernel 2 sourceHom.rangeRestrict rangeHom
  · rw [MonoidHom.ker_rangeRestrict]
    exact hkernel
  · exact hrangeKernel

theorem selfcentralizing_normal_conjugation_action_kernel_isPGroup
    {ambient : Type u} [Group ambient]
    (prime : ℕ) (normal : Subgroup ambient) [normal.Normal]
    (hnormal : IsPGroup prime normal)
    (hcentralizer : Subgroup.centralizer (normal : Set ambient) ≤ normal) :
    letI : MulDistribMulAction ambient normal :=
      MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
    IsPGroup prime (MulDistribMulAction.toMulAut ambient normal).ker := by
  let : MulDistribMulAction ambient normal :=
    MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
  apply hnormal.to_le
  intro scalar hscalar
  apply hcentralizer
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hequal := congrArg (fun equivalence : MulAut normal => equivalence (⟨member, hmember⟩ : normal))
    (show MulDistribMulAction.toMulAut ambient normal scalar = 1 from hscalar)
  have hfixed := congrArg Subtype.val hequal
  change scalar * member * scalar⁻¹ = member at hfixed
  have hmultiplied := congrArg (fun value : ambient => value * scalar) hfixed
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmultiplied.symm

theorem normal_subgroup_le_critical_center_quotient_action_kernel
    {ambient : Type u} [Group ambient]
    (normal : Subgroup ambient) [normal.Normal]
    (critical : Subgroup normal) [critical.Characteristic]
    (hcommutator : ⁅(⊤ : Subgroup normal), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype) :
    letI : MulDistribMulAction ambient normal :=
      MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
    letI := characteristic_subgroup_mulDistribMulAction (acting := ambient) critical
    letI := characteristic_quotient_mulDistribMulAction (acting := ambient) (Subgroup.center critical)
    normal ≤ (MulDistribMulAction.toMulAut ambient (critical ⧸ Subgroup.center critical)).ker := by
  let : MulDistribMulAction ambient normal :=
    MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
  let := characteristic_subgroup_mulDistribMulAction (acting := ambient) critical
  let := characteristic_quotient_mulDistribMulAction (acting := ambient) (Subgroup.center critical)
  intro scalar hscalar
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro member
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center critical) member
  change (QuotientGroup.mk' (Subgroup.center critical)) (scalar • lift) =
    (QuotientGroup.mk' (Subgroup.center critical)) lift
  have hcentral : ⁅(⟨scalar, hscalar⟩ : normal), (lift : normal)⁆ ∈
      (Subgroup.center critical).map critical.subtype :=
    hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) lift.property)
  obtain ⟨correction, hcorrection, hcorrectionEqual⟩ := hcentral
  have hequal : correction * lift = scalar • lift := by
    apply Subtype.ext
    apply Subtype.ext
    have hambient := congrArg Subtype.val hcorrectionEqual
    change (correction : ambient) = scalar * (lift : ambient) * scalar⁻¹ * (lift : ambient)⁻¹ at hambient
    change (correction : ambient) * (lift : ambient) = scalar * (lift : ambient) * scalar⁻¹
    rw [hambient]
    group
  have hcorrectionQuotient : (QuotientGroup.mk' (Subgroup.center critical)) correction = 1 :=
    (QuotientGroup.eq_one_iff correction).mpr hcorrection
  rw [← hequal, map_mul, hcorrectionQuotient, one_mul]

theorem critical_cyclic_center_conjugation_kernel_eq_twoCore
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hcentralizer : Subgroup.centralizer (pCore 2 ambient : Set ambient) ≤ pCore 2 ambient)
    (critical : Subgroup (pCore 2 ambient)) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set (pCore 2 ambient)) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup (pCore 2 ambient)), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) :
    letI : (pCore 2 ambient).Normal := pCore_normal 2
    letI : MulDistribMulAction ambient (pCore 2 ambient) :=
      MulDistribMulAction.compHom (pCore 2 ambient) (MulAut.conjNormal (H := pCore 2 ambient))
    letI := characteristic_subgroup_mulDistribMulAction (acting := ambient) critical
    letI := characteristic_quotient_mulDistribMulAction (acting := ambient) (Subgroup.center critical)
    (MulDistribMulAction.toMulAut ambient (critical ⧸ Subgroup.center critical)).ker = pCore 2 ambient := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : (pCore 2 ambient).Normal := pCore_normal 2
  let : MulDistribMulAction ambient (pCore 2 ambient) :=
    MulDistribMulAction.compHom (pCore 2 ambient) (MulAut.conjNormal (H := pCore 2 ambient))
  have hcoreKernel : IsPGroup 2 (MulDistribMulAction.toMulAut ambient (pCore 2 ambient)).ker :=
    selfcentralizing_normal_conjugation_action_kernel_isPGroup 2 (pCore 2 ambient)
      (pCore_isPGroup 2) hcentralizer
  let := characteristic_subgroup_mulDistribMulAction (acting := ambient) critical
  have hcriticalKernel : IsPGroup 2 (MulDistribMulAction.toMulAut ambient critical).ker :=
    critical_restriction_action_kernel_isPGroup 2 (pCore_isPGroup 2) critical hcritical hcoreKernel
  let := characteristic_quotient_mulDistribMulAction (acting := ambient) (Subgroup.center critical)
  let hom := MulDistribMulAction.toMulAut ambient (critical ⧸ Subgroup.center critical)
  have hquotientKernel : IsPGroup 2 hom.ker :=
    cyclic_center_quotient_action_kernel_isPGroup_of_source_kernel
      ((pCore_isPGroup 2).to_subgroup critical) hcenter hcriticalKernel
  apply le_antisymm
  · exact le_sSup ⟨(inferInstance : hom.ker.Normal), hquotientKernel⟩
  · exact normal_subgroup_le_critical_center_quotient_action_kernel (pCore 2 ambient) critical hcommutator

end CFSG.PreuniquenessRankFour.Helpers
