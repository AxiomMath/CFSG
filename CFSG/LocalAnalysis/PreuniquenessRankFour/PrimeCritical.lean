module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CharacteristicAbelian

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem class_two_commutator_pow_left
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source)
    (first second : source) (exponent : ℕ) :
    ⁅first ^ exponent, second⁆ = ⁅first, second⁆ ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent hinduction =>
    rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, hinduction]
    have hcentral := hcommutator (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top first) (Subgroup.mem_top second))
    have hconjugate : first ^ exponent * ⁅first, second⁆ * (first ^ exponent)⁻¹ =
        ⁅first, second⁆ := by
      rw [Subgroup.mem_center_iff.mp hcentral, mul_inv_cancel_right]
    rw [hconjugate, ← pow_succ', pow_succ]

theorem commutator_pow_prime_eq_one_of_powers_central
    {source : Type u} [Group source] (prime : ℕ)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hpowers : ∀ member : source, member ^ prime ∈ Subgroup.center source)
    (first second : source) : ⁅first, second⁆ ^ prime = 1 := by
  rw [← class_two_commutator_pow_left hcommutator]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact (Subgroup.mem_center_iff.mp (hpowers first) second).symm

@[instance_reducible]
def class_two_prime_center_quotient_module
    {source : Type u} [Group source] [IsMulCommutative (source ⧸ Subgroup.center source)]
    (prime : ℕ) (hpowers : ∀ member : source, member ^ prime ∈ Subgroup.center source) :
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    Module (ZMod prime) (Additive (source ⧸ Subgroup.center source)) := by
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  exact AddCommGroup.zmodModule fun member => by
    change member.toMul ^ prime = 1
    have hquotient : ∀ value : source ⧸ Subgroup.center source, value ^ prime = 1 := by
      intro value
      obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) value
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hpowers lift)
    exact hquotient member.toMul

theorem class_two_prime_center_quotient_torsion_pairing
    {source : Type u} [Group source] (prime : ℕ)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hpowers : ∀ member : source, member ^ prime ∈ Subgroup.center source) :
    letI : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
    letI : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
    ∃ pairing : (source ⧸ Subgroup.center source) →*
        (source ⧸ Subgroup.center source) →* centralPrimeTorsion prime source,
      (∀ first second : source,
        (pairing ((QuotientGroup.mk' (Subgroup.center source)) first)
          ((QuotientGroup.mk' (Subgroup.center source)) second) : source) = ⁅first, second⁆) ∧
      (∀ member : source ⧸ Subgroup.center source, pairing member member = 1) ∧
      (∀ member : source ⧸ Subgroup.center source,
        (∀ other : source ⧸ Subgroup.center source, pairing member other = 1) → member = 1) := by
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  let : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
  let : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
  obtain ⟨base, hbase, halt, hradical⟩ := class_two_center_quotient_commutator_pairing hcommutator
  have hbaseTorsion : ∀ first second : source ⧸ Subgroup.center source,
      (base first second : source) ∈ centralPrimeTorsion prime source := by
    intro first second
    obtain ⟨firstLift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) first
    obtain ⟨secondLift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
    rw [hbase]
    exact (mem_centralPrimeTorsion prime _).mpr
      ⟨hcommutator (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top firstLift) (Subgroup.mem_top secondLift)),
        commutator_pow_prime_eq_one_of_powers_central prime hcommutator hpowers firstLift secondLift⟩
  let pairing : (source ⧸ Subgroup.center source) →*
      (source ⧸ Subgroup.center source) →* centralPrimeTorsion prime source :=
    { toFun := fun first => ((Subgroup.center source).subtype.comp (base first)).codRestrict
        (centralPrimeTorsion prime source) (hbaseTorsion first)
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
    exact Subtype.ext (congrArg (fun value : centralPrimeTorsion prime source =>
      (value : source)) (hfixed other))

theorem cyclic_center_prime_quotient_has_nondegenerate_alternating_form
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hcenter : IsCyclic (Subgroup.center source)) (hnontrivial : Nontrivial source)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hpowers : ∀ member : source, member ^ prime ∈ Subgroup.center source) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_prime_center_quotient_module prime hpowers
    ∃ form : LinearMap.BilinForm (ZMod prime) (Additive (source ⧸ Subgroup.center source)),
      form.IsAlt ∧ form.Nondegenerate ∧
        ∃ coordinate : centralPrimeTorsion prime source ≃* Multiplicative (ZMod prime),
          ∀ first second : source,
            form (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center source)) first))
              (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center source)) second)) =
                (coordinate ⟨⁅first, second⁆,
                  (mem_centralPrimeTorsion prime _).mpr
                    ⟨hcommutator (Subgroup.commutator_mem_commutator
                        (Subgroup.mem_top first) (Subgroup.mem_top second)),
                      commutator_pow_prime_eq_one_of_powers_central
                        prime hcommutator hpowers first second⟩⟩).toAdd := by
  let : IsMulCommutative (source ⧸ Subgroup.center source) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  let := class_two_prime_center_quotient_module prime hpowers
  let : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
  let : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
  let := centralPrimeTorsion_zmod_module (source := source) prime
  have hcard : Nat.card (Additive (centralPrimeTorsion prime source)) = prime :=
    centralPrimeTorsion_card_eq_prime_of_cyclic_center prime hsource hcenter hnontrivial
  obtain ⟨coordinate⟩ := prime_card_zmod_module_has_linear_equiv prime hcard
  let multiplicativeCoordinate := AddEquiv.toMultiplicativeRight coordinate.toAddEquiv
  obtain ⟨pairing, hpairing, halt, hradical⟩ :=
    class_two_prime_center_quotient_torsion_pairing prime hcommutator hpowers
  obtain ⟨form, hformAlt, hformNondegenerate, hform⟩ :=
    multiplicative_pairing_has_nondegenerate_alternating_form
      prime coordinate pairing halt hradical
  refine ⟨form, hformAlt, hformNondegenerate, multiplicativeCoordinate, ?_⟩
  intro first second
  rw [hform]
  apply congrArg coordinate
  apply congrArg Additive.ofMul
  apply Subtype.ext
  exact hpairing first second

theorem scalar_commutator_has_prime_center_quotient_hom
    {source : Type u} [Group source] (prime : ℕ)
    (critical : Subgroup source) (scalar : source)
    (hcommutator : ∀ member : critical,
      ⁅scalar, (member : source)⁆ ∈ (Subgroup.center critical).map critical.subtype)
    (hpowers : ∀ member : critical, member ^ prime ∈ Subgroup.center critical)
    (hcentralizes : scalar ∈ Subgroup.centralizer
      ((Subgroup.center critical).map critical.subtype : Set source)) :
    ∃ hom : (critical ⧸ Subgroup.center critical) →* centralPrimeTorsion prime critical,
      ∀ member : critical,
        ((hom ((QuotientGroup.mk' (Subgroup.center critical)) member) : critical) : source) =
          ⁅scalar, (member : source)⁆ := by
  let raw : critical →* source :=
    { toFun := fun member => ⁅scalar, (member : source)⁆
      map_one' := commutatorElement_one_right scalar
      map_mul' := fun first second => by
        obtain ⟨correction, hcorrection, hequal⟩ := hcommutator second
        have hcommute := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcorrection) first)
        change (first : source) * (correction : source) =
          (correction : source) * (first : source) at hcommute
        change (correction : source) = ⁅scalar, (second : source)⁆ at hequal
        rw [hequal] at hcommute
        have hconjugate : (first : source) * ⁅scalar, (second : source)⁆ * (first : source)⁻¹ =
            ⁅scalar, (second : source)⁆ := by
          rw [hcommute, mul_inv_cancel_right]
        change ⁅scalar, (first : source) * (second : source)⁆ = _
        rw [commutatorElement_mul_right_eq_mul_conj]
        simpa only [mul_assoc] using
          congrArg (fun value : source => ⁅scalar, (first : source)⁆ * value) hconjugate }
  let base := raw.codRestrict critical fun member =>
    (Subgroup.map_subtype_le (Subgroup.center critical)) (hcommutator member)
  have hbaseTorsion : ∀ member : critical, base member ∈ centralPrimeTorsion prime critical := by
    intro member
    apply (mem_centralPrimeTorsion prime _).mpr
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_map_iff_mem Subtype.val_injective).mp (hcommutator member)
    · apply Subtype.ext
      change raw member ^ prime = 1
      rw [← map_pow]
      change ⁅scalar, ((member ^ prime : critical) : source)⁆ = 1
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact ((Subgroup.mem_centralizer_iff.mp hcentralizes) _
        (Subgroup.mem_map_of_mem critical.subtype (hpowers member))).symm
  let torsionHom := base.codRestrict (centralPrimeTorsion prime critical) hbaseTorsion
  have hkernel : Subgroup.center critical ≤ torsionHom.ker := by
    intro member hmember
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    apply Subtype.ext
    change ⁅scalar, (member : source)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (((Subgroup.mem_centralizer_iff.mp hcentralizes) _
        (Subgroup.mem_map_of_mem critical.subtype hmember)).symm)
  exact ⟨QuotientGroup.lift (Subgroup.center critical) torsionHom hkernel, fun _ => rfl⟩

theorem prime_critical_cyclic_center_centralizer_eq
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (critical : Subgroup source)
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    Subgroup.centralizer ((Subgroup.center critical).map critical.subtype : Set source) =
      critical := by
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutatorLocal : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini prime (hsource.to_subgroup critical)).trans hfrattiniLocal
  have hpowers : ∀ member : critical, member ^ prime ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini prime (hsource.to_subgroup critical) member)
  let : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  let : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
  let := class_two_prime_center_quotient_module prime hpowers
  obtain ⟨form, _, hnondegenerate, coordinate, hform⟩ :=
    cyclic_center_prime_quotient_has_nondegenerate_alternating_form
      prime (hsource.to_subgroup critical) hcenter hnontrivial hcommutatorLocal hpowers
  apply le_antisymm
  · intro scalar hscalar
    obtain ⟨hom, hhom⟩ := scalar_commutator_has_prime_center_quotient_hom prime critical scalar
      (fun member => hcommutator (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top scalar) member.property)) hpowers hscalar
    let : AddCommGroup (ZMod prime) := (ZMod.commRing prime).toAddCommGroup
    let functional : Module.Dual (ZMod prime) (Additive (critical ⧸ Subgroup.center critical)) :=
      AddMonoidHom.toZModLinearMap prime
        (MonoidHom.toAdditiveLeft (coordinate.toMonoidHom.comp hom))
    let vector := (form.toDual hnondegenerate).symm functional
    obtain ⟨representative, hrepresentative⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center critical) vector.toMul
    have hequal : ∀ member : critical, ⁅(representative : source), (member : source)⁆ =
        ⁅scalar, (member : source)⁆ := by
      intro member
      have hpairing : form (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center critical)) representative))
          (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center critical)) member)) =
            (coordinate (hom ((QuotientGroup.mk' (Subgroup.center critical)) member))).toAdd := by
        rw [hrepresentative]
        exact form.apply_toDual_symm_apply (hB := hnondegenerate) functional _
      rw [hform] at hpairing
      have hcoordinates : coordinate ⟨⁅representative, member⁆,
          (mem_centralPrimeTorsion prime _).mpr
            ⟨hcommutatorLocal (Subgroup.commutator_mem_commutator
                (Subgroup.mem_top representative) (Subgroup.mem_top member)),
              commutator_pow_prime_eq_one_of_powers_central
                prime hcommutatorLocal hpowers representative member⟩⟩ =
          coordinate (hom ((QuotientGroup.mk' (Subgroup.center critical)) member)) := hpairing
      have hvalues := congrArg (fun value : centralPrimeTorsion prime critical =>
        ((value : critical) : source)) (coordinate.injective hcoordinates)
      change ⁅(representative : source), (member : source)⁆ = _ at hvalues
      exact hvalues.trans (hhom member)
    have hdifference : (representative : source)⁻¹ * scalar ∈ critical := by
      apply hcritical
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have hcommutators := hequal (⟨member, hmember⟩ : critical)
      change (representative : source) * member * (representative : source)⁻¹ * member⁻¹ =
        scalar * member * scalar⁻¹ * member⁻¹ at hcommutators
      have hconjugations := congrArg (fun value : source => value * member) hcommutators
      have hfixed := congrArg (fun value : source =>
        (representative : source)⁻¹ * value * scalar) hconjugations
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hfixed
    simpa only [mul_inv_cancel_left] using critical.mul_mem representative.property hdifference
  · intro scalar hscalar
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    obtain ⟨lift, hlift, rfl⟩ := hmember
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hlift)
      (⟨scalar, hscalar⟩ : critical))).symm

theorem prime_critical_cyclic_center_quotient_embeds_center_aut
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    ∃ embedding : (source ⧸ critical) →* MulAut (Subgroup.center critical),
      Function.Injective embedding := by
  let center := (Subgroup.center critical).map critical.subtype
  let : center.Characteristic := inferInstance
  let : center.Normal := inferInstance
  let hom := MulAut.conjNormal (H := center)
  have hcentralizer : Subgroup.centralizer (center : Set source) = critical :=
    prime_critical_cyclic_center_centralizer_eq
      prime hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
  have hkernel : hom.ker = critical := by
    rw [← hcentralizer]
    ext scalar
    constructor
    · intro hscalar
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have hequal := congrArg (fun equivalence : MulAut center =>
        ((equivalence (⟨member, hmember⟩ : center)) : source))
        (MonoidHom.mem_ker.mp hscalar)
      change scalar * member * scalar⁻¹ = member at hequal
      have hmultiplied := congrArg (fun value : source => value * scalar) hequal
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmultiplied.symm
    · intro hscalar
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro member
      apply Subtype.ext
      change scalar * (member : source) * scalar⁻¹ = (member : source)
      rw [← (Subgroup.mem_centralizer_iff.mp hscalar) _ member.property,
        mul_inv_cancel_right]
  obtain ⟨embedding, hinjective, _⟩ := quotient_hom_injective_of_kernel_eq critical hom hkernel
  let centerEquiv := (Subgroup.center critical).equivMapOfInjective critical.subtype Subtype.val_injective
  exact ⟨(MulAut.congr centerEquiv.symm).toMonoidHom.comp embedding,
    (MulAut.congr centerEquiv.symm).injective.comp hinjective⟩

theorem odd_prime_critical_cyclic_center_quotient_isCyclic
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    IsCyclic (source ⧸ critical) := by
  let : IsCyclic (Subgroup.center critical) := hcenter
  let : IsCyclic (MulAut (Subgroup.center critical)) :=
    odd_cyclic_pGroup_mulAut_isCyclic prime hodd
      ((hsource.to_subgroup critical).to_subgroup (Subgroup.center critical))
  obtain ⟨embedding, hinjective⟩ := prime_critical_cyclic_center_quotient_embeds_center_aut
    prime hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
  exact isCyclic_of_injective embedding hinjective

theorem cyclic_characteristic_abelian_pGroup_has_cyclic_critical_quotient
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (habelian : ∀ abelian : Subgroup source, abelian.Characteristic →
      IsMulCommutative abelian → IsCyclic abelian) :
    ∃ critical : Subgroup source, ∃ hcharacteristic : critical.Characteristic,
      letI := hcharacteristic
      (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
      ⁅(⊤ : Subgroup source), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
      Subgroup.centralizer (critical : Set source) = (Subgroup.center critical).map critical.subtype ∧
      IsCyclic (Subgroup.center critical) ∧ IsCyclic (source ⧸ critical) := by
  obtain ⟨critical, hcharacteristic, hfrattini, hcommutator, hcentralizer⟩ :=
    pGroup_has_characteristic_critical_subgroup prime hsource
  let : critical.Characteristic := hcharacteristic
  let center := (Subgroup.center critical).map critical.subtype
  let : center.Characteristic := inferInstance
  have hcenterCommutative : IsMulCommutative center := IsMulCommutative.of_comm (by
    intro first second
    apply Subtype.ext
    obtain ⟨firstLift, hfirst, hfirsteq⟩ := first.property
    obtain ⟨secondLift, hsecond, hsecondeq⟩ := second.property
    change (first : source) * (second : source) = (second : source) * (first : source)
    rw [← hfirsteq, ← hsecondeq]
    exact congrArg (fun member : critical => (member : source))
      (Subgroup.mem_center_iff.mp hfirst secondLift).symm)
  have hcenterCyclic : IsCyclic (Subgroup.center critical) :=
    ((Subgroup.center critical).equivMapOfInjective critical.subtype Subtype.val_injective).isCyclic.mpr
      (habelian center (inferInstance : center.Characteristic) hcenterCommutative)
  have hquotientCyclic : IsCyclic (source ⧸ critical) := by
    by_cases htrivial : critical = ⊥
    · have htop : (⊤ : Subgroup source) ≤ critical := by
        have hfull : Subgroup.centralizer (critical : Set source) = ⊤ := by
          apply Subgroup.centralizer_eq_top_iff_subset.mpr
          intro member hmember
          rw [htrivial] at hmember
          rw [Subgroup.mem_bot.mp hmember]
          exact (Subgroup.center source).one_mem
        exact hfull.symm.le.trans (hcentralizer.le.trans (Subgroup.map_subtype_le _))
      have hequal : critical = ⊤ := top_unique htop
      let : Subsingleton (source ⧸ critical) := QuotientGroup.subsingleton_iff.mpr hequal
      exact inferInstance
    · exact odd_prime_critical_cyclic_center_quotient_isCyclic
        prime hodd hsource critical (by rw [hcentralizer]; exact Subgroup.map_subtype_le _)
        hcommutator hfrattini hcenterCyclic (critical.nontrivial_iff_ne_bot.mpr htrivial)
  exact ⟨critical, hcharacteristic, hfrattini, hcommutator, hcentralizer,
    hcenterCyclic, hquotientCyclic⟩

theorem escaping_primeCore_quotient_normal_pGroup_has_cyclic_critical_quotient
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup)) (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormal : IsPGroup prime normal) :
    ∃ critical : Subgroup normal, ∃ hcharacteristic : critical.Characteristic,
      letI := hcharacteristic
      (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
      ⁅(⊤ : Subgroup normal), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
      Subgroup.centralizer (critical : Set normal) = (Subgroup.center critical).map critical.subtype ∧
      IsCyclic (Subgroup.center critical) ∧ IsCyclic (normal ⧸ critical) := by
  let : Fact prime.Prime := ⟨hprime⟩
  apply cyclic_characteristic_abelian_pGroup_has_cyclic_critical_quotient prime hodd hnormal
  intro abelian hcharacteristic habelian
  let : abelian.Characteristic := hcharacteristic
  exact escaping_primeCore_quotient_normal_pGroup_characteristic_abelian_isCyclic
    prime hprime sylow hsylow hcore hrank hescape normal hnormal abelian habelian

end CFSG.PreuniquenessRankFour.Helpers
