module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSymplectic

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem scalar_commutator_has_binary_center_quotient_hom
    {source : Type u} [Group source]
    (critical : Subgroup source) (scalar : source)
    (hcommutator : ∀ member : critical,
      ⁅scalar, (member : source)⁆ ∈ (Subgroup.center critical).map critical.subtype)
    (hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical)
    (hcentralizes : scalar ∈ Subgroup.centralizer
      ((Subgroup.center critical).map critical.subtype : Set source)) :
    ∃ hom : (critical ⧸ Subgroup.center critical) →* centralPrimeTorsion 2 critical,
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
  have hbaseTorsion : ∀ member : critical, base member ∈ centralPrimeTorsion 2 critical := by
    intro member
    apply (mem_centralPrimeTorsion 2 _).mpr
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_map_iff_mem Subtype.val_injective).mp (hcommutator member)
    · apply Subtype.ext
      change raw member ^ 2 = 1
      rw [← map_pow]
      change ⁅scalar, ((member ^ 2 : critical) : source)⁆ = 1
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact ((Subgroup.mem_centralizer_iff.mp hcentralizes) _
        (Subgroup.mem_map_of_mem critical.subtype (hsquares member))).symm
  let torsionHom := base.codRestrict (centralPrimeTorsion 2 critical) hbaseTorsion
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

theorem critical_cyclic_center_centralizer_eq
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source)
    (critical : Subgroup source)
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    Subgroup.centralizer ((Subgroup.center critical).map critical.subtype : Set source) =
      critical := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutatorLocal : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini 2 (hsource.to_subgroup critical)).trans hfrattiniLocal
  have hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini 2 (hsource.to_subgroup critical) member)
  let : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  let : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  obtain ⟨form, _, hnondegenerate, coordinate, hform⟩ :=
    cyclic_center_binary_quotient_has_nondegenerate_alternating_form
      (hsource.to_subgroup critical) hcenter hnontrivial hcommutatorLocal hsquares
  apply le_antisymm
  · intro scalar hscalar
    obtain ⟨hom, hhom⟩ := scalar_commutator_has_binary_center_quotient_hom critical scalar
      (fun member => hcommutator (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top scalar) member.property)) hsquares hscalar
    let : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
    let functional : Module.Dual (ZMod 2) (Additive (critical ⧸ Subgroup.center critical)) :=
      AddMonoidHom.toZModLinearMap 2 (M₁ := ZMod 2)
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
          (mem_centralPrimeTorsion 2 _).mpr
            ⟨hcommutatorLocal (Subgroup.commutator_mem_commutator
                (Subgroup.mem_top representative) (Subgroup.mem_top member)),
              commutator_pow_two_eq_one_of_squares_central
                hcommutatorLocal hsquares representative member⟩⟩ =
          coordinate (hom ((QuotientGroup.mk' (Subgroup.center critical)) member)) := hpairing
      have hvalues := congrArg (fun value : centralPrimeTorsion 2 critical =>
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

theorem critical_cyclic_center_quotient_embeds_center_aut
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source)
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
    critical_cyclic_center_centralizer_eq hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
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

theorem critical_cyclic_center_quotient_isMulCommutative
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    IsMulCommutative (source ⧸ critical) := by
  let : IsCyclic (Subgroup.center critical) := hcenter
  obtain ⟨embedding, hinjective⟩ := critical_cyclic_center_quotient_embeds_center_aut
    hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
  let hom := (IsCyclic.mulAutMulEquiv (Subgroup.center critical)).toMonoidHom.comp embedding
  apply IsMulCommutative.of_comm
  intro first second
  apply ((IsCyclic.mulAutMulEquiv (Subgroup.center critical)).injective.comp hinjective)
  change hom (first * second) = hom (second * first)
  rw [map_mul, map_mul, mul_comm]

theorem critical_cyclic_center_index_dvd_center_totient
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    critical.index ∣ (Nat.card (Subgroup.center critical)).totient := by
  let : IsCyclic (Subgroup.center critical) := hcenter
  obtain ⟨embedding, hinjective⟩ := critical_cyclic_center_quotient_embeds_center_aut
    hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
  have hcard : Nat.card embedding.range = Nat.card (source ⧸ critical) :=
    Nat.card_congr (MonoidHom.ofInjective hinjective).toEquiv.symm
  have hdivides := embedding.range.card_subgroup_dvd_card
  rw [hcard, IsCyclic.card_mulAut, ← critical.index_eq_card] at hdivides
  exact hdivides

end CFSG.PreuniquenessRankFour.Helpers
