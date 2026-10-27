module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm

public section

open CFSG.Open
open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem prime_card_two_group_action_trivial
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (hcard : Nat.card source = 2) :
    ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : IsCyclic source := isCyclic_of_prime_card hcard
  have hautCard : Nat.card (MulAut source) = 1 := by
    rw [IsCyclic.card_mulAut, hcard]
    norm_num
  have hsubsingleton : Subsingleton (MulAut source) :=
    (Nat.card_eq_one_iff_unique.mp hautCard).1
  intro scalar member
  exact congrArg (fun equivalence : MulAut source => equivalence member)
    (hsubsingleton.elim (MulDistribMulAction.toMulAut acting source scalar) 1)

theorem cyclic_center_binary_quotient_has_invariant_alternating_form
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    [Fact (Nat.Prime 2)] (hsource : IsPGroup 2 source)
    (hcenter : IsCyclic (Subgroup.center source)) (hnontrivial : Nontrivial source)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
    ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (source ⧸ Subgroup.center source)),
      form.IsAlt ∧ form.Nondegenerate ∧
        Even (Module.finrank (ZMod 2) (Additive (source ⧸ Subgroup.center source))) ∧
          ∀ scalar : acting, ∀ first second : source ⧸ Subgroup.center source,
            form (Additive.ofMul (scalar • first)) (Additive.ofMul (scalar • second)) =
              form (Additive.ofMul first) (Additive.ofMul second) := by
  let : IsMulCommutative (source ⧸ Subgroup.center source) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
  obtain ⟨form, hformAlt, hformNondegenerate, coordinate, hform⟩ :=
    cyclic_center_binary_quotient_has_nondegenerate_alternating_form
      hsource hcenter hnontrivial hcommutator hsquares
  refine ⟨form, hformAlt, hformNondegenerate,
    alternating_nondegenerate_form_finrank_even form hformAlt hformNondegenerate, ?_⟩
  let : (centralPrimeTorsion 2 source).Characteristic := centralPrimeTorsion_characteristic 2
  let := characteristic_subgroup_mulDistribMulAction (acting := acting) (centralPrimeTorsion 2 source)
  have htorsionCard : Nat.card (centralPrimeTorsion 2 source) = 2 :=
    centralPrimeTorsion_card_eq_prime_of_cyclic_center 2 hsource hcenter hnontrivial
  have hfixedTorsion := prime_card_two_group_action_trivial (acting := acting) htorsionCard
  intro scalar first second
  obtain ⟨firstLift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) first
  obtain ⟨secondLift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
  change form (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center source)) (scalar • firstLift)))
    (Additive.ofMul ((QuotientGroup.mk' (Subgroup.center source)) (scalar • secondLift))) = _
  rw [hform, hform]
  apply congrArg Multiplicative.toAdd
  apply congrArg coordinate
  apply Subtype.ext
  have htorsion : ⁅firstLift, secondLift⁆ ∈ centralPrimeTorsion 2 source :=
    (mem_centralPrimeTorsion 2 _).mpr
      ⟨hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)),
        commutator_pow_two_eq_one_of_squares_central hcommutator hsquares firstLift secondLift⟩
  have hfixed := congrArg Subtype.val (hfixedTorsion scalar ⟨⁅firstLift, secondLift⁆, htorsion⟩)
  change scalar • ⁅firstLift, secondLift⁆ = ⁅firstLift, secondLift⁆ at hfixed
  change ⁅scalar • firstLift, scalar • secondLift⁆ = ⁅firstLift, secondLift⁆
  have hcommutatorEquivariant :=
    map_commutatorElement (MulDistribMulAction.toMulAut acting source scalar) firstLift secondLift
  change scalar • ⁅firstLift, secondLift⁆ = ⁅scalar • firstLift, scalar • secondLift⁆ at hcommutatorEquivariant
  rw [← hcommutatorEquivariant]
  exact hfixed

@[expose] def multiplicative_action_zmod_linear_aut
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] :
    acting →* (Additive source ≃ₗ[ZMod prime] Additive source) where
  toFun scalar :=
    { toLinearMap := AddMonoidHom.toZModLinearMap prime
        (MonoidHom.toAdditive (MulDistribMulAction.toMulAut acting source scalar).toMonoidHom)
      invFun := fun member => Additive.ofMul (scalar⁻¹ • member.toMul)
      left_inv := fun member => by
        change Additive.ofMul (scalar⁻¹ • (scalar • member.toMul)) = member
        rw [inv_smul_smul]
        rfl
      right_inv := fun member => by
        change Additive.ofMul (scalar • (scalar⁻¹ • member.toMul)) = member
        rw [smul_inv_smul]
        rfl }
  map_one' := by
    apply LinearEquiv.ext
    intro member
    change Additive.ofMul ((1 : acting) • member.toMul) = member
    rw [one_smul]
    rfl
  map_mul' first second := by
    apply LinearEquiv.ext
    intro member
    change Additive.ofMul ((first * second) • member.toMul) =
      Additive.ofMul (first • (second • member.toMul))
    rw [mul_smul]

theorem multiplicative_action_zmod_linear_aut_kernel
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] :
    (multiplicative_action_zmod_linear_aut (acting := acting) (source := source) prime).ker =
      (MulDistribMulAction.toMulAut acting source).ker := by
  apply Subgroup.ext
  intro scalar
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hequal
    apply MulEquiv.ext
    intro member
    exact congrArg Additive.toMul
      (congrArg (fun equivalence : Additive source ≃ₗ[ZMod prime] Additive source =>
        equivalence (Additive.ofMul member)) hequal)
  · intro hequal
    apply LinearEquiv.ext
    intro member
    exact congrArg Additive.ofMul
      (congrArg (fun equivalence : MulAut source => equivalence member.toMul) hequal)

theorem faithful_multiplicative_action_zmod_linear_aut
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)]
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    Function.Injective (multiplicative_action_zmod_linear_aut (acting := acting) (source := source) prime) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [multiplicative_action_zmod_linear_aut_kernel]
  exact MonoidHom.ker_eq_bot _ hfaithful

theorem quotient_hom_injective_of_kernel_eq
    {source : Type u} {target : Type v} [Group source] [Group target]
    (normal : Subgroup source) [normal.Normal] (hom : source →* target)
    (hkernel : hom.ker = normal) :
    ∃ embedding : (source ⧸ normal) →* target,
      Function.Injective embedding ∧
        ∀ member : source, embedding ((QuotientGroup.mk' normal) member) = hom member := by
  let embedding := QuotientGroup.lift normal hom (le_of_eq hkernel.symm)
  have hinjective : Function.Injective embedding := by
    apply embedding.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_lift, hkernel]
    apply le_antisymm _ bot_le
    rintro member ⟨lift, hlift, rfl⟩
    exact (QuotientGroup.eq_one_iff lift).mpr hlift
  exact ⟨embedding, hinjective, fun member => QuotientGroup.lift_mk' normal (le_of_eq hkernel.symm) member⟩

theorem critical_cyclic_center_has_faithful_quotient_embedding
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hcentralizer : Subgroup.centralizer (pCore 2 ambient : Set ambient) ≤ pCore 2 ambient)
    (critical : Subgroup (pCore 2 ambient)) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set (pCore 2 ambient)) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup (pCore 2 ambient)), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical)
    (hcommutatorLocal : commutator critical ≤ Subgroup.center critical)
    (hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical) :
    letI : (pCore 2 ambient).Normal := pCore_normal 2
    letI : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
    letI : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (critical ⧸ Subgroup.center critical)),
      form.IsAlt ∧ form.Nondegenerate ∧
        Even (Module.finrank (ZMod 2) (Additive (critical ⧸ Subgroup.center critical))) ∧
          ∃ embedding : (ambient ⧸ pCore 2 ambient) →*
              (Additive (critical ⧸ Subgroup.center critical) ≃ₗ[ZMod 2]
                Additive (critical ⧸ Subgroup.center critical)),
            Function.Injective embedding ∧
              ∀ scalar : ambient ⧸ pCore 2 ambient,
                ∀ first second : Additive (critical ⧸ Subgroup.center critical),
                  form (embedding scalar first) (embedding scalar second) = form first second := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : (pCore 2 ambient).Normal := pCore_normal 2
  let : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  let : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  let : MulDistribMulAction ambient (pCore 2 ambient) :=
    MulDistribMulAction.compHom (pCore 2 ambient) (MulAut.conjNormal (H := pCore 2 ambient))
  let := characteristic_subgroup_mulDistribMulAction (acting := ambient) critical
  let := characteristic_quotient_mulDistribMulAction (acting := ambient) (Subgroup.center critical)
  obtain ⟨form, hformAlt, hformNondegenerate, heven, hinvariant⟩ :=
    cyclic_center_binary_quotient_has_invariant_alternating_form (acting := ambient)
      ((pCore_isPGroup 2).to_subgroup critical) hcenter hnontrivial hcommutatorLocal hsquares
  let actionHom := multiplicative_action_zmod_linear_aut
    (acting := ambient) (source := critical ⧸ Subgroup.center critical) 2
  have hkernel : actionHom.ker = pCore 2 ambient := by
    rw [multiplicative_action_zmod_linear_aut_kernel]
    exact critical_cyclic_center_conjugation_kernel_eq_twoCore
      hcentralizer critical hcritical hcommutator hcenter
  obtain ⟨embedding, hembedding, hembeddingApply⟩ :=
    quotient_hom_injective_of_kernel_eq (pCore 2 ambient) actionHom hkernel
  refine ⟨form, hformAlt, hformNondegenerate, heven, embedding, hembedding, ?_⟩
  intro scalar first second
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ambient) scalar
  rw [hembeddingApply]
  exact hinvariant lift first.toMul second.toMul

theorem twoCore_has_critical_with_conditional_symplectic_quotient
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hcentralizer : Subgroup.centralizer (pCore 2 ambient : Set ambient) ≤ pCore 2 ambient)
    (hcoreNontrivial : pCore 2 ambient ≠ ⊥) :
    ∃ critical : Subgroup (pCore 2 ambient), ∃ hcharacteristic : critical.Characteristic,
      letI := hcharacteristic
      critical ≠ ⊥ ∧
        (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
          ⁅(⊤ : Subgroup (pCore 2 ambient)), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
            Subgroup.centralizer (critical : Set (pCore 2 ambient)) =
              (Subgroup.center critical).map critical.subtype ∧
                (IsCyclic (Subgroup.center critical) →
                  ∃ hcommutator : commutator critical ≤ Subgroup.center critical,
                    ∃ hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical,
                      letI : (pCore 2 ambient).Normal := pCore_normal 2
                      letI : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
                        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
                      letI : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
                      letI := class_two_binary_center_quotient_module hsquares
                      ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (critical ⧸ Subgroup.center critical)),
                        form.IsAlt ∧ form.Nondegenerate ∧
                          Even (Module.finrank (ZMod 2) (Additive (critical ⧸ Subgroup.center critical))) ∧
                            ∃ embedding : (ambient ⧸ pCore 2 ambient) →*
                                (Additive (critical ⧸ Subgroup.center critical) ≃ₗ[ZMod 2]
                                  Additive (critical ⧸ Subgroup.center critical)),
                              Function.Injective embedding ∧
                                ∀ scalar : ambient ⧸ pCore 2 ambient,
                                  ∀ first second : Additive (critical ⧸ Subgroup.center critical),
                                    form (embedding scalar first) (embedding scalar second) = form first second) := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : Nontrivial (pCore 2 ambient) := Subgroup.nontrivial_iff_ne_bot _ |>.mpr hcoreNontrivial
  obtain ⟨critical, hcharacteristic, hfrattini, hcommutator, hselfcentralizer⟩ :=
    pGroup_has_characteristic_critical_subgroup (source := pCore 2 ambient) 2
      (pCore_isPGroup (G := ambient) 2)
  let : critical.Characteristic := hcharacteristic
  have hcenterLe : (Subgroup.center critical).map critical.subtype ≤ critical := Subgroup.map_subtype_le _
  have hselfcentralizing : Subgroup.centralizer (critical : Set (pCore 2 ambient)) ≤ critical :=
    hselfcentralizer.le.trans hcenterLe
  have hnontrivial : critical ≠ ⊥ :=
    characteristic_critical_subgroup_nontrivial critical inferInstance hselfcentralizing
  refine ⟨critical, hcharacteristic, hnontrivial, hfrattini, hcommutator, hselfcentralizer, ?_⟩
  intro hcyclic
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutatorLocal : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini 2 ((pCore_isPGroup 2).to_subgroup critical)).trans hfrattiniLocal
  have hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini 2 ((pCore_isPGroup 2).to_subgroup critical) member)
  refine ⟨hcommutatorLocal, hsquares, ?_⟩
  exact critical_cyclic_center_has_faithful_quotient_embedding hcentralizer critical hselfcentralizing
    hcommutator hcyclic (critical.nontrivial_iff_ne_bot.mpr hnontrivial) hcommutatorLocal hsquares

theorem charTwo_local_twoCore_selfcentralizing
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup) :
    Subgroup.centralizer (pCore 2 localGroup : Set localGroup) ≤ pCore 2 localGroup := by
  intro member hmember
  have hambient : (member : ambient) ∈ localGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set ambient) := by
    refine ⟨member.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro other hother
    obtain ⟨lift, hlift, rfl⟩ := hother
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hmember lift hlift)
  have hcore := hchar localGroup hlocal hambient
  exact (Subgroup.mem_map_iff_mem (f := localGroup.subtype) Subtype.val_injective).mp hcore

theorem charTwo_local_twoCore_nontrivial
    {ambient : Type u} [Group ambient] [Finite ambient]
    (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup) :
    pCore 2 localGroup ≠ ⊥ := by
  intro hbot
  apply twoLocal_pCoreOf_ne_bot hlocal
  change (pCore 2 localGroup).map localGroup.subtype = ⊥
  rw [hbot, Subgroup.map_bot]

end CFSG.PreuniquenessRankFour.Helpers
