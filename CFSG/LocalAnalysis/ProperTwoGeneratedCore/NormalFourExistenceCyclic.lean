module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistenceExtension
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut

public section

open CFSG.Open CFSG.LargeEvenClassification.Helpers

namespace CFSG.ProperTwoGeneratedCore

universe u v

theorem cyclic_scalar_transport {C : Type u} [Group C] {D : Type v} [Group D]
    (n : ℕ) (coordinates : Multiplicative (ZMod n) ≃* C)
    (equivalence : C ≃* D) (automorphism : MulAut C) :
    (cyclicScalarAutEquiv n (coordinates.trans equivalence))
      ((MulAut.congr equivalence) automorphism) =
        (cyclicScalarAutEquiv n coordinates) automorphism := by
  apply Units.ext
  have hfirst := cyclicScalarAutEquiv_apply n (coordinates.trans equivalence)
    ((MulAut.congr equivalence) automorphism) (Multiplicative.ofAdd (1 : ZMod n))
  have hsecond := cyclicScalarAutEquiv_apply n coordinates automorphism
    (Multiplicative.ofAdd (1 : ZMod n))
  have hleft : ((MulAut.congr equivalence) automorphism)
      ((coordinates.trans equivalence) (Multiplicative.ofAdd (1 : ZMod n))) =
        equivalence (automorphism (coordinates (Multiplicative.ofAdd (1 : ZMod n)))) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hleft] at hfirst
  change equivalence (automorphism (coordinates (Multiplicative.ofAdd (1 : ZMod n)))) =
    equivalence (coordinates (Multiplicative.ofAdd
      (((cyclicScalarAutEquiv n (coordinates.trans equivalence))
        ((MulAut.congr equivalence) automorphism) : ZMod n) * 1))) at hfirst
  change automorphism (coordinates (Multiplicative.ofAdd (1 : ZMod n))) =
    coordinates (Multiplicative.ofAdd
      (((cyclicScalarAutEquiv n coordinates) automorphism : ZMod n) * 1)) at hsecond
  rw [mul_one] at hfirst hsecond
  exact congrArg Multiplicative.toAdd
    (coordinates.injective (equivalence.injective
      (hfirst.symm.trans (congrArg equivalence hsecond))))

theorem cyclic_principal_action_normal_four {P : Type u} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] [IsCyclic H]
    (hcentralizer : Subgroup.centralizer (H : Set P) = H)
    (exponent : ℕ) (coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* H)
    (hin : binaryCongruenceInvolution exponent ∈
      ((cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := H))).range) :
    ∃ V : Subgroup P, V.Normal ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  let action := (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom.comp
    (MulAut.conjNormal (H := H))
  have hker : action.ker = H :=
    (MonoidHom.ker_comp_of_injective (MulAut.conjNormal (H := H))
      (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom
        (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).injective).trans
          ((conjNormal_ker_eq_centralizer H).trans hcentralizer)
  obtain ⟨x, hx⟩ := hin
  change action x = binaryCongruenceInvolution exponent at hx
  let Z := Subgroup.zpowers (binaryCongruenceInvolution exponent)
  have horder : orderOf (binaryCongruenceInvolution exponent) = 2 :=
    orderOf_eq_prime_iff.mpr
      ⟨binaryCongruenceInvolution_sq exponent, binaryCongruenceInvolution_ne_one exponent⟩
  have hZcard : Nat.card Z = 2 := (Nat.card_zpowers _).trans horder
  have hZle : Z ≤ action.range := (Subgroup.zpowers_le).mpr ⟨x, hx⟩
  let L := Z.comap action
  let : L.Normal := inferInstance
  have hHle : H ≤ L := hker ▸ Subgroup.ker_le_comap action Z
  let HL := H.subgroupOf L
  let : HL.Normal := inferInstance
  let equivalence : H ≃* HL := (Subgroup.subgroupOfEquivOfLe hHle).symm
  have hequivalence : ∀ t : H, ((equivalence t : L) : P) = (t : P) := by
    intro t
    rfl
  let : IsCyclic HL := equivalence.isCyclic.mp inferInstance
  let restricted := action.subgroupComap Z
  have hrestricted : Function.Surjective restricted := by
    intro z
    obtain ⟨p, hp⟩ := hZle z.property
    exact ⟨⟨p, by change action p ∈ Z; rw [hp]; exact z.property⟩, Subtype.ext hp⟩
  have hrestrictedKer : restricted.ker = HL := by
    ext l
    change restricted l = 1 ↔ (l : P) ∈ H
    rw [← hker]
    exact Subtype.ext_iff
  have hindex : HL.index = 2 := by
    rw [← hrestrictedKer, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hrestricted, Subgroup.card_top]
    exact hZcard
  have hxL : x ∈ L := by
    change action x ∈ Z
    rw [hx]
    exact Subgroup.mem_zpowers _
  let xl : L := ⟨x, hxL⟩
  have hxHL : xl ∉ HL := by
    intro hxH
    have hone : action x = 1 := hker.symm.le hxH
    exact binaryCongruenceInvolution_ne_one exponent (hx.symm.trans hone)
  have hconj : (MulAut.congr equivalence) (MulAut.conjNormal (H := H) x) =
      MulAut.conjNormal (H := HL) xl := by
    apply MulEquiv.ext
    intro t
    obtain ⟨original, rfl⟩ := equivalence.surjective t
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change ((equivalence ((MulAut.conjNormal (H := H) x) original) : L) : P) =
      x * ((equivalence original : L) : P) * x⁻¹
    rw [hequivalence, hequivalence]
    rfl
  have hscalar : (cyclicScalarAutEquiv (2 ^ (exponent + 3)) (coordinates.trans equivalence))
      (MulAut.conjNormal (H := HL) xl) = binaryCongruenceInvolution exponent := by
    rw [← hconj, cyclic_scalar_transport]
    exact hx
  obtain ⟨V, hVcharacteristic, hVelementary, hVcard, _⟩ :=
    principal_cyclic_extension_characteristic_four HL hindex exponent
      (coordinates.trans equivalence) xl hxHL hscalar
  let : V.Characteristic := hVcharacteristic
  refine ⟨V.map L.subtype, ConjAct.normal_of_characteristic_of_normal, ?_, ?_⟩
  · constructor
    · let : IsMulCommutative V := hVelementary.1
      infer_instance
    · intro p hp
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hp
      exact congrArg (fun l : L => (l : P)) (hVelementary.2 v hv)
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hVcard]

theorem cyclic_abelian_normal_self_centralizing_index_two
    {P : Type u} [Group P] [Finite P] (htwo : IsPGroup 2 P)
    (hcyclic : ∀ A : Subgroup P, A.Normal → IsMulCommutative A → IsCyclic A)
    (H : Subgroup P) [H.Normal] [IsCyclic H]
    (hcentralizer : Subgroup.centralizer (H : Set P) = H) : H.index ≤ 2 := by
  have hconjugationKernel : (MulAut.conjNormal (H := H)).ker = H :=
    (conjNormal_ker_eq_centralizer H).trans hcentralizer
  obtain ⟨normalRank, hnormalCard⟩ := (htwo.to_subgroup H).exists_card_eq
  by_cases hsmall : normalRank ≤ 2
  · have hautomorphismCard : Nat.card (MulAut H) ≤ 2 := by
      rw [IsCyclic.card_mulAut, hnormalCard]
      interval_cases normalRank
      · norm_num
      · norm_num
      · decide
    rw [← hconjugationKernel, Subgroup.index_ker]
    exact (MulAut.conjNormal (H := H)).range.card_le_card_group.trans hautomorphismCard
  · obtain ⟨exponent, hrankEq⟩ : ∃ exponent, normalRank = exponent + 3 :=
      ⟨normalRank - 3, by omega⟩
    rw [hrankEq] at hnormalCard
    let coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* H := by
      rw [← hnormalCard]
      exact zmodCyclicMulEquiv (inferInstance : IsCyclic H)
    let action := (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := H))
    have hexcludes : binaryCongruenceInvolution exponent ∉ action.range := by
      intro hin
      obtain ⟨V, hVnormal, hVelementary, hVcard⟩ :=
        cyclic_principal_action_normal_four H hcentralizer exponent coordinates hin
      let : IsCyclic V := hcyclic V hVnormal hVelementary.1
      let : CommGroup V := IsCyclic.commGroup
      have hexponent : Monoid.exponent V ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one (fun v : V =>
          Subtype.ext (hVelementary.2 v v.property))
      rw [IsCyclic.exponent_eq_card, hVcard] at hexponent
      norm_num at hexponent
    let divides : 4 ∣ 2 ^ (exponent + 3) := by
      rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
      exact dvd_mul_right _ _
    let reduction := ZMod.unitsMap divides
    have hdisjoint : Disjoint action.range reduction.ker :=
      binary_congruence_subgroup_excludes_involution action.range hexcludes
    let restricted := reduction.comp action.range.subtype
    have hrestrictedInjective : Function.Injective restricted := by
      apply (MonoidHom.ker_eq_bot_iff restricted).mp
      apply le_antisymm _ bot_le
      intro scalar hscalar
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hdisjoint scalar.property hscalar
    have hcardRange : Nat.card action.range ≤ 2 := by
      have hbound := Nat.card_le_card_of_injective restricted hrestrictedInjective
      have htargetCard : Nat.card (ZMod 4)ˣ = 2 := by
        rw [Nat.card_eq_fintype_card]
        decide
      exact hbound.trans_eq htargetCard
    have hactionKernel : action.ker = H :=
      (MonoidHom.ker_comp_of_injective (MulAut.conjNormal (H := H))
        (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom
          (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).injective).trans
            hconjugationKernel
    rw [← hactionKernel, Subgroup.index_ker]
    exact hcardRange

theorem cyclic_abelian_normal_index_two (P : Type u) [Group P] [Finite P]
    (htwo : IsPGroup 2 P)
    (hcyclic : ∀ A : Subgroup P, A.Normal → IsMulCommutative A → IsCyclic A) :
    ∃ H : Subgroup P, H.Normal ∧ IsCyclic H ∧ H.index ≤ 2 := by
  have hbot : (⊥ : Subgroup P).Normal ∧ IsMulCommutative (⊥ : Subgroup P) :=
    ⟨inferInstance, inferInstance⟩
  obtain ⟨H, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun H : Subgroup P => H.Normal ∧ IsMulCommutative H) hbot
  obtain ⟨hnormal, hcommutative⟩ := hmaximal.prop
  let : H.Normal := hnormal
  let : IsCyclic H := hcyclic H hnormal hcommutative
  have hcentralizer := maximal_abelian_normal_selfCentralizing Nat.prime_two htwo H
    hcommutative (fun A hAnormal hAcommutative hHA =>
      hmaximal.2 ⟨hAnormal, hAcommutative⟩ hHA)
  exact ⟨H, hnormal, inferInstance,
    cyclic_abelian_normal_self_centralizing_index_two htwo hcyclic H hcentralizer⟩

end CFSG.ProperTwoGeneratedCore
