module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixed
public import Certificates.Certificate11002

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

section General

variable {G : Type*} [Group G]

@[expose] def FusionData (γ : MulAut G) (D W : Subgroup G) (r s z h : G) : Prop :=
  D = ⁅fixSub γ, fixSub γ⁆ ∧ ⁅D, D⁆ = D ∧ Nat.card D = 60 ∧
  orderOf z = 2 ∧ z ∈ Subgroup.centralizer (D : Set G) ∧ z ∉ D ∧
  W = Subgroup.closure {r, s} ∧ W ≤ D ∧ Nat.card W = 4 ∧
  r ≠ 1 ∧ s ≠ 1 ∧ r ≠ s ∧ (∀ w ∈ W, w ^ 2 = 1) ∧ (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧
  (∃ P : Sylow 2 D, (P : Subgroup D) = W.subgroupOf D) ∧
  (∀ d ∈ D, orderOf d = 2 → ∃ c ∈ D, d = c * r * c⁻¹) ∧
  Nat.card {d : D // orderOf d = 2} = 15 ∧
  h * z * h⁻¹ = z * r

theorem exists_sylow_of_card {D W : Subgroup G} (hWD : W ≤ D) (hW : Nat.card W = 4)
    (hD : Nat.card D = 60) : ∃ P : Sylow 2 D, (P : Subgroup D) = W.subgroupOf D := by
  have hc : Nat.card (W.subgroupOf D) = 4 := by
    rw [← hW]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWD).toEquiv
  have hp : IsPGroup 2 (W.subgroupOf D) := IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)
  have hi : (W.subgroupOf D).index = 15 := by
    have h := (W.subgroupOf D).card_mul_index
    rw [hc, hD] at h
    omega
  exact ⟨hp.toSylow (by rw [hi]; norm_num), hp.toSylow_coe _⟩

theorem fixSub_conj (α γ : MulAut G) :
    fixSub (α * γ * α⁻¹) = (fixSub γ).map α.toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub]
  simp only [MulAut.mul_apply, MulAut.inv_def]
  constructor
  · intro h
    apply α.injective
    rw [MulEquiv.apply_symm_apply, h]
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem FusionData.map {γ : MulAut G} {D W : Subgroup G} {r s z h : G}
    (hF : FusionData γ D W r s z h) (α : MulAut G) :
    FusionData (α * γ * α⁻¹) (D.map α.toMonoidHom) (W.map α.toMonoidHom) (α r) (α s) (α z)
      (α h) := by
  obtain ⟨hD, hDD, hD60, hz2, hzc, hzD, hW, hWD, hW4, hr1, hs1, hrs, hWsq, hWc, -, hinv, h15,
    hh⟩ := hF
  have hinj : Function.Injective α.toMonoidHom := α.injective
  have hD60' : Nat.card (D.map α.toMonoidHom) = 60 := by
    rw [Subgroup.card_map_of_injective hinj, hD60]
  have hW4' : Nat.card (W.map α.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective hinj, hW4]
  have hWD' : W.map α.toMonoidHom ≤ D.map α.toMonoidHom := Subgroup.map_mono hWD
  refine ⟨?_, ?_, hD60', ?_, ?_, ?_, ?_, hWD', hW4', ?_, ?_, ?_, ?_, ?_,
    exists_sylow_of_card hWD' hW4' hD60', ?_, ?_, ?_⟩
  · rw [fixSub_conj, ← Subgroup.map_commutator, hD]
  · rw [← Subgroup.map_commutator, hDD]
  · rw [MulEquiv.orderOf_eq, hz2]
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hzc
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hzc d hd]
  · intro hm
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hm
    exact hzD hm
  · rw [hW, MonoidHom.map_closure, Set.image_pair]
    rfl
  · exact fun h1 => hr1 (α.injective (by rw [h1, map_one]))
  · exact fun h1 => hs1 (α.injective (by rw [h1, map_one]))
  · exact fun h1 => hrs (α.injective h1)
  · rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hWsq w hw, map_one]
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hWc w hw w' hw']
  · rintro _ ⟨d, hd, rfl⟩ hd2
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hd2
    obtain ⟨c, hc, rfl⟩ := hinv d hd hd2
    exact ⟨α c, ⟨c, hc, rfl⟩, by simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]⟩
  · rw [← h15]
    refine (Nat.card_congr ?_).symm
    exact (D.equivMapOfInjective α.toMonoidHom hinj).toEquiv.subtypeEquiv fun d => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.orderOf_eq]
  · rw [← map_inv, ← map_mul, ← map_mul, hh, map_mul]

end General

theorem permR_apply : ∀ i, permR i = ![0, 1, 10, 5, 8, 3, 11, 7, 4, 9, 2, 6] i :=
  Certificates.certificate11002.1

theorem permS_apply : ∀ i, permS i = ![1, 0, 2, 3, 8, 5, 11, 9, 4, 7, 10, 6] i :=
  Certificates.certificate11002.2.1

theorem permR_mem : permR ∈ fixedDQ.originalSubgroup := fourGroupPerm_le 0
  (Subgroup.subset_closure (Set.mem_insert _ _))

theorem permS_mem : permS ∈ fixedDQ.originalSubgroup := fourGroupPerm_le 0
  (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

@[expose] def elemR : NativeSporadic.M12 := ⟨permR, fixedDQ_le permR_mem⟩

@[expose] def elemS : NativeSporadic.M12 := ⟨permS, fixedDQ_le permS_mem⟩

theorem permH_word : permH = m12gA * m12gB * m12gB * m12gA * m12gB * m12gA * m12gB * m12gB *
    m12gA * m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB :=
  Certificates.certificate11002.2.2.1

theorem permH_word_list : permH = ([1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2].map
    fun k : ℕ => if k = 1 then m12gA else m12gB).prod :=
  Certificates.certificate11002.2.2.2.1

theorem permH_apply : ∀ i, permH i = ![3, 6, 2, 5, 0, 7, 11, 4, 8, 10, 1, 9] i :=
  Certificates.certificate11002.2.2.2.2.1

theorem permH_mem : permH ∈ NativeSporadic.M12 := by
  rw [permH_word_list]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  split_ifs
  · exact m12a.2
  · exact m12b.2

@[expose] def elemH : NativeSporadic.M12 := ⟨permH, permH_mem⟩

theorem permH_word_pow : permH = m12gA * m12gB ^ 2 * m12gA * m12gB * m12gA * m12gB ^ 2 * m12gA *
    m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB :=
  Certificates.certificate11002.2.2.2.2.2.1

theorem elemH_word : elemH = m12a * m12b ^ 2 * m12a * m12b * m12a * m12b ^ 2 * m12a * m12b *
    m12a * m12b * m12a * m12b * m12a * m12b := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
  exact permH_word_pow

theorem permH_conj : permH * permZ * permH⁻¹ = permZ * permR :=
  Certificates.certificate11002.2.2.2.2.2.2

@[expose] def fusionW : Subgroup NativeSporadic.M12 := Subgroup.closure {elemR, elemS}

theorem fusionW_eq : fusionW = fourGroup 0 := by
  apply Subgroup.map_injective NativeSporadic.M12.subtype_injective
  rw [fourGroup_map, fusionW, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem elemR_ne : elemR ≠ 1 ∧ elemS ≠ 1 ∧ elemR ≠ elemS := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun g : NativeSporadic.M12 => (g : Equiv.Perm (Fin 12)) 2) h
    change permR 2 = (1 : Equiv.Perm (Fin 12)) 2 at this
    exact absurd this (by decide +kernel)
  · have := congrArg (fun g : NativeSporadic.M12 => (g : Equiv.Perm (Fin 12)) 0) h
    change permS 0 = (1 : Equiv.Perm (Fin 12)) 0 at this
    exact absurd this (by decide +kernel)
  · have := congrArg (fun g : NativeSporadic.M12 => (g : Equiv.Perm (Fin 12)) 0) h
    change permR 0 = permS 0 at this
    exact absurd this (by decide +kernel)

theorem fixedD_involution_conj : ∀ d ∈ fixedD, orderOf d = 2 →
    ∃ c ∈ fixedD, d = c * elemR * c⁻¹ := by
  intro d hd hd2
  have h2 : (d : Equiv.Perm (Fin 12)) ^ 2 = 1 := by
    rw [← SubgroupClass.coe_pow, ← hd2, pow_orderOf_eq_one, OneMemClass.coe_one]
  have h1 : (d : Equiv.Perm (Fin 12)) ≠ 1 := by
    intro h
    have : d = 1 := Subtype.ext h
    rw [this, orderOf_one] at hd2
    omega
  obtain ⟨c, hc, hdc⟩ := exists_conj_permR (mem_fixedD.1 hd) h2 h1
  refine ⟨⟨c, fixedDQ_le hc⟩, mem_fixedD.2 hc, Subtype.ext ?_⟩
  exact hdc

theorem card_fixedD_involutions : Nat.card {d : fixedD // orderOf d = 2} = 15 := by
  rw [← checkCount_spec.1]
  refine card_eq_length _ (fun d : fixedD => ((d : NativeSporadic.M12) : Equiv.Perm (Fin 12)))
    (fun a b hab => Subtype.ext (Subtype.ext hab)) _
    ((enumeration_nodup fixedDQ fixedDQ_valid).filter _) fun g => ?_
  simp only [involutionsOf, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    schreierPermEq_eq_true_iff, mem_enum_fixedDQ]
  constructor
  · rintro ⟨hg, hg2, hg1⟩
    refine ⟨⟨⟨g, fixedDQ_le hg⟩, mem_fixedD.2 hg⟩, ?_, rfl⟩
    have h1 : g ≠ 1 := fun h => by rw [h] at hg1; exact absurd hg1 (by decide)
    have : orderOf g = 2 := orderOf_eq_prime hg2 h1
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact this
  · rintro ⟨d, hd2, rfl⟩
    have h2 : orderOf ((d : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hd2
    refine ⟨mem_fixedD.1 d.2, by rw [← h2, pow_orderOf_eq_one], ?_⟩
    apply Bool.eq_false_iff.2
    intro h
    rw [schreierPermEq_eq_true_iff] at h
    rw [h, orderOf_one] at h2
    omega

theorem fusionData_pinned : FusionData beta fixedD fusionW elemR elemS elemZ elemH := by
  have hW4 : Nat.card fusionW = 4 := by rw [fusionW_eq, card_fourGroup]
  have hWD : fusionW ≤ fixedD := by rw [fusionW_eq]; exact fourGroup_le 0
  obtain ⟨hr1, hs1, hrs⟩ := elemR_ne
  refine ⟨fixedD_eq_commutator, fixedD_perfect, card_fixedD, orderOf_elemZ, ?_, elemZ_not_mem,
    rfl, hWD, hW4, hr1, hs1, hrs, ?_, ?_, exists_sylow_of_card hWD hW4 card_fixedD,
    fixedD_involution_conj, card_fixedD_involutions, Subtype.ext permH_conj⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (elemZ_comm_fixedD d hd).symm
  · rw [fusionW_eq]
    exact (fourGroup_elementary 0).1
  · rw [fusionW_eq]
    exact (fourGroup_elementary 0).2

theorem ctss_m12_pinned_central_involution_fusion_for_fixed_section :
    (∀ i, permR i = ![0, 1, 10, 5, 8, 3, 11, 7, 4, 9, 2, 6] i) ∧
    (∀ i, permS i = ![1, 0, 2, 3, 8, 5, 11, 9, 4, 7, 10, 6] i) ∧
    (∀ i, permH i = ![3, 6, 2, 5, 0, 7, 11, 4, 8, 10, 1, 9] i) ∧
    elemH = m12a * m12b ^ 2 * m12a * m12b * m12a * m12b ^ 2 * m12a * m12b * m12a * m12b *
      m12a * m12b * m12a * m12b ∧
    permH = ([1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2].map
      fun k : ℕ => if k = 1 then m12gA else m12gB).prod ∧
    FusionData beta fixedD fusionW elemR elemS elemZ elemH ∧
    ∀ g : NativeSporadic.M12,
      FusionData (MulAut.conj g * beta * (MulAut.conj g)⁻¹)
        (fixedD.map (MulAut.conj g).toMonoidHom) (fusionW.map (MulAut.conj g).toMonoidHom)
        (g * elemR * g⁻¹) (g * elemS * g⁻¹) (g * elemZ * g⁻¹) (g * elemH * g⁻¹) :=
  ⟨permR_apply, permS_apply, permH_apply, elemH_word, permH_word_list, fusionData_pinned,
    fun g => fusionData_pinned.map (MulAut.conj g)⟩

end CFSG.ComponentClassification.M12Cover
