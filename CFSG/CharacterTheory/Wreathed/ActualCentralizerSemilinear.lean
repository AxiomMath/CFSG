module

public import CFSG.CharacterTheory.Wreathed.ActualProjectiveLayer
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift

public noncomputable section
namespace CFSG.Wreathed.ActualCentralizerSemilinear

universe u v
open CFSG.Wreathed.ActualProjectiveLayer
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOddExtensions

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

@[expose] def rangeEquiv {D : Type u} [Group D] {F : Type v} [Field F]
    (rho : D →* coordinateE F) (hrho : Function.Injective rho) : D ≃* rho.range :=
  MulEquiv.ofBijective rho.rangeRestrict
    ⟨fun _ _ h => hrho (congrArg Subtype.val h), rho.rangeRestrict_surjective⟩

theorem rangeEquiv_coe {D : Type u} [Group D] {F : Type v} [Field F]
    (rho : D →* coordinateE F) (hrho : Function.Injective rho) (x : D) :
    (rangeEquiv rho hrho x : coordinateE F) = rho x := rfl

@[expose] def actualField {F : Type v} [Field F] [Finite F]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (rho : centralizerFullQuotient n hn S e →* coordinateE F) :
    Subgroup (F ≃+* F) := fieldImage F rho.range

omit [IsSimpleGroup G] in
theorem actual_layer_map_eq_special
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) :
    (centralizerSimpleLayer n hn S e).map rho = specialLayer F := by
  let t := theta.trans (pslEquivCoordinateG F)
  apply le_antisymm
  · rintro x ⟨l, hl, rfl⟩
    change (rho l).val ∈ coordinateG F
    rw [hextends ⟨l, hl⟩]
    exact (t ⟨l, hl⟩).property
  · intro x hx
    let a : coordinateG F := ⟨x.val, hx⟩
    let l := t.symm a
    refine ⟨l.val, l.property, ?_⟩
    apply Subtype.ext
    rw [hextends l]
    exact congrArg Subtype.val (t.apply_symm_apply a)

omit [IsSimpleGroup G] in
theorem actual_layer_index_in_range
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) :
    (specialLayer F).relIndex rho.range = (centralizerSimpleLayer n hn S e).index := by
  rw [← actual_layer_map_eq_special n hn S e theta rho hextends, ← Subgroup.map_top rho,
    Subgroup.relIndex_map_map_of_injective _ _ hrho, Subgroup.relIndex_top_right]

theorem actual_layer_index_even
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Even (centralizerSimpleLayer n hn S e).index := by
  have h := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at h
  obtain ⟨_, _, _, _, _, _, _, _, htwo⟩ := h
  change 2 ^ (centralizerSimpleLayer n hn S e).index.factorization 2 = 2 at htwo
  have hdvd := Nat.ordProj_dvd (centralizerSimpleLayer n hn S e).index 2
  rw [htwo] at hdvd
  exact even_iff_two_dvd.mpr hdvd

@[expose] def actualRangeSylow
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F) : Sylow 2 rho.range := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (centralizerFullQuotientSylow n hn S e).mapSurjective
    (f := rho.rangeRestrict) rho.rangeRestrict_surjective

@[expose] def actualRangeSylowEquiv
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho) : actualRangeSylow n hn S e rho ≃*
      DihedralGroup (2 ^ n) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change ((centralizerFullQuotientSylow n hn S e).mapSurjective
    (f := rho.rangeRestrict) rho.rangeRestrict_surjective) ≃* _
  rw [Sylow.coe_mapSurjective]
  exact ((rangeEquiv rho hrho).subgroupMap
    (centralizerFullQuotientSylow n hn S e : Subgroup _)).symm.trans
      (centralizerFullQuotientSylowEquiv n hn S e)

theorem actual_model_linear_extension
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) :
    Odd (Nat.card (actualField n hn S e rho)) ∧
      Nat.card (actualField n hn S e rho) ∣ f ∧
      LinearExtension F rho.range (actualField n hn S e rho) := by
  have hG : specialLayer F ≤ rho.range :=
    (actual_layer_map_eq_special n hn S e theta rho hextends) ▸
      Subgroup.map_le_range rho (centralizerSimpleLayer n hn S e)
  let P := actualRangeSylow n hn S e rho
  have eP : P ≃* DihedralGroup (2 ^ ((n + 1) - 1)) := by
    rw [show n + 1 - 1 = n by omega]
    exact actualRangeSylowEquiv n hn S e rho hrho
  have hshape := dihedral_projective_semilinear_overgroups_have_odd_field_part F
    hp (hp.odd_of_ne_two hpodd) hf hcard rho.range hG P (show 2 ≤ n + 1 by omega) eP
  have heven : Even ((specialLayer F).relIndex rho.range) := by
    rw [actual_layer_index_in_range n hn S e theta rho hrho hextends]
    exact actual_layer_index_even hnonab n hn S e hfour
  exact ⟨hshape.2.1, hshape.2.2.1, hshape.2.2.2.2.1.mp heven⟩

@[expose] def actualRangePhi
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F) :
    centralizerOddCoreQuotient n S e →* rho.range :=
  rho.rangeRestrict.comp (centralizerFullQuotientMap n hn S e)

omit [IsSimpleGroup G] in
theorem actualRangePhi_coe
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (h : centralizerOddCoreQuotient n S e) :
    (actualRangePhi n hn S e rho h : coordinateE F) =
      rho (centralizerFullQuotientMap n hn S e h) := rfl

omit [IsSimpleGroup G] in
theorem actualRangePhi_surjective
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F) :
    Function.Surjective (actualRangePhi n hn S e rho) :=
  rho.rangeRestrict_surjective.comp (centralizerFullQuotientMap_surjective n hn S e)

omit [IsSimpleGroup G] in
theorem actualRangePhi_ker
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho) :
    (actualRangePhi n hn S e rho).ker = centralizerFullCenterImage n hn S e := by
  rw [actualRangePhi, MonoidHom.ker_comp_of_injective _ _
    ((MonoidHom.rangeRestrict_injective_iff).mpr hrho)]
  exact QuotientGroup.ker_mk' _

@[expose] def actualPhi
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho)) :
    centralizerOddCoreQuotient n S e →*
      CFSG.Semidihedral.OddFieldLift.Gamma F (actualField n hn S e rho) :=
  (MulEquiv.subgroupCongr hlinear.1.2.2.1).toMonoidHom.comp (actualRangePhi n hn S e rho)

omit [IsSimpleGroup G] in
theorem actualPhi_coe
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho))
    (h : centralizerOddCoreQuotient n S e) :
    (actualPhi n hn S e rho hlinear h : coordinateE F) =
      rho (centralizerFullQuotientMap n hn S e h) := rfl

omit [IsSimpleGroup G] in
theorem actualPhi_surjective
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho)) :
    Function.Surjective (actualPhi n hn S e rho hlinear) :=
  (MulEquiv.subgroupCongr hlinear.1.2.2.1).surjective.comp
    (actualRangePhi_surjective n hn S e rho)

omit [IsSimpleGroup G] in
theorem actualPhi_ker
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho)) :
    (actualPhi n hn S e rho hlinear).ker = centralizerFullCenterImage n hn S e := by
  rw [actualPhi, MonoidHom.ker_comp_of_injective _ _
    (MulEquiv.subgroupCongr hlinear.1.2.2.1).injective]
  exact actualRangePhi_ker n hn S e rho hrho

omit [IsSimpleGroup G] in
theorem actualPhi_actual_layer_action
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho))
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (hvalues : ∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
      coordinatePSLAction F (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F (eta v)) =
        (rho (centralizerFullQuotientMap n hn S e v)).val)
    (v : CFSG.layer (centralizerOddCoreQuotient n S e)) :
    coordinatePSLAction F (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F (eta v)) =
      (((actualPhi n hn S e rho hlinear v : CFSG.Semidihedral.OddFieldLift.Gamma F
        (actualField n hn S e rho)) : coordinateE F) : Equiv.Perm (Omega F)) := hvalues v

omit [Finite G] [IsSimpleGroup G] in
theorem actual_layer_card_sl2
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :
    Nat.card (CFSG.layer (centralizerOddCoreQuotient n S e)) =
      Nat.card F * (Nat.card F ^ 2 - 1) :=
  (Nat.card_congr eta.toEquiv).trans (CFSG.GorensteinWalter.sl2_card_formula F)

theorem actual_sl2_twoPart
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :
    2 ^ (Nat.card F * (Nat.card F ^ 2 - 1)).factorization 2 = 2 * 2 ^ n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := actual_layer_card_sl2 n S e eta
  rw [(wreathed_centralizer_unique_component_data hnonab n hn S e hfour).layer] at hcard
  change Nat.card (centralizerLiftedLayer n hn S e) = _ at hcard
  rw [← hcard, ← Sylow.card_eq_multiplicity (centralizerLiftedLayerSylow hnonab n hn S e hfour)]
  exact centralizerLiftedLayerSylow_card hnonab n hn S e hfour

theorem actual_q_square_sub_one_twoPart
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (hodd : Odd (Nat.card F))
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :
    2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
  have h := actual_sl2_twoPart hnonab n hn S e hfour eta
  let : Fintype F := Fintype.ofFinite F
  have hpos : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hsub : Nat.card F ^ 2 - 1 ≠ 0 := by
    have hpow := Nat.one_lt_pow (by decide : 2 ≠ 0) hpos
    omega
  rw [Nat.factorization_mul (Nat.card_pos.ne') hsub, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, zero_add] at h
  exact h

theorem actual_layer_normal
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
  rw [(wreathed_centralizer_unique_component_data hnonab n hn S e hfour).layer]
  infer_instance

@[expose] def actualLayerSylow
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Sylow 2 (CFSG.layer (centralizerOddCoreQuotient n S e)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t := (centralizerActualLayerEquiv hnonab n hn S e hfour).symm
  have ht : Function.Surjective t.toMonoidHom := by
    intro x
    exact ⟨t.symm x, t.apply_symm_apply x⟩
  exact (centralizerLiftedLayerSylow hnonab n hn S e hfour).mapSurjective
    (f := t.toMonoidHom) ht

theorem actualLayerSylow_card
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Nat.card (actualLayerSylow hnonab n hn S e hfour) = 2 * 2 ^ n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity,
    (wreathed_centralizer_unique_component_data hnonab n hn S e hfour).layer]
  change 2 ^ (Nat.card (centralizerLiftedLayer n hn S e)).factorization 2 = _
  rw [← Sylow.card_eq_multiplicity (centralizerLiftedLayerSylow hnonab n hn S e hfour)]
  exact centralizerLiftedLayerSylow_card hnonab n hn S e hfour

theorem actualLayerSylow_image
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (actualLayerSylow hnonab n hn S e hfour : Subgroup (CFSG.layer
      (centralizerOddCoreQuotient n S e))).map
        (CFSG.layer (centralizerOddCoreQuotient n S e)).subtype =
      modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t := (centralizerActualLayerEquiv hnonab n hn S e hfour).symm
  have ht : Function.Surjective t.toMonoidHom := by
    intro x
    exact ⟨t.symm x, t.apply_symm_apply x⟩
  change ((centralizerLiftedLayerSylow hnonab n hn S e hfour).mapSurjective
    (f := t.toMonoidHom) ht).toSubgroup.map
      (CFSG.layer (centralizerOddCoreQuotient n S e)).subtype = _
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : (CFSG.layer (centralizerOddCoreQuotient n S e)).subtype.comp t.toMonoidHom =
      (centralizerLiftedLayer n hn S e).subtype := by
    ext v
    rfl
  rw [hcomp, centralizerLiftedLayerSylow_image, centralizerQuaternionImage_eq_modelY]

theorem actual_quotient_sylow_inter_layer
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)) ⊓
        CFSG.layer (centralizerOddCoreQuotient n S e) =
      modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizerOddCoreQuotient n S e
  let P := centralizerOddCoreSylow n hn S e
  let M := CFSG.layer H
  let : M.Normal := actual_layer_normal hnonab n hn S e hfour
  let U := actualLayerSylow hnonab n hn S e hfour
  obtain ⟨t⟩ := normal_sylow_equiv_actual_intersection P M U
  have hcard : Nat.card ((P : Subgroup H) ⊓ M : Subgroup H) = Nat.card U :=
    (Nat.card_congr t.toEquiv).symm
  have hYcard : Nat.card (modelY P (centralizerOddCoreCoordinates n hn S e)) = Nat.card U := by
    rw [← actualLayerSylow_image hnonab n hn S e hfour, Subgroup.card_map_of_injective
      (CFSG.layer H).subtype_injective]
  have hYleM : modelY P (centralizerOddCoreCoordinates n hn S e) ≤ M := by
    rw [← actualLayerSylow_image hnonab n hn S e hfour]
    exact Subgroup.map_subtype_le _
  have hYleP : modelY P (centralizerOddCoreCoordinates n hn S e) ≤ (P : Subgroup H) :=
    modelY_le_sylow P _
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hYleP hYleM) (hcard.trans hYcard.symm).le).symm

omit [IsSimpleGroup G] in
theorem actual_quotient_wreath_value
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (w : Wreath (2 ^ n)) :
    wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) w =
      centralizerOddCoreMap n S e
        (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) w) :=
  centralizerOddCoreModelHom_apply n hn S e w

omit [IsSimpleGroup G] in
theorem actual_quotient_involution_value
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (Original.x (2 ^ n)) =
      centralizerOddCoreMap n S e (centralInvolution n S e) := by
  rw [actual_quotient_wreath_value, centralizerModelHom_x]

omit [IsSimpleGroup G] in
theorem actual_quotient_generator_order
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (Original.a (2 ^ n))) = 2 ^ n := by
  rw [orderOf_injective _ (wreathModelHom_injective _ _)]
  exact Original.orderOf_a _

omit [IsSimpleGroup G] in
theorem actualPhi_kernel_center_data
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho)) :
    (actualPhi n hn S e rho hlinear).ker =
        modelCenter (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) ∧
      (actualPhi n hn S e rho hlinear).ker = Subgroup.zpowers
        (wreathModelHom (centralizerOddCoreSylow n hn S e)
          (centralizerOddCoreCoordinates n hn S e) (Original.a (2 ^ n))) ∧
      Subgroup.center (centralizerOddCoreQuotient n S e) = (actualPhi n hn S e rho hlinear).ker ∧
      IsCyclic (actualPhi n hn S e rho hlinear).ker ∧
      Nat.card (actualPhi n hn S e rho hlinear).ker = 2 ^ n := by
  rw [actualPhi_ker n hn S e rho hrho hlinear]
  refine ⟨centralizerFullCenterImage_eq_modelCenter n hn S e, ?_,
    centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e, inferInstance,
    centralizerFullCenterImage_card n hn S e⟩
  rw [centralizerFullCenterImage_eq_zpowers, ← actual_quotient_wreath_value]

theorem actual_layer_component_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.IsComponent (CFSG.layer (centralizerOddCoreQuotient n S e)) ∧
      (∀ D : Subgroup (centralizerOddCoreQuotient n S e), CFSG.IsComponent D →
        D = CFSG.layer (centralizerOddCoreQuotient n S e)) ∧
      (CFSG.layer (centralizerOddCoreQuotient n S e)).Characteristic ∧
      Subgroup.centralizer (CFSG.layer (centralizerOddCoreQuotient n S e) :
        Set (centralizerOddCoreQuotient n S e)) = centralizerFullCenterImage n hn S e ∧
      Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e)) =
        (Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))).subgroupOf
          (CFSG.layer (centralizerOddCoreQuotient n S e)) := by
  have hU := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  rw [hU.layer]
  exact ⟨hU.component, hU.only_component, hU.characteristic,
    hU.centralizer.trans (QuotientGroup.ker_mk' _), hU.center⟩

structure ActualCentralCoverInputs
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) : Prop where
  field_odd : Odd (Nat.card (actualField n hn S e rho))
  field_order_dvd : Nat.card (actualField n hn S e rho) ∣ f
  linear_extension : LinearExtension F rho.range (actualField n hn S e rho)
  rho_layer : (centralizerSimpleLayer n hn S e).map rho = specialLayer F
  actual_index : (specialLayer F).relIndex rho.range = (centralizerSimpleLayer n hn S e).index
  index_two_part : (centralizerSimpleLayer n hn S e).index.factorization 2 = 1
  quotient_sylow_values : ∀ w : Wreath (2 ^ n),
    wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) w =
      centralizerOddCoreMap n S e
        (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) w)
  layer_normal : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal
  sylow_intersection :
    (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)) ⊓
        CFSG.layer (centralizerOddCoreQuotient n S e) =
      modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e)
  quotient_center : Subgroup.center (centralizerOddCoreQuotient n S e) =
    modelCenter (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e)
  center_card : Nat.card (Subgroup.center (centralizerOddCoreQuotient n S e)) = 2 ^ n
  center_cyclic : IsCyclic (Subgroup.center (centralizerOddCoreQuotient n S e))
  q_two_part : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n
  matrix_card : Nat.card (CFSG.layer (centralizerOddCoreQuotient n S e)) =
    Nat.card F * (Nat.card F ^ 2 - 1)
  involution : eta (centralizerActualLayerInvolution hnonab n hn S e hfour) =
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F
  projective : (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F).comp eta.toMonoidHom =
    theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour)
  action_values : ∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
    coordinatePSLAction F (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F (eta v)) =
      (rho (centralizerFullQuotientMap n hn S e v)).val

theorem actual_central_cover_inputs
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (hprojective : (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F).comp eta.toMonoidHom =
      theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour))
    (hinvolution : eta (centralizerActualLayerInvolution hnonab n hn S e hfour) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta := by
  obtain ⟨hodd, hdvd, hlinear⟩ := actual_model_linear_extension
    hnonab n hn S e hfour p f hp hpodd hf hcard theta rho hrho hextends
  have hL := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at hL
  have hindex : (centralizerSimpleLayer n hn S e).index.factorization 2 = 1 := hL.2.2.2.2.2.2.2.1
  have hA := centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e
  have hqodd : Odd (Nat.card F) := hcard ▸ (hp.odd_of_ne_two hpodd).pow
  refine ⟨hodd, hdvd, hlinear, actual_layer_map_eq_special n hn S e theta rho hextends,
    actual_layer_index_in_range n hn S e theta rho hrho hextends, hindex,
    actual_quotient_wreath_value n hn S e, actual_layer_normal hnonab n hn S e hfour,
    actual_quotient_sylow_inter_layer hnonab n hn S e hfour,
    hA.trans (centralizerFullCenterImage_eq_modelCenter n hn S e),
    hA ▸ centralizerFullCenterImage_card n hn S e,
    hA ▸ (inferInstance : IsCyclic (centralizerFullCenterImage n hn S e)),
    actual_q_square_sub_one_twoPart hnonab n hn S e hfour hqodd eta,
    actual_layer_card_sl2 n S e eta, hinvolution, hprojective, ?_⟩
  intro v
  have hv := DFunLike.congr_fun hprojective v
  change CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F (eta v) =
    theta (centralizerActualLayerMap hnonab n hn S e hfour v) at hv
  rw [hv]
  have hvalue := hextends (centralizerActualLayerMap hnonab n hn S e hfour v)
  rw [centralizerActualLayerMap_coe] at hvalue
  exact hvalue.symm

theorem actual_projective_model_cover_inputs
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F),
        Function.Injective rho ∧
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta,
    hrho, hextends, _, _, _, hprojective, hinvolution, _⟩ :=
    actual_projective_layer_model_compatible_sl2 hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, hextends,
    actual_central_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hcard
      theta rho hrho hextends eta hprojective hinvolution⟩

theorem actual_stated_projective_model_cover_inputs
    {G₀ : Type} [Group G₀] [Finite G₀] [IsSimpleGroup G₀]
    (hnonab : ∃ a b : G₀, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G₀) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F),
        Function.Injective rho ∧
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta :=
  actual_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf
    ((pslTwoClassicalModel_iff_stated _ p f).mpr hmodel)

theorem actual_original_phi_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) :
    ∃ phi : centralizerOddCoreQuotient n S e →*
        CFSG.Semidihedral.OddFieldLift.Gamma F (actualField n hn S e rho),
      Function.Surjective phi ∧
      (∀ h, (phi h : coordinateE F) = rho (centralizerFullQuotientMap n hn S e h)) ∧
      phi.ker = modelCenter (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) ∧
      phi.ker = Subgroup.zpowers (wreathModelHom (centralizerOddCoreSylow n hn S e)
        (centralizerOddCoreCoordinates n hn S e) (Original.a (2 ^ n))) ∧
      Subgroup.center (centralizerOddCoreQuotient n S e) = phi.ker ∧
      IsCyclic phi.ker ∧ Nat.card phi.ker = 2 ^ n := by
  have hlinear := (actual_model_linear_extension hnonab n hn S e hfour
    p f hp hpodd hf hcard theta rho hrho hextends).2.2
  exact ⟨actualPhi n hn S e rho hlinear, actualPhi_surjective n hn S e rho hlinear,
    actualPhi_coe n hn S e rho hlinear, actualPhi_kernel_center_data n hn S e rho hrho hlinear⟩

end CFSG.Wreathed.ActualCentralizerSemilinear
