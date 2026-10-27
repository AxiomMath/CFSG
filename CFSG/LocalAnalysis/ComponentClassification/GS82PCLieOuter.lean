module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.Sporadic.Schreier.TitsInner

public noncomputable section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (σ : K ≃+* K) : σ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK]
  refine RingEquiv.ext fun x => ?_
  have hx : x ^ 2 = x := by rw [← hcard]; exact FiniteField.pow_card x
  have hx' : x = 0 ∨ x = 1 := by
    have h0 : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hx, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact .inl h
    · exact .inr (sub_eq_zero.mp h)
  rcases hx' with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

theorem psp_three_two_mem_range {J : Type} [Group J] (hm : Blueprint.LieModel J .PSp 3 2 1)
    (α : MulAut J) : α ∈ (MulAut.conj : J →* MulAut J).range := by
  by_contra hαo
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel hm.admissible hm
  rw [pow_one] at hK
  have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 1) le_rfl (by rw [hK, pow_one])
  have hβo : MulAut.congr e α ∉ inner (StatedProj (StatedSp 3 K)) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have hmem : MulAut.congr e α ∈
      LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 3 K := by
    rw [(LocalAnalysis.ComponentInitial.SymplecticHigher.automorphism_generation (K := K)
      (r := 3) le_rfl).1]
    exact mem_top _
  obtain ⟨g, σ, hgσ⟩ := UnbalancedCatalog.SpChain.exists_eq_spInner_mul_fieldAut hmem
  rw [ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one] at hgσ
  exact hβo (hgσ ▸ UnbalancedCatalog.SpChain.spInner_mem_inner g)

theorem twistedB2_mem_range
    {J : Type} [Group J] {f : ℕ}
    (hm : Blueprint.LieModel J .twistedB2 0 2 f) {α : MulAut J} (hα : orderOf α = 2) :
    α ∈ (MulAut.conj : J →* MulAut J).range := by
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner J f (Or.inl ?_) α
    (hα ▸ pow_orderOf_eq_one α)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem card_fusionZStar_quot_of_statedSp_three_two {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {F : Type} [Group F] [Finite F] (Φ : F ≃* StatedSp 3 k)
    {P : Subgroup F} (hP : IsPComponent 2 P) :
    Nat.card (P ⧸ Open.fusionZStar P) = 1451520 := by
  have hk' : Nat.card k = 2 ^ 1 := by rw [hk, pow_one]
  have : CharP k 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hk'
  have : Finite (GL (Fin 3 ⊕ Fin 3) k) := Finite.of_injective Units.val Units.val_injective
  have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ 3) ∨
      (Nat.card k = 2 ∧ 3 ≤ 3) := Or.inr (Or.inr ⟨hk, le_rfl⟩)
  have := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k 3 (by norm_num) hcond
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp 3 k) hk' (by norm_num) ⟨MulEquiv.refl _⟩
  have : IsSimpleGroup (StatedSp 3 k) := eProj.symm.isSimpleGroup
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Φ hP
  rw [Nat.card_congr E.toEquiv, LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk]
  decide

theorem card_outer_fixed_omegaPlus {J : Type} [Group J] [Finite J]
    (hm : Blueprint.LieModel J .POmegaPlus 4 2 1) {α : MulAut J} (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) {P : Subgroup (fixedSubgroup α)}
    (hP : IsPComponent 2 P) : Nat.card (P ⧸ Open.fusionZStar P) = 1451520 := by
  obtain ⟨K, _, _, hK, hcases⟩ :=
    evenOrthogonal_outer_fixed_cases (Or.inl rfl) hm.admissible hm α hα hαo
  rw [pow_one] at hK
  rcases hcases with hch | ⟨⟨Φ⟩⟩ | ⟨⟨σ, hσ⟩, -⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · exact card_fusionZStar_quot_of_statedSp_three_two hK Φ hP
  · exact absurd (ringEquiv_eq_one_of_card_two hK σ) hσ

theorem card_outer_fixed_psu {J : Type} [Group J] [Finite J]
    (hm : Blueprint.LieModel J .PSU 6 2 1) {α : MulAut J} (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) {P : Subgroup (fixedSubgroup α)}
    (hP : IsPComponent 2 P) : Nat.card (P ⧸ Open.fusionZStar P) = 1451520 := by
  rcases even_unitary_outer_fixed_cases hm.admissible hm α hα hαo with
    hch | ⟨k, _, _, hk, r, -, hnr, ⟨Φ⟩⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · obtain rfl : r = 3 := by omega
    rw [pow_one] at hk
    exact card_fusionZStar_quot_of_statedSp_three_two hk Φ hP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem lieModel_outer_fixed_twistedE6
    {K : Type} [Group K] {f : ℕ} (hadm : StatedLieAdmissible .twistedE6 0 2 f)
    (hm : Blueprint.LieModel K .twistedE6 0 2 f) {α : MulAut K} (hα2 : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : K →* MulAut K).range) {P : Subgroup (fixedSubgroup α)}
    (hP : IsPComponent 2 P) : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .F4 0 2 f := by
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact (even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP).2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem even_G2_four_outer_fixed
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2)
    (β : MulAut (adjointGroup .G2 F)) (hβ2 : β ^ 2 = 1) (hβo : β ∉ inner (adjointGroup .G2 F)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ∧
      Nonempty (fixedSubgroup β ≃* adjointGroup .G2 k) := by
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have hβ1 : β ≠ 1 := fun h => hβo (h ▸ Subgroup.one_mem _)
  rcases UnbalancedCatalog.even_G2_involution_inner_or_canonical_field (f := 2) le_rfl F hF β
      (orderOf_eq_prime hβ2 hβ1) with h | ⟨-, hδ⟩
  · exact absurd h hβo
  have hF' : Nat.card F = 2 ^ (2 * 1) := hF
  set δ := iterateFrobenius F 2 1 with hδdef
  have hδc : ∀ c, δ c = c ^ 2 ^ (2 / 2) := fun c => iterateFrobenius_def 2 1 c
  obtain ⟨β', ψ, hβ', hψ, -⟩ := hδ δ hδc
  set σ := ExcSelector.ringEquivOfFinite δ
  have hσ : ∀ c, σ c = c ^ 2 ^ 1 := fun c => by
    rw [ExcSelector.ringEquivOfFinite_apply, hδdef, iterateFrobenius_def]
  have hk := ExcSelector.card_fixSubfield_of_pow le_rfl hF' hσ
  have hβ'σ : ∀ u, (β' u : ModGL .G2 F) =
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL .G2 F) := fun u => by
    rw [hβ' u, ExcSelector.toRingHom_ringEquivOfFinite]
  have hfix := ExcSelector.fixedSubgroup_eq_fixedFieldImage_even (τ := .G2) (Or.inl rfl) hchar σ
    hβ'σ
  have hc : MulAut.congr ψ β = β' :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ β = ψ * β * ψ⁻¹).trans hψ
  have hJC : fixedFieldImage .G2 σ ≤ adjointGroup .G2 F := fun x hx => (fixedFieldImage_le hx).1
  have hβψ : fixedSubgroup (MulAut.congr ψ β) =
      (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 F) := by rw [hc, hfix]
  exact ⟨fixSubfield σ, inferInstance, inferInstance, by rw [hk, pow_one],
    ⟨(fixedSubgroupCongrEquiv ψ β).trans ((MulEquiv.subgroupCongr hβψ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))⟩⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem lieModel_outer_fixed_G2_four
    {K : Type} [Group K] (hm : Blueprint.LieModel K .G2 0 2 2) {α : MulAut K}
    (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1 := by
  have hu : UntwistedChevalleyModel K .G2 (2 ^ 2) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hu
  have : Finite (ModGL .G2 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .G2 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨k, _, _, hk2, ⟨Φ⟩⟩ := even_G2_four_outer_fixed hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  have hL := Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk2
  have hs : IsSimpleGroup ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
    rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact (ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 h).2
    all_goals exact absurd h (by norm_num)
  have hD : IsSimpleGroup (commutator ↥(adjointGroup .G2 k)) :=
    (commutatorSubtypeEquiv (adjointGroup .G2 k)).isSimpleGroup
  have hPeq := eq_commutator_of_isPComponent hD
    (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hP)
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((P.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
      (MulEquiv.subgroupCongr hPeq)).trans (commutatorSubtypeEquiv (adjointGroup .G2 k)))
  exact LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree in
theorem lieModel_outer_fixed_F4_two
    {K : Type} [Group K] (hm : Blueprint.LieModel K .F4 0 2 1) {α : MulAut K}
    (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    Blueprint.LieModel (P ⧸ Open.fusionZStar P) .Tits 0 2 1 := by
  have hu : UntwistedChevalleyModel K .F4 (2 ^ 1) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hu
  have : Finite (ModGL .F4 F) := finite_modGL
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .F4 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  obtain ⟨ψ, hψ, -, hodd, -⟩ := even_F4_all_outer_involutions_canonical le_rfl F hF β hβ2 hβo
  set ψ₀ : MulAut (adjointGroup .F4 F) := ψ
  have hc : MulAut.congr ψ₀ β = ReeTag.F4.finiteExceptionalAut F ^ 1 :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ₀ β = ψ₀ * β * ψ₀⁻¹).trans hψ
  have hβψ : fixedSubgroup (MulAut.congr ψ₀ β) = reeFixed ReeTag.F4 F 0 :=
    (congrArg fixedSubgroup (hc.trans (hodd 0 rfl).1)).trans
      (ExcSelector.fixedSubgroup_finiteReeAut 0)
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  exact (lieModel_tits_of_isPComponent hF2 ((fixedSubgroupCongrEquiv e α).trans
    ((fixedSubgroupCongrEquiv ψ₀ β).trans (MulEquiv.subgroupCongr hβψ))) hP).2

end CFSG.ComponentClassification.GS82PumpInputs
