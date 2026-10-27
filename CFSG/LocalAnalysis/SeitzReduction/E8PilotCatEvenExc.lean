module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatEvenClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcE6

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


@[expose] def EvenOuterFamilyTagInput (τ : StatedLieTag) (T : Finset StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f → LieModel K τ n 2 f →
    ∀ α : MulAut K, orderOf α = 2 → α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P →
      (∃ (τ' : StatedLieTag) (e : ℕ), τ' ∈ T ∧ StatedLieAdmissible τ' 0 2 e ∧
          LieModel (P ⧸ Open.fusionZStar P) τ' 0 2 e) ∨
        LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1

theorem no_e7_component_of_tagInput {τ : StatedLieTag} {T : Finset StatedLieTag}
    (h : EvenOuterFamilyTagInput τ T) (hT : StatedLieTag.E7 ∉ T) {S : Type} [Group S]
    [Finite S] {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e) (hm : LieModel S τ n 2 e)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {f : ℕ} {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hD7 : LieModel D .E7 0 2 f) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have : IsSimpleGroup D := isSimpleGroup_of_lieModel_E7 hD7
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP (MulEquiv.refl D)
  have hD7' : LieModel (D ⧸ Open.fusionZStar D) .E7 0 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv E.symm hD7
  rcases h S n e hadm hm σ hσ hout D hP with ⟨τ', e', hτ', -, hm'⟩ | hU
  · obtain ⟨rfl, -, -⟩ := lieModel_E7_two_unique hD7' hm'
    exact hT hτ'
  · have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) hU
    rw [show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide, Nat.card_congr E.toEquiv] at h1
    have h2 := two_pow_le_card_of_lieModel_E7_two hD7
    rw [h1] at h2
    norm_num at h2

theorem evenOuterFamilyTagInput_G2 : EvenOuterFamilyTagInput .G2 {.G2} := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hq : 3 ≤ 2 ^ f := hadm.2.2.2
  have hf2 : 2 ≤ f := by
    by_contra h
    interval_cases f <;> norm_num at hq
  have hu : UntwistedChevalleyModel K .G2 (2 ^ f) :=
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
  obtain ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ := even_G2_outer_fixed hf2 hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  rcases Nat.lt_or_ge e' 2 with he1 | he2
  · obtain rfl : e' = 1 := by omega
    have hk2 : Nat.card k = 2 := by simpa using hk
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
    exact Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL)
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    exact Or.inl ⟨.G2, e', by decide, lieModel_G2_of_mulEquiv he2 hk E⟩

theorem evenOuterFamilyTagInput_F4 : EvenOuterFamilyTagInput .F4 {.F4, .twistedF4, .Tits} := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .F4 (2 ^ f) :=
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
    Nat.prime_two (by omega) hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  rcases even_F4_outer_fixed hf hF β hβ2 hβo with ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ | ⟨m, hfm, ⟨Φ⟩⟩
  · have : Finite (ModGL .F4 k) := finite_modGL
    have := (ExcSelector.adjointGroup_F4_even he' hk).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
      ((fixedSubgroupCongrEquiv e α).trans Φ) hP
    exact Or.inl ⟨.F4, e', by decide, lieModel_F4_of_mulEquiv he' hk E⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      exact Or.inl ⟨.Tits, 1, by decide, lieModel_tits_of_isPComponent hF2
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP⟩
    · have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      exact Or.inl ⟨.twistedF4, 2 * m + 1, by decide, lieModel_twistedF4_of_mulEquiv hm1 hF' E⟩

theorem evenOuterFamilyTagInput_E6 : EvenOuterFamilyTagInput .E6 {.F4, .E6, .twistedE6} := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  rcases F4Pilot.EvenExc.even_E6_outer_lieModel_exact hf hF β hβ2 hβo
      (fixedSubgroupCongrEquiv e α) hP with h | ⟨e', -, he', h | h⟩
  · exact Or.inl ⟨.F4, f, by decide, ⟨Nat.prime_two, hf, rfl⟩, h⟩
  · exact Or.inl ⟨.E6, e', by decide, ⟨Nat.prime_two, he', rfl⟩, h⟩
  · exact Or.inl ⟨.twistedE6, e', by decide, ⟨Nat.prime_two, he', rfl⟩, h⟩

theorem evenOuterFamilyTagInput_twistedE6 : EvenOuterFamilyTagInput .twistedE6 {.F4} := by
  intro K _ n f hadm hm α hα2 hαo P hP
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
  exact Or.inl ⟨.F4, f, by decide,
    even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP⟩

theorem evenOuterFamilyTagInput_trialityD4 :
    EvenOuterFamilyTagInput .trialityD4 {.trialityD4} := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.D4.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', hadm', hL⟩ :=
    even_triality_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact Or.inl ⟨.trialityD4, e', by decide, hadm', hL⟩

theorem even_E7_E8_outer_fixed_exact {F : Type} [Field F] [Finite F] {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (β : MulAut (adjointGroup τ F)) (hβ2 : β ^ 2 = 1) (hβo : β ∉ inner (adjointGroup τ F)) :
    ∃ e : ℕ, 1 ≤ e ∧ f = 2 * e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = 2 ^ e ∧ IsSimpleGroup (adjointGroup τ k) ∧
        Nonempty (fixedSubgroup β ≃* adjointGroup τ k) := by
  have : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf F hF τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF β
  have hσ : Θ β = σ := hΘ β g σ hgσ
  rcases hinv β hβ2 with h1 | ⟨⟨e, he⟩, hpow⟩
  · have hker' : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hker'
    exact absurd hker' hβo
  have he1 : 1 ≤ e := by omega
  have hF' : Nat.card F = 2 ^ (2 * e) := by rw [hF, he, two_mul]
  have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
    rw [← hσ, hpow c, show f / 2 = e by omega]
  obtain ⟨_, -, hdesc⟩ :=
    (even_exceptional_quadratic_field_graph_field_involution_descent he1 F hF' σ.toRingHom
      hσe).1 τ
  obtain ⟨ψ, hψ, -⟩ := (hdesc g 1).2 β
    (fun u => by rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]) (by rw [← sq, hβ2])
  have hk := ExcSelector.card_fixSubfield_of_pow he1 hF' hσe
  have hfix := ExcSelector.fixedSubgroup_eq_fixedFieldImage_even (τ := τ) (by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hchar σ hψ
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ F := fun x hx => (fixedFieldImage_le hx).1
  have hβψ : fixedSubgroup (MulAut.congr ψ β) =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ F) := by rw [hc, hfix]
  have hs : IsSimpleGroup (adjointGroup τ (fixSubfield σ)) := by
    rcases hτ with rfl | rfl
    · exact (ExcSelector.adjointGroup_E7_even he1 hk).1
    · exact (ExcSelector.adjointGroup_E8_even he1 hk).1
  refine ⟨e, he1, by omega, fixSubfield σ, inferInstance, inferInstance, hk, hs, ⟨?_⟩⟩
  exact (fixedSubgroupCongrEquiv ψ β).trans ((MulEquiv.subgroupCongr hβψ).trans
    ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))

theorem evenOuterFamilyTagInput_E8 : EvenOuterFamilyTagInput .E8 {.E8} := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E8 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hu
  have : Finite (ModGL .E8 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E8 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', he', k, _, _, hk, hs, ⟨Φ⟩⟩ := even_E7_E8_outer_fixed (Or.inr rfl) hf hF β hβ2 hβo
  have : Finite (ModGL .E8 k) := finite_modGL
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
    ((fixedSubgroupCongrEquiv e α).trans Φ) hP
  exact Or.inl ⟨.E8, e', by decide,
    lieModel_of_mulEquiv_adjointGroup_E7_E8 (Or.inr ⟨rfl, rfl⟩) he' hk E⟩

theorem catE7EvenOuterFamily_of_tagInput {τ : StatedLieTag} {T : Finset StatedLieTag}
    (h : EvenOuterFamilyTagInput τ T) (hT : StatedLieTag.E7 ∉ T) : CatE7EvenOuterFamily τ :=
  catE7EvenOuterFamily_of_forall_false fun _ _ _ _ _ hadm hm _ hσ hout _ _ hD hD7 =>
    no_e7_component_of_tagInput h hT hadm hm hσ hout hD hD7

theorem catE7EvenOuterFamily_G2 : CatE7EvenOuterFamily .G2 :=
  catE7EvenOuterFamily_of_tagInput evenOuterFamilyTagInput_G2 (by decide)

theorem catE7EvenOuterFamily_F4 : CatE7EvenOuterFamily .F4 :=
  catE7EvenOuterFamily_of_tagInput evenOuterFamilyTagInput_F4 (by decide)

theorem catE7EvenOuterFamily_E6 : CatE7EvenOuterFamily .E6 :=
  catE7EvenOuterFamily_of_tagInput evenOuterFamilyTagInput_E6 (by decide)

theorem catE7EvenOuterFamily_twistedE6 : CatE7EvenOuterFamily .twistedE6 :=
  catE7EvenOuterFamily_of_tagInput evenOuterFamilyTagInput_twistedE6 (by decide)

theorem catE7EvenOuterFamily_trialityD4 : CatE7EvenOuterFamily .trialityD4 :=
  catE7EvenOuterFamily_of_tagInput evenOuterFamilyTagInput_trialityD4 (by decide)

theorem catE7EvenOuterFamily_E8 : CatE7EvenOuterFamily .E8 :=
  catE7EvenOuterFamily_of_tagInput evenOuterFamilyTagInput_E8 (by decide)

theorem catE7EvenOuterFamily_E7 : CatE7EvenOuterFamily .E7 := by
  intro S _ _ _ _ n e hadm hm σ hσ hout f D hD hD7
  obtain ⟨-, he, rfl⟩ := hadm
  have hu : UntwistedChevalleyModel S .E7 (2 ^ e) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨eS⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hu
  have : Finite (ModGL .E7 F) := finite_modGL
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr eS σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E7 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  obtain ⟨e', he', hee', k, _, _, hk, hs, ⟨Φ⟩⟩ :=
    even_E7_E8_outer_fixed_exact (Or.inl rfl) he hF β hβ2 hβo
  have : Finite (ModGL .E7 k) := finite_modGL
  let Ψ : fixedSubgroup σ ≃* adjointGroup .E7 k := (fixedSubgroupCongrEquiv eS σ).trans Φ
  have hsimple : IsSimpleGroup (fixedSubgroup σ) := Ψ.isSimpleGroup
  have hfix7 : LieModel (fixedSubgroup σ) .E7 0 2 e' :=
    (lieModel_of_mulEquiv_adjointGroup_E7_E8 (Or.inl ⟨rfl, rfl⟩) he' hk Ψ).2
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  obtain ⟨-, -, rfl⟩ := lieModel_E7_two_unique (LieType.CurtisTits.lieModel_of_mulEquiv eD hD7)
    hfix7
  exact ⟨hee' ▸ hm, hfix7⟩

theorem catE7EvenOuter : CatE7EvenOuter :=
  catE7EvenOuter_of_open_families catE7EvenOuterFamily_PSL catE7EvenOuterFamily_PSU
    catE7EvenOuterFamily_PSp catE7EvenOuterFamily_POmegaPlus catE7EvenOuterFamily_POmegaMinus
    catE7EvenOuterFamily_G2 catE7EvenOuterFamily_F4 catE7EvenOuterFamily_E6
    catE7EvenOuterFamily_E7 catE7EvenOuterFamily_E8 catE7EvenOuterFamily_twistedE6
    catE7EvenOuterFamily_trialityD4

end CFSG.SeitzReduction.E8Pilot
