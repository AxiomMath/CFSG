module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def EvenOuterFamilyExcInput (τ : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f → LieModel K τ n 2 f →
    ∀ α : MulAut K, orderOf α = 2 → α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P → ExcEvenType (P ⧸ Open.fusionZStar P)

theorem evenOuterFamilyExcInput_G2 :
    EvenOuterFamilyExcInput .G2 := by
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

theorem evenOuterFamilyExcInput_F4 :
    EvenOuterFamilyExcInput .F4 := by
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

theorem evenOuterFamilyExcInput_E6 :
    EvenOuterFamilyExcInput .E6 := by
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
  rcases EvenExc.even_E6_outer_lieModel_exact hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
    with h | ⟨e', -, he', h | h⟩
  · exact Or.inl ⟨.F4, f, by decide, ⟨Nat.prime_two, hf, rfl⟩, h⟩
  · exact Or.inl ⟨.E6, e', by decide, ⟨Nat.prime_two, he', rfl⟩, h⟩
  · exact Or.inl ⟨.twistedE6, e', by decide, ⟨Nat.prime_two, he', rfl⟩, h⟩

theorem evenOuterFamilyExcInput_twistedE6 :
    EvenOuterFamilyExcInput .twistedE6 := by
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

theorem evenOuterFamilyExcInput_E7_E8
    {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8) : EvenOuterFamilyExcInput t := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨τ, hτ, htτ, hu⟩ : ∃ τ : Tag, (τ = .E7 ∨ τ = .E8) ∧
      (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) ∧ UntwistedChevalleyModel K τ (2 ^ f) := by
    rcases ht with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, Or.inl ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
    · exact ⟨.E8, Or.inr rfl, Or.inr ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hu
  have : Finite (ModGL τ F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup τ F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', he', k, _, _, hk, hs, ⟨Φ⟩⟩ := even_E7_E8_outer_fixed hτ hf hF β hβ2 hβo
  have : Finite (ModGL τ k) := finite_modGL
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
    ((fixedSubgroupCongrEquiv e α).trans Φ) hP
  exact Or.inl ⟨t, e', by rcases ht with rfl | rfl <;> decide,
    lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk E⟩

theorem evenOuterFamilyExcInput_trialityD4 :
    EvenOuterFamilyExcInput .trialityD4 := by
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

theorem no_sp6_component_of_excInput
    {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ) {S : Type} [Group S] [Finite S]
    {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e) (hm : LieModel S τ n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hD6 : LieModel D .PSp 3 2 f) :
    False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hm σ hσ hout D hP
  have : IsSimpleGroup D := isSimpleGroup_of_lieModel_PSp hD6
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP (MulEquiv.refl D)
  exact card_ne_of_excEvenType_of_lieModel_PSp_three hX hD6 (Nat.card_congr E.toEquiv)

theorem catSp6EvenOuterFamily_of_excInput
    {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ) : CatSp6EvenOuterFamily τ :=
  fun _ _ _ _ _ _ _ hadm hm _ hσ hout _ _ hD hD6 _ =>
    (no_sp6_component_of_excInput h hadm hm hσ hout hD hD6).elim

theorem catSp6EvenOuterFamily_G2 :
    CatSp6EvenOuterFamily .G2 :=
  catSp6EvenOuterFamily_of_excInput evenOuterFamilyExcInput_G2

theorem catSp6EvenOuterFamily_F4 :
    CatSp6EvenOuterFamily .F4 :=
  catSp6EvenOuterFamily_of_excInput evenOuterFamilyExcInput_F4

theorem catSp6EvenOuterFamily_E6 :
    CatSp6EvenOuterFamily .E6 :=
  catSp6EvenOuterFamily_of_excInput evenOuterFamilyExcInput_E6

theorem catSp6EvenOuterFamily_E7 :
    CatSp6EvenOuterFamily .E7 :=
  catSp6EvenOuterFamily_of_excInput (evenOuterFamilyExcInput_E7_E8 (Or.inl rfl))

theorem catSp6EvenOuterFamily_E8 :
    CatSp6EvenOuterFamily .E8 :=
  catSp6EvenOuterFamily_of_excInput (evenOuterFamilyExcInput_E7_E8 (Or.inr rfl))

theorem catSp6EvenOuterFamily_twistedE6 :
    CatSp6EvenOuterFamily .twistedE6 :=
  catSp6EvenOuterFamily_of_excInput evenOuterFamilyExcInput_twistedE6

theorem catSp6EvenOuterFamily_trialityD4 :
    CatSp6EvenOuterFamily .trialityD4 :=
  catSp6EvenOuterFamily_of_excInput evenOuterFamilyExcInput_trialityD4

end CFSG.SeitzReduction.F4Pilot
