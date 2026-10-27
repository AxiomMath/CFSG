module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


variable {F : Type} [Field F]

theorem even_G2_outer_fixed_two_mul [Finite F] {f : ℕ} (hf2 : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (β : MulAut (adjointGroup .G2 F)) (hβ2 : β ^ 2 = 1) (hβo : β ∉ inner (adjointGroup .G2 F)) :
    ∃ e : ℕ, 1 ≤ e ∧ f = 2 * e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ e ∧
      Nonempty (fixedSubgroup β ≃* adjointGroup .G2 k) := by
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have hβ1 : β ≠ 1 := fun h => hβo (h ▸ Subgroup.one_mem _)
  rcases UnbalancedCatalog.even_G2_involution_inner_or_canonical_field hf2 F hF β
      (orderOf_eq_prime hβ2 hβ1) with h | ⟨⟨e, he⟩, hδ⟩
  · exact absurd h hβo
  have he1 : 1 ≤ e := by omega
  have hF' : Nat.card F = 2 ^ (2 * e) := by rw [hF, he, two_mul]
  set δ := iterateFrobenius F 2 (f / 2) with hδdef
  have hδc : ∀ c, δ c = c ^ 2 ^ (f / 2) := fun c => iterateFrobenius_def 2 (f / 2) c
  obtain ⟨β', ψ, hβ', hψ, -⟩ := hδ δ hδc
  set σ := ExcSelector.ringEquivOfFinite δ
  have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
    rw [ExcSelector.ringEquivOfFinite_apply, hδc, show f / 2 = e by omega]
  have hk := ExcSelector.card_fixSubfield_of_pow he1 hF' hσ
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
  exact ⟨e, he1, by omega, fixSubfield σ, inferInstance, inferInstance, hk,
    ⟨(fixedSubgroupCongrEquiv ψ β).trans ((MulEquiv.subgroupCongr hβψ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))⟩⟩

theorem g2EvenOuterFamily_G2 : G2EvenOuterFamily .G2 := by
  intro K _ _ m f hadm hmK α hα2 hαo P hP n hG
  have hq : 3 ≤ 2 ^ f := hadm.2.2.2
  have hf2 : 2 ≤ f := by
    by_contra h
    interval_cases f <;> norm_num at hq
  have hu : UntwistedChevalleyModel K .G2 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hu
  have : Finite (ModGL .G2 F) := finite_modGL
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .G2 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', he', hfe, k, _, _, hk, ⟨Φ⟩⟩ := even_G2_outer_fixed_two_mul hf2 hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_or_ge e' 2 with he1 | he2
  · exfalso
    obtain rfl : e' = 1 := by omega
    have hk2 : Nat.card k = 2 := by simpa using hk
    have hc : Nat.card (adjointGroup .G2 k) = Open.ordG2 2 := by
      rw [← hk2]
      exact Timmesfeld.ExceptionalOrders.card_adjointGroup_G2
    have h12 : 2 ^ 12 ∣ Nat.card (adjointGroup .G2 k) := by
      rw [← Nat.card_congr Ψ.toEquiv]
      exact (two_pow_twelve_dvd_card_of_lieModel_G2 hG).trans
        ((Subgroup.card_quotient_dvd_card (Open.fusionZStar P)).trans
          (Subgroup.card_subgroup_dvd_card P))
    rw [hc] at h12
    exact absurd h12 (by decide)
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    obtain ⟨-, hM⟩ := lieModel_G2_of_mulEquiv he2 hk E
    obtain ⟨-, hen⟩ := lieModel_G2_two_unique hG hM
    omega

theorem g2EvenOuterFamily_F4 : G2EvenOuterFamily .F4 := by
  intro K _ _ m f hadm hmK α hα2 hαo P hP n hG
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .F4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hu
  have : Finite (ModGL .F4 F) := finite_modGL
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .F4 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  exfalso
  rcases even_F4_outer_fixed hf hF β hβ2 hβo with ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ | ⟨m', hfm, ⟨Φ⟩⟩
  · have : Finite (ModGL .F4 k) := finite_modGL
    have := (ExcSelector.adjointGroup_F4_even he' hk).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
      ((fixedSubgroupCongrEquiv e α).trans Φ) hP
    exact false_of_lieModel_G2_of_ne hG (by decide) (lieModel_F4_of_mulEquiv he' hk E).2
  · rcases Nat.eq_zero_or_pos m' with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      exact false_of_lieModel_G2_of_ne hG (by decide)
        (lieModel_tits_of_isPComponent hF2 ((fixedSubgroupCongrEquiv e α).trans Φ) hP).2
    · have hF' : Nat.card F = 2 ^ (2 * m' + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      exact false_of_lieModel_G2_of_ne hG (by decide)
        (lieModel_twistedF4_of_mulEquiv hm1 hF' E).2

theorem g2EvenOuterFamily_E6 : G2EvenOuterFamily .E6 := by
  intro K _ _ m f hadm hmK α hα2 hαo P hP n hG
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨τ', n', f', hτ', -, hm'⟩ :=
    even_E6_outer_lieModel_tag hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact (false_of_lieModel_G2_of_ne hG (by rcases hτ' with rfl | rfl | rfl <;> decide) hm').elim

theorem g2EvenOuterFamily_twistedE6 : G2EvenOuterFamily .twistedE6 := by
  intro K _ _ m f hadm hmK α hα2 hαo P hP n hG
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact (false_of_lieModel_G2_of_ne hG (by decide)
    (even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP).2).elim

theorem g2EvenOuterFamily_E7_E8 {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8) :
    G2EvenOuterFamily t := by
  intro K _ _ m f hadm hmK α hα2 hαo P hP n hG
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨τ, hτ, htτ, hu⟩ : ∃ τ : Tag, (τ = .E7 ∨ τ = .E8) ∧
      (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) ∧ UntwistedChevalleyModel K τ (2 ^ f) := by
    rcases ht with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, Or.inl ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2⟩
    · exact ⟨.E8, Or.inr rfl, Or.inr ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hu
  have : Finite (ModGL τ F) := finite_modGL
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
  exact (false_of_lieModel_G2_of_ne hG (by rcases ht with rfl | rfl <;> decide)
    (lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk E).2).elim

theorem g2EvenOuterFamily_E7 : G2EvenOuterFamily .E7 := g2EvenOuterFamily_E7_E8 (Or.inl rfl)

theorem g2EvenOuterFamily_E8 : G2EvenOuterFamily .E8 := g2EvenOuterFamily_E7_E8 (Or.inr rfl)

theorem g2EvenOuterFamily_trialityD4 : G2EvenOuterFamily .trialityD4 := by
  intro K _ _ m f hadm hmK α hα2 hαo P hP n hG
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hmK).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.D4.tag M) := finite_modGL
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', -, hL⟩ :=
    even_triality_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact (false_of_lieModel_G2_of_ne hG (by decide) hL).elim

end CFSG.EvenSporadicStandard.Induction
