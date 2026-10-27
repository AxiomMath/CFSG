module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenF4

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem a2l_even_G2_outer_fixed
    {F : Type} [Field F] [Finite F] {f : ℕ} (hf2 : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
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

theorem a2l_evenTCOuter_G2
    (hO : LieOrderFormulasInput) :
    EvenTCOuter .G2 := by
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
  obtain ⟨e', he', hfe, k, _, _, hk, ⟨Φ⟩⟩ := a2l_even_G2_outer_fixed hf2 hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  rcases Nat.lt_or_ge e' 2 with he1 | he2
  · exact fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hadm.2.2.1, by omega⟩)))))
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    obtain ⟨hA, hM⟩ := lieModel_G2_of_mulEquiv he2 hk E
    exact EvenTCConc.of_model_ne hO hA hM (by decide)

theorem a2l_evenTCOuter_F4
    (hO : LieOrderFormulasInput) : EvenTCOuter .F4 := by
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
    obtain ⟨hA, hM⟩ := lieModel_F4_of_mulEquiv he' hk E
    exact EvenTCConc.of_model_ne hO hA hM (by decide)
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      obtain ⟨hA, hM⟩ := lieModel_tits_of_isPComponent hF2
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      exact EvenTCConc.of_model_ne hO hA hM (by decide)
    · have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      obtain ⟨hA, hM⟩ := lieModel_twistedF4_of_mulEquiv hm1 hF' E
      exact EvenTCConc.of_model_ne hO hA hM (by decide)

private theorem a2l_evenTCOuter_E7_E8
    (hO : LieOrderFormulasInput) {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8) :
    EvenTCOuter t := by
  have hne : t ≠ .PSU := by rcases ht with rfl | rfl <;> decide
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
  obtain ⟨hA, hM⟩ := lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk E
  exact EvenTCConc.of_model_ne hO hA hM hne

theorem a2l_evenTCOuter_E7
    (hO : LieOrderFormulasInput) : EvenTCOuter .E7 :=
  a2l_evenTCOuter_E7_E8 hO (Or.inl rfl)

theorem a2l_evenTCOuter_E8
    (hO : LieOrderFormulasInput) : EvenTCOuter .E8 :=
  a2l_evenTCOuter_E7_E8 hO (Or.inr rfl)

end CFSG.OddStandard.SmallF3.HypA2Leaves
