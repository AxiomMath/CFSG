module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqLieEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality
public import CFSG.Sporadic.Schreier.TitsInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)


theorem a6sq_even_twistedB2 {S : Type} [Group S] {n f : ℕ}
    (hadm : StatedLieAdmissible .twistedB2 n 2 f) (hm : LieModel S .twistedB2 n 2 f)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    False := by
  have hsq : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  refine hout (Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner S f
    (Or.inl ?_) σ hsq)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem a6sq_even_twistedF4 {S : Type} [Group S] {n f : ℕ}
    (hadm : StatedLieAdmissible .twistedF4 n 2 f) (hm : LieModel S .twistedF4 n 2 f)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    False := by
  have hsq : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  refine hout (Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner S f
    (Or.inr (Or.inl ?_)) σ hsq)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem a6sq_even_Tits {S : Type} [Group S] {n f : ℕ}
    (hadm : StatedLieAdmissible .Tits n 2 f) (hm : LieModel S .Tits n 2 f)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    False := by
  have hsq : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain rfl : f = 1 := hadm.2.2.2.2
  refine hout (Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner S 1
    (Or.inr (Or.inr ?_)) σ hsq)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem a6sq_even_E6 (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hadm : StatedLieAdmissible .E6 n 2 f) (hm : LieModel S .E6 n 2 f) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨D, -, hDp, -, -, hDz, -, -⟩ := a6sq_even_data hC hC'
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel S .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr e σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  obtain ⟨τ', n', f', hadm', hm'⟩ :=
    even_E6_outer_lieModel hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e σ) hDp
  exact a6sq_close_zstar hO hDz hadm' hm'

theorem a6sq_even_twistedE6 (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S]
    {n f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n 2 f) (hm : LieModel S .twistedE6 n 2 f)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨D, -, hDp, -, -, hDz, -, -⟩ := a6sq_even_data hC hC'
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel S .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ', hM, hσ', ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr e σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ'.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  obtain ⟨hadm', hm'⟩ :=
    even_twistedE6_outer_lieModel hf hM σ' hσ' β hβ2 hβo (fixedSubgroupCongrEquiv e σ) hDp
  exact a6sq_close_zstar hO hDz hadm' hm'

theorem a6sq_even_trialityD4 (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S]
    {n f : ℕ} (hadm : StatedLieAdmissible .trialityD4 n 2 f) (hm : LieModel S .trialityD4 n 2 f)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨D, -, hDp, -, -, hDz, -, -⟩ := a6sq_even_data hC hC'
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel S .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ', hM, hσ', ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.D4.tag M) := finite_modGL
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr e σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 M σ'.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  obtain ⟨e', hadm', hm'⟩ :=
    even_triality_outer_lieModel hf hM σ' hσ' β hβ2 hβo (fixedSubgroupCongrEquiv e σ) hDp
  exact a6sq_close_zstar hO hDz hadm' hm'

theorem a6sq_even_E7_E8 (hO : LieOrderFormulasInput) {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8)
    {S : Type} [Group S] [Finite S] {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hm : LieModel S t n 2 f) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨D, -, hDp, hDn, hD360, -, -, -⟩ := a6sq_even_data hC hC'
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨τ, hτ, htτ, hu⟩ : ∃ τ : Tag, (τ = .E7 ∨ τ = .E8) ∧
      (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) ∧ UntwistedChevalleyModel S τ (2 ^ f) := by
    rcases ht with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, Or.inl ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
    · exact ⟨.E8, Or.inr rfl, Or.inr ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hu
  have : Finite (ModGL τ F) := finite_modGL
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr e σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup τ F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  obtain ⟨e', he', k, _, _, hk, hs, ⟨Φ⟩⟩ := even_E7_E8_outer_fixed hτ hf hF β hβ2 hβo
  have : Finite (ModGL τ k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e σ).trans Φ
  obtain ⟨hadm', hm'⟩ := lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk Ψ
  exact a6sq_close_simple hO (Ψ.isSimpleGroup) hDn hD360 hadm' hm'

theorem a6sq_even_G2 (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hadm : StatedLieAdmissible .G2 n 2 f) (hm : LieModel S .G2 n 2 f) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨D, -, hDp, hDn, hD360, -, -, -⟩ := a6sq_even_data hC hC'
  have hq : 3 ≤ 2 ^ f := hadm.2.2.2
  have hf2 : 2 ≤ f := by
    by_contra h
    interval_cases f <;> norm_num at hq
  have hu : UntwistedChevalleyModel S .G2 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hu
  have : Finite (ModGL .G2 F) := finite_modGL
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr e σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .G2 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  obtain ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ := even_G2_outer_fixed hf2 hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e σ).trans Φ
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
      (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hDp)
    let E : ↥D ≃* ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
      ((D.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
        (MulEquiv.subgroupCongr hPeq)).trans (commutatorSubtypeEquiv (adjointGroup .G2 k))
    have hLm : LieModel ↥D .PSU 3 3 1 := LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL
    exact lieModel_psu33_card_ne_360 hO hLm hD360
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨hadm', hm'⟩ := lieModel_G2_of_mulEquiv he2 hk Ψ
    exact a6sq_close_simple hO (Ψ.isSimpleGroup) hDn hD360 hadm' hm'

theorem a6sq_even_F4 (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hadm : StatedLieAdmissible .F4 n 2 f) (hm : LieModel S .F4 n 2 f) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨D, -, hDp, hDn, hD360, hDz, -, -⟩ := a6sq_even_data hC hC'
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel S .F4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hu
  have : Finite (ModGL .F4 F) := finite_modGL
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  have hα : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set β := MulAut.congr e σ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .F4 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  rcases even_F4_outer_fixed hf hF β hβ2 hβo with ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ | ⟨m, hfm, ⟨Φ⟩⟩
  · have : Finite (ModGL .F4 k) := finite_modGL
    have := (ExcSelector.adjointGroup_F4_even he' hk).1
    set Ψ := (fixedSubgroupCongrEquiv e σ).trans Φ
    obtain ⟨hadm', hm'⟩ := lieModel_F4_of_mulEquiv he' hk Ψ
    exact a6sq_close_simple hO (Ψ.isSimpleGroup) hDn hD360 hadm' hm'
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      obtain ⟨hadm', hm'⟩ :=
        lieModel_tits_of_isPComponent hF2 ((fixedSubgroupCongrEquiv e σ).trans Φ) hDp
      exact a6sq_close_zstar hO hDz hadm' hm'
    · have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      set Ψ := (fixedSubgroupCongrEquiv e σ).trans Φ
      obtain ⟨hadm', hm'⟩ := lieModel_twistedF4_of_mulEquiv hm1 hF' Ψ
      exact a6sq_close_simple hO (Ψ.isSimpleGroup) hDn hD360 hadm' hm'

end CFSG.ComponentClassification.CatFC
