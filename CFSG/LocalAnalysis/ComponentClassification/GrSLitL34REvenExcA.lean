module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenF4

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace L34R

theorem lieModel_nonclassical_card_ne_L34 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ}
    (ht : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧ t ≠ .POmegaMinus)
    (hadm : StatedLieAdmissible t n p f) (hX : Blueprint.LieModel X t n p f) :
    Nat.card X ≠ 20160 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 20160 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 20160 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  rcases prime_dvd_L34 hp hpd with rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl
      exacts [absurd rfl h1, absurd rfl h2]
    · rcases ht with rfl | rfl
      exacts [absurd rfl h3, absurd rfl h4]
    · cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem not_isL34Type_of_nonclassical (hO : LieOrderFormulasInput)
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧ t ≠ .POmegaMinus)
    (hadm : StatedLieAdmissible t n p f) (hX : Blueprint.LieModel X t n p f) :
    ¬ IsL34Type X := fun hL =>
  lieModel_nonclassical_card_ne_L34 hO ht hadm hX (card_of_isL34Type hL)

theorem not_isL34Type_of_psu33 (hO : LieOrderFormulasInput)
    {X : Type} [Group X] (hX : Blueprint.LieModel X .PSU 3 3 1) : ¬ IsL34Type X := fun hL =>
  have hadm : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  lieModel_odd_card_ne_L34 hO (by norm_num) hadm hX (card_of_isL34Type hL)

theorem not_isL34Type_outer_G2
    (hO : LieOrderFormulasInput) {K : Type} [Group K] {n f : ℕ}
    (hadm : StatedLieAdmissible .G2 n 2 f) (hm : LieModel K .G2 n 2 f) {α : MulAut K}
    (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
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
    exact not_isL34Type_of_psu33 hO (LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL)
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    obtain ⟨hadm', hm'⟩ := lieModel_G2_of_mulEquiv he2 hk E
    exact not_isL34Type_of_nonclassical hO (by decide) hadm' hm'

theorem not_isL34Type_outer_F4
    (hO : LieOrderFormulasInput) {K : Type} [Group K] {n f : ℕ}
    (hadm : StatedLieAdmissible .F4 n 2 f) (hm : LieModel K .F4 n 2 f) {α : MulAut K}
    (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
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
    obtain ⟨hadm', hm'⟩ := lieModel_F4_of_mulEquiv he' hk E
    exact not_isL34Type_of_nonclassical hO (by decide) hadm' hm'
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      obtain ⟨hadm', hm'⟩ := lieModel_tits_of_isPComponent hF2
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      exact not_isL34Type_of_nonclassical hO (by decide) hadm' hm'
    · have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      obtain ⟨hadm', hm'⟩ := lieModel_twistedF4_of_mulEquiv hm1 hF' E
      exact not_isL34Type_of_nonclassical hO (by decide) hadm' hm'

theorem not_isL34Type_outer_E7_E8
    (hO : LieOrderFormulasInput) {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8) {K : Type} [Group K]
    {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hm : LieModel K t n 2 f) {α : MulAut K}
    (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
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
  obtain ⟨hadm', hm'⟩ := lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk E
  refine not_isL34Type_of_nonclassical hO ?_ hadm' hm'
  rcases ht with rfl | rfl <;> decide

end L34R

end CFSG.ComponentClassification.GrSLit
