module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenExc
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.GH74.GLS.Stage2.Final.LayerLiftN

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem eq_commutator_of_isPComponent {X : Type*} [Group X] [Finite X]
    (hD : IsSimpleGroup (commutator X)) {P : Subgroup X} (hP : IsPComponent 2 P) :
    P = commutator X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := GH74.GLS.Stage2.Final.LayerLiftN.isPerfect_of_isPComponent hP
  have hle : P ≤ commutator X := by
    rw [← hperf, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hsub : (P.subgroupOf (commutator X)).IsSubnormal :=
    Subgroup.IsSubnormal.subgroupOf
      ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 P).mp hP).1
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hD hsub with h | h
  · exfalso
    have hP0 : P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hle hx⟩ : commutator X) ∈ P.subgroupOf (commutator X) := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
    have hnt := GrSLit.nontrivial_of_isPComponent hP
    rw [hP0] at hnt
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
  · refine le_antisymm hle fun x hx => ?_
    have hx' : (⟨x, hx⟩ : commutator X) ∈ P.subgroupOf (commutator X) := h ▸ Subgroup.mem_top _
    exact hx'

@[expose] def commutatorSubtypeEquiv {M : Type*} [Group M] (H : Subgroup M) :
    commutator ↥H ≃* ↥⁅H, H⁆ :=
  ((commutator ↥H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]))

variable {F : Type} [Field F]

theorem even_G2_outer_fixed
    [Finite F] {f : ℕ} (hf2 : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (β : MulAut (adjointGroup .G2 F)) (hβ2 : β ^ 2 = 1) (hβo : β ∉ inner (adjointGroup .G2 F)) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ e ∧
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
  exact ⟨e, he1, fixSubfield σ, inferInstance, inferInstance, hk,
    ⟨(fixedSubgroupCongrEquiv ψ β).trans ((MulEquiv.subgroupCongr hβψ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))⟩⟩

theorem lieModel_G2_of_mulEquiv
    {G : Type} [Group G] {k : Type} [Field k] [Finite k] {e : ℕ} (he : 2 ≤ e)
    (hk : Nat.card k = 2 ^ e) (E : G ≃* adjointGroup .G2 k) :
    StatedLieAdmissible .G2 0 2 e ∧ LieModel G .G2 0 2 e := by
  have h3 : 3 ≤ 2 ^ e := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
  exact ⟨⟨Nat.prime_two, by omega, rfl, h3⟩, Or.inr (Or.inl ⟨rfl, by decide,
    ⟨⟨Nat.prime_two, by omega, rfl, h3⟩, untwistedChevalleyModel_of_mulEquiv hk E⟩⟩)⟩

theorem evenOuterFamilyInput_G2
    : EvenOuterFamilyInput .G2 := by
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
    exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL))
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    exact Or.inl ⟨.G2, 0, e', lieModel_G2_of_mulEquiv he2 hk E⟩

end CFSG.ComponentClassification.CatLeafProof
