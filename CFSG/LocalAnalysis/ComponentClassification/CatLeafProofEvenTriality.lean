module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenExc
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem even_triality_outer_actual
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) {X : Type} [Group X]
    [Finite X] (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    IsSimpleGroup ↥P ∧ ∃ e : ℕ, StatedLieAdmissible .trialityD4 0 2 e ∧
      LieModel (P ⧸ Open.fusionZStar P) .trialityD4 0 2 e := by
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨⟨e, he⟩, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ β hβ2 hβo
  have he1 : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (3 * e * 2) := by rw [hK', he]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (e * 2) := fun c => by rw [hσ, he]; ring_nf
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ, show 3 * f / 2 = 3 * e by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, hsimple, -, -⟩ :=
    RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      Nat.prime_two he1 (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK6 σ hσ' δ hδ'
  have hc : MulAut.congr ψ β = fieldActor σ δ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ β = ψ * β * ψ⁻¹).trans hψ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    change _ = (trialityFieldImage σ δ).comap
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective]
    rfl
  have hk' : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ) c = c ^ ((2 ^ e) ^ 2) :=
    fun c => Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow, ← pow_mul, mul_comm])
  let e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have hFc : fixedSubgroup (MulAut.congr ψ β) =
      (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [hc, hF]
  let Φ₀ : X ≃* ↥(trialityFieldImage σ δ) :=
    (Ψ.trans (fixedSubgroupCongrEquiv ψ β)).trans ((MulEquiv.subgroupCongr hFc).trans
      (Subgroup.subgroupOfEquivOfLe hJC))
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Φ₀ hP
  have hPsimp : IsSimpleGroup ↥P := by
    have hsimple' : IsSimpleGroup ↥(trialityFieldImage σ δ) := hsimple
    have hX : IsSimpleGroup X := Φ₀.isSimpleGroup
    have htop := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
    exact ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans Φ₀)).isSimpleGroup
  have hL := RankThree.PartOne.Sec66T.lieModel_graphFixedRootGroup_trialityD4 he1 hk'
    (fixSubfieldRestrict σ δ) (Or.inr hσ₀)
  exact ⟨hPsimp, e, ⟨Nat.prime_two, he1, rfl⟩,
    LieType.CurtisTits.lieModel_of_mulEquiv (E.trans e₁.symm).symm hL⟩

theorem even_triality_outer_lieModel
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) {X : Type} [Group X]
    [Finite X] (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    ∃ e : ℕ, StatedLieAdmissible .trialityD4 0 2 e ∧
      LieModel (P ⧸ Open.fusionZStar P) .trialityD4 0 2 e :=
  (even_triality_outer_actual hf hK σ hσ β hβ2 hβo Ψ hP).2

theorem evenOuterFamilyInput_trialityD4
    : EvenOuterFamilyInput .trialityD4 := by
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
  exact Or.inl ⟨.trialityD4, 0, e', hadm', hL⟩

end CFSG.ComponentClassification.CatLeafProof
