module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem a6_trialityD4_outer_false (hO : LieOrderFormulasInput) {J : Type} [Group J] [Finite J]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 0 p f)
    (hm : Blueprint.LieModel J .trialityD4 0 p f) {α : MulAut J} (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) {D : Subgroup ↥(fixedSubgroup α)}
    (hD : A6Hyp α D) : False := by
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hDc, -⟩ := hD.component
  obtain ⟨-, ⟨eD⟩, -⟩ := hD
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  set C := graphFixedRootGroup TwistTag.D4 M σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβo : β ∉ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∉ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hex β
  have hΘβ : Θ β = δ := hΘ β g δ hgδ
  rcases hinv β hβ2 with h1 | ⟨⟨e', he'⟩, hδc⟩
  · exact absurd (hker ▸ (MonoidHom.mem_ker.mpr h1)) hβo
  have he1 : 1 ≤ e' := by omega
  have hδ : ∀ c, δ c = c ^ p ^ (3 * e') := fun c => by
    rw [← hΘβ, hδc, show 3 * f / 2 = 3 * e' by omega]
  have hr : IsPrimePow (p ^ e') := hp.isPrimePow.pow (by omega)
  have hro : Odd (p ^ e') := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hM3 : Nat.card M = (p ^ f) ^ 3 := hM
  have hM6 : Nat.card M = (p ^ e') ^ 6 := by
    rw [hM3, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hσ2 : ∀ c, σ c = c ^ ((p ^ e') ^ 2) := fun c => by
    rw [hσ, show f = e' * 2 by omega, pow_mul]
  have hδ3 : ∀ c, δ c = c ^ ((p ^ e') ^ 3) := fun c => by
    rw [hδ, ← pow_mul, mul_comm]
  have hα2 : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 := hgδ ▸ hβ2
  obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components hr hro M hM6 σ
    hσ2 δ hδ3 g hα2
  have hM6' : Nat.card M = p ^ (3 * e' * 2) := by
    rw [hM3, ← pow_mul]
    congr 1
    omega
  have hσ' : ∀ c, σ c = c ^ p ^ (e' * 2) := fun c => by
    rw [hσ, show f = e' * 2 by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, hsimple, hnab, -⟩ :=
    RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp he1
      (le_refl 2) (by norm_num : Nat.Coprime 2 3) M hM6' σ hσ' δ hδ
  have hc : MulAut.congr ψ β = fieldActor σ δ := by
    rw [show MulAut.congr ψ β = ψ * β * ψ⁻¹ from MulEquiv.ext fun _ => rfl, hgδ]
    exact hψ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      (trialityFieldImage σ δ).subgroupOf C := by
    change _ = (trialityFieldImage σ δ).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have hFc : fixedSubgroup (MulAut.congr ψ β) = (trialityFieldImage σ δ).subgroupOf C := by
    rw [hc, hF]
  let Ψ : fixedSubgroup α ≃* trialityFieldImage σ δ :=
    ((fixedSubgroupCongrEquiv e α).trans (fixedSubgroupCongrEquiv ψ β)).trans
      ((MulEquiv.subgroupCongr hFc).trans (Subgroup.subgroupOfEquivOfLe hJC))
  have : IsSimpleGroup (trialityFieldImage σ δ) := hsimple
  obtain ⟨E⟩ := nonempty_component_equiv_of_simple Ψ hDc
  have hk' : Nat.card (fixSubfield δ) = (p ^ e') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ) c = c ^ ((p ^ e') ^ 2) :=
    fun c => Subtype.ext (by rw [hres c, hσ2, SubmonoidClass.coe_pow])
  let e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have hY := LieType.CurtisTits.lieModel_of_mulEquiv e₁
    (lieModel_graphFixedRootGroup_trialityD4_odd hp hp2 he1 hk' (fixSubfieldRestrict σ δ)
      (Or.inr hσ₀))
  have hcard : Nat.card (trialityFieldImage σ δ) = 360 := by
    rw [← Nat.card_congr E.toEquiv, Nat.card_congr eD.toEquiv, a6sq_card]
  have h360 := a6sq_lieModel_card_360 hO ⟨hp, he1, rfl⟩ hp2 hY hcard
  exact absurd h360.1 (by decide)

end CFSG.ComponentClassification.CatFC
