module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXS
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer P211
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {Q : ℕ → Prop}

theorem compOrd_D4_outer
    {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hm : Blueprint.LieModel J .trialityD4 0 p f) {α : MulAut J} (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range)
    (hQ : ∀ e, f = 2 * e → Q (Open.ordTrialityD4 (p ^ e))) : CompOrd Q (fixedSubgroup α) := by
  intro L hL
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
    ((CatLeafProof.fixedSubgroupCongrEquiv e α).trans
      (CatLeafProof.fixedSubgroupCongrEquiv ψ β)).trans
      ((MulEquiv.subgroupCongr hFc).trans (Subgroup.subgroupOfEquivOfLe hJC))
  have : IsSimpleGroup (trialityFieldImage σ δ) := hsimple
  obtain ⟨E⟩ := CatLeafProof.nonempty_component_equiv_of_simple Ψ hL
  have hk' : Nat.card (fixSubfield δ) = (p ^ e') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ) c = c ^ ((p ^ e') ^ 2) :=
    fun c => Subtype.ext (by rw [hres c, hσ2, SubmonoidClass.coe_pow])
  let e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have hY := LieType.CurtisTits.lieModel_of_mulEquiv e₁
    (CatLeafProof.lieModel_graphFixedRootGroup_trialityD4_odd hp hp2 he1 hk'
      (fixSubfieldRestrict σ δ) (Or.inr hσ₀))
  have hnab' : ∃ a b : trialityFieldImage σ δ, a * b ≠ b * a := by
    obtain ⟨a, ha⟩ := not_forall.mp hnab
    obtain ⟨b, hb⟩ := not_forall.mp ha
    exact ⟨a, b, hb⟩
  have hZ : center (trialityFieldImage σ δ) = ⊥ := center_eq_bot_of_simple hnab'
  rw [card_centerQuotient_congr E, Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv,
    GH74.card_of_lieModel_trialityD4 hp2 hY]
  exact hQ e' (by omega)

theorem p211For_D4 :
    P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel G .trialityD4 0 p f := by
  intro X _ _ hsimp hC ⟨p', f', hp', hp2', hf', hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  exfalso
  have hmodel := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLie
  have hq'odd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp2').pow
  have hq'3 := CatLeafProof.three_le_pow_of_odd_prime hp' hp2' hf'
  refine p211_of_outer (n := padicValNat 2 ((p' ^ f') ^ 2 - 1)) hC
    (LieType.Chevalley.exceptional_Chevalley_model_Schreier _ .trialityD4 p' f' (by decide)
      hmodel).1
    (CatLeaf.fixedTwoComponentsQuasisimple_exceptional (by decide) hp' hp2' hmodel)
    (by rw [GH74.card_of_lieModel_trialityD4 hp2' hLie]; exact v2_ordTrialityD4 hq'odd hq'3)
    (fun β hβ hin => compOrd_D4_outer hp' hp2' hf' hLie hβ hin fun e' he' => ?_) hp hp2 hf hJt
    hDJ hDsyl hbound hb hb1 hKC hK hKt
  have he1 : 1 ≤ e' := by omega
  have hq0 : Odd (p' ^ e') := (hp'.odd_of_ne_two hp2').pow
  have hq03 := CatLeafProof.three_le_pow_of_odd_prime hp' hp2' he1
  show padicValNat 2 (Open.ordTrialityD4 (p' ^ e')) < 2 * padicValNat 2 ((p' ^ f') ^ 2 - 1)
  rw [v2_ordTrialityD4 hq0 hq03, he', pow_mul', v2_sq_sq_sub hq0 hq03]
  omega

end P211X

end CFSG.ComponentClassification.GSThmB
