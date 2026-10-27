module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormD4
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcBasic

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Exc

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem isEmpty_a5_of_simple_model (hO : LieOrderFormulasInput) {L J : Type} [Group L] [Group J]
    [IsSimpleGroup J] (hnab : ∃ a b : J, a * b ≠ b * a) (E : L ≃* J) {τ : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hY : Blueprint.LieModel J τ n p f) (hne : ¬ (τ = .PSL ∧ n = 2)) :
    IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 5)) := by
  have hZ : center J = ⊥ := center_eq_bot_of_simple hnab
  let eQ : J ⧸ center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hlie : Blueprint.LieModel (J ⧸ center J) τ n p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv eQ.symm hY
  exact isEmpty_a5_of_lieModel hO E hadm hp2 hlie hne

theorem noLitA5_trialityOuter
    (hO : LieOrderFormulasInput) (J : Type) [Group J] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p f) (hm : Blueprint.LieModel J .trialityD4 0 p f)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    NoLitA5 (fixedSubgroup α) := by
  rintro L hL ⟨eA⟩
  exfalso
  have hf : 1 ≤ f := hadm.2.1
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
  obtain ⟨E⟩ := nonempty_component_equiv_of_simple Ψ hL
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
  have hnab' : ∃ a b : trialityFieldImage σ δ, a * b ≠ b * a := by
    obtain ⟨a, ha⟩ := not_forall.mp hnab
    obtain ⟨b, hb⟩ := not_forall.mp ha
    exact ⟨a, b, hb⟩
  exact (isEmpty_a5_of_simple_model hO hnab' E ⟨hp, he1, rfl⟩ hp2 hY (by decide)).false eA

theorem oddLieA5For_trialityD4
    (hO : LieOrderFormulasInput) : OddLieA5For .trialityD4 := by
  intro J _ n p f hp hp2 _ hadm hm α hα
  obtain rfl : n = 0 := hadm.2.2
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨-, hform⟩ := oddTrialityInnerSLForm_holds J p f hp hp2 hadm hm α hα hi
    have : Fact p.Prime := ⟨hp⟩
    have hf : 1 ≤ f := hadm.2.1
    haveI : Finite J := (hO J .trialityD4 0 p f hadm hm).1
    exact noLitA5_of_slComponentForm (K := GaloisField p f)
      (by rw [ringChar.eq (GaloisField p f) p]; exact hp2)
      (hform (GaloisField p f) (GaloisField.card p f (by omega)))
  · exact noLitA5_trialityOuter hO J p f hp hp2 hadm hm α hα hi

end CFSG.ComponentClassification.SolMax.FiveCat.C5Exc
