module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial

section


theorem noL2Layer_entrywise_e6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hcard : Nat.card (fixSubfield σ) = ℓ ^ d) :
    NoL2Layer (entrywiseAdjointAut Tag.E6 σ) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 ℓ d :=
    ⟨⟨hℓ, hd, rfl⟩, untwisted_adjointGroup hcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ ℓ d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL2Layer_entrywise_of_model hO (by decide) (by decide) σ
    (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (exists_noncomm_of_center_bot hZ) hZ

theorem noL2Layer_of_not_mem_e6Inndiag (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {x : MulAut (adjointGroup Tag.E6 K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ e6Inndiag K) : NoL2Layer x := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨σ, hσo, hpf, δ, hδ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ hf K hK
    Nat.prime_three (by norm_num) hx3 hxo
  have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
  have hcard : Nat.card (fixSubfield σ) = ℓ ^ (f / 3) := by
    have := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ).2
    rwa [hσo] at this
  have h1 : NoL2Layer (δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹) :=
    noL2Layer_conj δ⁻¹ (noL2Layer_entrywise_e6 hO hℓ hd σ hcard)
  have h2 : δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹ = x := by
    rw [← hδ]
    group
  rwa [h2] at h1

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
