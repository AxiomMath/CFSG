module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Chevalley
  CFSG.RankThree.LocalRank SteinbergBT

section


theorem G2_descent {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (α : MulAut ↥(adjointGroup Tag.G2 K)) (hαp : α ^ 3 = 1)
    (hα : α ∉ inner ↥(adjointGroup Tag.G2 K)) :
    ∃ (d : ℕ) (σ : K ≃+* K) (δ : MulAut ↥(adjointGroup Tag.G2 K)), f = 3 * d ∧
      orderOf σ = 3 ∧ Nat.card ↥(fixSubfield σ) = ℓ ^ d ∧
        δ * α * δ⁻¹ = entrywiseAdjointAut Tag.G2 σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαord : orderOf α = 3 :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner ↥(adjointGroup Tag.G2 K)).one_mem)
  have hform : ∃ (x : ↥(adjointGroup Tag.G2 K)) (σ : K ≃+* K),
      orderOf σ = 3 ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hf2 : 2 ≤ f := by
        by_contra h
        have : f = 1 := by omega
        subst this
        omega
      exact G2_form_even hf2 K hK Nat.prime_three α hαord hα
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      have : CharP K 3 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
      exact G2_form_three hf K hK Nat.prime_three (by norm_num) α hαord hα
    · exact G2_form_odd hℓ hℓ2 hℓ3 hf K hK Nat.prime_three α hαord hα
  obtain ⟨x, σ, hσp, hασ⟩ := hform
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK Nat.prime_three α
    hαord x σ hσp hασ
  obtain ⟨hpf, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hpf hcard
  obtain ⟨d, hd⟩ := hpf
  refine ⟨d, σ, δ, hd, hσp, ?_, hδ⟩
  rw [hcard, hd, Nat.mul_div_cancel_left d Nat.prime_three.pos]

theorem not_dvd_g2_two (r m : ℕ) (hr : 10 ≤ r) (hm : m + r = r ^ 3) : ¬ m ∣ 2 * 12096 := by
  intro hdvd
  have hle : m ≤ 2 * 12096 := Nat.le_of_dvd (by norm_num) hdvd
  have hr28 : r ≤ 28 := by
    by_contra hcon
    have h29 : 29 ≤ r := by omega
    have h1 : 29 * 29 * r ≤ r * r * r := Nat.mul_le_mul (Nat.mul_le_mul h29 h29) le_rfl
    have h2 : r ^ 3 = r * r * r := by ring
    rw [h2] at hm
    generalize r * r * r = u at h1 hm
    omega
  have hm' : m = r ^ 3 - r := by omega
  subst hm'
  interval_cases r <;> simp at hdvd

theorem noL2Layer_entrywise_G2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = ℓ ^ d) : NoL2Layer (entrywiseAdjointAut Tag.G2 σ) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  by_cases h3 : 3 ≤ ℓ ^ d
  · have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield σ)) .G2 ℓ d :=
      ⟨⟨hℓ, hd, rfl, h3⟩, untwisted_adjointGroup hk⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ ℓ d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.G2 ↥(fixSubfield σ)) = ⊥ :=
      center_adjointGroup_eq_bot
    exact noL2Layer_entrywise_of_model hO (by decide) (by decide) σ
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (exists_noncomm_of_center_bot hZ) hZ
  · have h2 : ℓ ^ d = 2 := by
      have : 2 ≤ ℓ ^ d := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
      omega
    refine noL2Layer_of_card_dvd _ (N := 12096) ?_ fun r m hr hm => not_dvd_g2_two r m hr hm
    have hfix : Nat.card ↥(fixSubgroup (entrywiseAdjointAut Tag.G2 σ)) =
        Nat.card ↥(entrywiseFixedGroup Tag.G2 σ) := by
      rw [fixSubgroup_entrywiseAdjointAut]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hfix, card_entrywiseFixedGroup_G2 σ (hk.trans h2)]
    simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]

theorem noL2OuterAt_g2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL2OuterAt FamG2 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .G2 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.G2 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ :=
    G2_descent hadm.1 hf hadm.2.2.2 F hFcard _ hβ3 hβinn
  refine noL2Layer_congr θ (noL2Layer_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) ?_)
  exact noL2Layer_entrywise_G2 hO T hadm.1 (by omega) hTc

theorem y923_g2_holds :
    Y923_G2 :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_g2 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
