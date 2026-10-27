module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.Ree CFSG.RankThree.Chevalley
  CFSG.RankThree.LocalRank SteinbergBT

section


theorem F4_descent {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (α : MulAut ↥(adjointGroup Tag.F4 K)) (hαp : α ^ 3 = 1)
    (hα : α ∉ inner ↥(adjointGroup Tag.F4 K)) :
    ∃ (d : ℕ) (σ : K ≃+* K) (δ : MulAut ↥(adjointGroup Tag.F4 K)), f = 3 * d ∧
      orderOf σ = 3 ∧ Nat.card ↥(fixSubfield σ) = ℓ ^ d ∧
        δ * α * δ⁻¹ = entrywiseAdjointAut Tag.F4 σ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαord : orderOf α = 3 :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner ↥(adjointGroup Tag.F4 K)).one_mem)
  have hαin : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range :=
    hα
  obtain ⟨σ, ψ, hσp, hψ⟩ : ∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup Tag.F4 K)),
      orderOf σ = 3 ∧ ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.F4 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact even_F4_odd_prime_field_descent hf K hK Nat.prime_three (by norm_num) α hαord hαin
    · obtain ⟨-, σ, δ, hσp, -, hδ, -⟩ :=
        odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK Nat.prime_three α hαord hαin
      exact ⟨σ, δ, hσp, hδ⟩
  obtain ⟨hpf, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hpf hcard
  obtain ⟨d, hd⟩ := hpf
  refine ⟨d, σ, ψ, hd, hσp, ?_, hψ⟩
  rw [hcard, hd, Nat.mul_div_cancel_left d Nat.prime_three.pos]

theorem noL2OuterAt_f4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL2OuterAt FamF4 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .F4 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.F4 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ := F4_descent hf F hFcard _ hβ3 hβinn
  refine noL2Layer_congr θ (noL2Layer_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) .F4 p d :=
    ⟨⟨hadm.1, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ p d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL2Layer_entrywise_of_model hO ht (by decide) T (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ) hZ

theorem y923_f4_holds :
    Y923_F4 :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_f4 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
