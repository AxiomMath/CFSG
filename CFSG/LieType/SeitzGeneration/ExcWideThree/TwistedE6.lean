module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTwField
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Escape
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwistedE6
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti

section TwE6


@[expose] def TwistedE6KernelLemma : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = ℓ ^ (2 * f) → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ η : K ≃+* K, orderOf η = 3 →
    ∀ ι : MulAut (twistedE6RootGroup K σ), ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
      (∀ x ∈ fixedSubgroup (fieldActor (t := TwistTag.E6) σ η), ι x = x) → ι = 1

theorem twistedE6_fieldPlanes_three (hker : TwistedE6KernelLemma) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hΘker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK2 σ hσ
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK
  have : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    DFunLike.coe_injective
  have hH : Nat.card {h : RingAut K // h ^ 3 = 1} ≤ 3 := by
    have := Fintype.ofFinite (RingAut K)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  have : Finite {h : RingAut K // h ^ 3 = 1} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨ι, hιE, hι1, hιker⟩ := exists_ne_one_mem_ker_of_card_le Nat.prime_three Θ hH E hEc
  have hιdiag : ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := hΘker ▸ hιker
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E, α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    by_contra h
    push Not at h
    exact hout fun x hx => h x hx
  have hα1 : α ≠ 1 := fun h => hα (h ▸ one_mem _)
  have hβ : α * ι ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun h =>
    hα (by simpa using mul_mem h (inv_mem hιdiag))
  have hβ1 : α * ι ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨hδa, -, ψa, hψa⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK σ hσ
    Θ hΘ Nat.prime_three (by norm_num) hα3 hα
  obtain ⟨-, -, ψb, hψb⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK σ hσ
    Θ hΘ Nat.prime_three (by norm_num) hβ3 hβ
  have hΘβ : Θ (α * ι) = Θ α := by rw [map_mul, MonoidHom.mem_ker.1 hιker, mul_one]
  refine closure_fixUnion_eq_top_of_kernel_escape (N := Θ.ker)
    (R := CFSG.RankThree.PartOne.CTP.fixedSubgroup (fieldActor (t := TwistTag.E6) σ (Θ α)))
    (subfieldMaximalAllThreeTwE6 ℓ f hℓ hf K hK2 σ hσ 3 rfl (fun h => hℓ3 h.symm) (Θ α) hδa) ?_
    hαE hιE hα1 hβ1 hι1 hιker (by rw [hψa]) (by rw [hψb, hΘβ])
  intro ι' hι'ker hι'fix
  exact hker ℓ f hℓ hℓ3 hf K hK σ hσ (Θ α) hδa ι' (hΘker ▸ hι'ker) hι'fix

end TwE6

end CFSG.LieType.SeitzGeneration.ExcWideThree
