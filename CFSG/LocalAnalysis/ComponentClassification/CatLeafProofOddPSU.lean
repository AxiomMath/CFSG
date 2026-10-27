module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def OddPSUInnerDiagInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] (p f : ℕ) (h : UnitaryFieldData p f K), p ≠ 2 →
    StatedLieAdmissible .PSU n p f →
    ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      orderOf (primeFormConjHom h _ A) = 2 →
      ∀ L : Subgroup (fixedSubgroup (primeFormConjHom h _ A)), IsComponent L →
        OddLieCentralQuotient p L

@[expose] def OddPSUGraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] (p f : ℕ) (h : UnitaryFieldData p f K), p ≠ 2 →
    StatedLieAdmissible .PSU n p f →
    ∀ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K),
      (∀ x, φ x = h.bar x) → orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 →
      ∀ L : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)),
        IsComponent L → OddLieCentralQuotient p L

theorem nonempty_mulEquiv_primeFormP_of_lieModel' {J : Type} [Group J] {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSU n p f) (hm : Blueprint.LieModel J .PSU n p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K),
      Nonempty (J ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hn : 3 ≤ n := hadm.2.2.1
  rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hU : UnitaryFieldData p f K := ⟨hadm.1, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_one (n := n) (K := K))
    exact ⟨K, inferInstance, hU, ⟨e.trans ((unitaryPSUEquiv hU (by omega)).symm.trans χ.symm)⟩⟩
  all_goals omega

theorem gls3OddFamilyInput_PSU (hinner : OddPSUInnerDiagInput) (hgraph : OddPSUGraphInput) :
    GLS3OddFamilyInput .PSU := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC hn hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  have hKc' := LocalCores.isComponent_map_mulEquiv (fixedSubgroupCongrEquiv ψ α) hKc
  refine oddLieCentralQuotient_of_mulEquiv
    (Kc.equivMapOfInjective (fixedSubgroupCongrEquiv ψ α).toMonoidHom
      (fixedSubgroupCongrEquiv ψ α).injective) ?_
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact oddLieCentralQuotient_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      (hinner n K p f h hp2 hadm A hord) hKc'
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact oddLieCentralQuotient_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (hgraph n K p f h hp2 hadm A φ hφ hord) hKc'

end CFSG.ComponentClassification.CatLeafProof
