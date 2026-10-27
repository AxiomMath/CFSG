module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamULift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamUGraph
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

theorem cl24_family_PSU : Cl24OddFamily .PSU := by
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
  refine cl24_of_mulEquiv
    (Kc.equivMapOfInjective (fixedSubgroupCongrEquiv ψ α).toMonoidHom
      (fixedSubgroupCongrEquiv ψ α).injective) ?_
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact cl24_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      (fun M hM =>
        cl24_oddLie_inner_psu h hp2 hadm A hord hM) hKc'
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact cl24_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (fun M hM =>
        cl24_oddLie_graph_psu (cl24_orthogonalComponentsLie_holds hp hp2) h hp2 hadm A φ
          hφ hord hM) hKc'

end CFSG.OddStandard.SmallF3.HypA2Leaves
