module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigRWit

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82CorIIIq_of_orders
    (hCI : CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput)
    (hCL1 : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) : Asc82CorIIIq := by
  intro G _ _ t L hS z K p n _ hz hn hq hK
  obtain ⟨hzK, hKle, hKsub, hSL⟩ := hK
  rw [top_inf_eq] at hKle hKsub
  have hsub : CFSG.Open.IsSubnormal K (centralizer ({z} : Set G)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hKle).2 hKsub
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  exact c3b_false_of_witness hCI hCL1 hO hS hz hzK hsub S
    (sec5c3q_quaternion_of_isSL2qMod hn hq hSL S) (sec5c3q_witness_of_isSL2qMod hn hq hSL)

end CFSG.OddStandard.SmallF3.Omega
