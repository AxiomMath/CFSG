module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped MatrixGroups

theorem c3b_nonempty_genFittingFStar_equiv {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Nonempty (CFSG.Open.genFittingFStar G ≃* G) :=
  ⟨(MulEquiv.subgroupCongr
    (CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnab)).trans Subgroup.topEquiv⟩

theorem c3b_genFittingFStar_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    IsSimpleGroup (CFSG.Open.genFittingFStar G) ∧
      ∃ a b : CFSG.Open.genFittingFStar G, a * b ≠ b * a := by
  obtain ⟨e⟩ := c3b_nonempty_genFittingFStar_equiv hnab
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

theorem c3b_classicalInvolutionWitness_of_isSL23Mod {G : Type} [Group G] {K : Subgroup G}
    (h : IsSL23Mod K) : CFSG.Open.classicalInvolutionWitness K := by
  obtain ⟨e⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : CFSG.Open.classicalInvolutionOddCore ↥K = CFSG.oddCore ↥K := rfl
  exact Or.inl ⟨3, 1, inferInstance, by norm_num, by norm_num,
    ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans e).trans
      (CFSG.ClassicalModels.specialLinearFieldEquiv
        (GaloisField.equivZmodP 3).symm.toRingEquiv (Fin 2))⟩⟩

theorem c3b_oddLieType_or_m11_of_isI4PlusIn
    (hCI : CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup (CFSG.Open.genFittingFStar G)]
    (hnab : ∃ a b : CFSG.Open.genFittingFStar G, a * b ≠ b * a) {z : G}
    (hz : IsI4PlusIn (⊤ : Subgroup G) z) :
    CFSG.Blueprint.OddLieType (CFSG.Open.genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (CFSG.Open.genFittingFStar G) .M11 := by
  obtain ⟨hz2, K, hzK, hKle, hKsub, hK⟩ := hz
  rw [top_inf_eq] at hKle hKsub
  have hsub : CFSG.Open.IsSubnormal K (centralizer ({z} : Set G)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hKle).2 hKsub
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨e⟩ := hK
  have hO : CFSG.Open.classicalInvolutionOddCore ↥K = CFSG.oddCore ↥K := rfl
  have hQ : Nonempty ((S : Subgroup ↥K) ≃* QuaternionGroup 2) :=
    CFSG.ClassicalInvolution.Q3.Q3T6.exists_quaternion_of_quotEquiv_sl2Three
      ((QuotientGroup.quotientMulEquivOfEq hO).trans e) S
  exact (hCI G hnab z hz2 K hzK hsub S ⟨3, le_rfl, hQ⟩).1
    (c3b_classicalInvolutionWitness_of_isSL23Mod ⟨e⟩)

end CFSG.OddStandard.SmallF3.Omega
