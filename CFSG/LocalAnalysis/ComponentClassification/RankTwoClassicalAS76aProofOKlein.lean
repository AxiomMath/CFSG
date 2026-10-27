module

public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nonempty_statedOmega_quadPlus_three_equiv (hK : 4 ≤ Nat.card K) :
    Nonempty (StatedOmega (StatedQuadPlus 3 K) ≃* SL(4, K)) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)
  obtain ⟨eK⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six (quadPlus 3 K)
    (nondegenerate_polarBilin_quadPlus 3 K) (by simp) (exists_totallySingular_quadPlus le_rfl K) hK
  have h1 : (StatedOmega (StatedQuadPlus 3 K)).map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom = ⁅O, O⁆ := by
    rw [← coe_quadPlus, CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap rfl]
    exact map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).surjective _
  have h2 : (commutator ↥O).map O.subtype = ⁅O, O⁆ := Subgroup.map_subtype_commutator _
  exact ⟨((((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).subgroupMap
    (StatedOmega (StatedQuadPlus 3 K))).trans (MulEquiv.subgroupCongr h1)).trans
      (((Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
        (MulEquiv.subgroupCongr h2)).symm.trans eK)).trans
          (specialLinearGroupEquivStatedSL 4 K).symm⟩

theorem statedClassicalModel_psl_four {L : Type} [Group L] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) (hK4 : 4 ≤ Nat.card K)
    (e : L ⧸ center L ≃*
      StatedOmega (StatedQuadPlus 3 K) ⧸ center (StatedOmega (StatedQuadPlus 3 K))) :
    StatedClassicalModel (L ⧸ center L) .PSL 4 2 m := by
  obtain ⟨eSL⟩ := nonempty_statedOmega_quadPlus_three_equiv (K := K) hK4
  refine ⟨⟨Nat.prime_two, hm, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance, hK,
    ⟨(e.trans (QuotientGroup.congr _ _ eSL (Subgroup.map_center_eq _))).trans
      (projectiveSpecialLinearGroupEquivStatedProj 4 K)⟩⟩

end CFSG.ComponentClassification.RankTwoClassical
