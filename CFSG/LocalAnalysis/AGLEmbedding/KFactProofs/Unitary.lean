module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneSchreier

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryOrder : KFactUnitaryOrder := by
  intro L _ _ p d hd h
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := UnitaryModel.statedClassicalModel hd h
  exact UnitaryModel.card_mul_gcd hp hf hK e

theorem kFactUnitaryOuterSolvable : KFactUnitaryOuterSolvable := by
  intro L _ _ p d hd h
  exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_rank_one_classical_model_schreier
    (UnitaryModel.statedClassicalModel hd h)).2

theorem kFactUnitaryBorelMaximal : KFactUnitaryBorelMaximal := by
  intro L _ _ p _ d hd h U
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have h1 : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, he', hS]
  have h2 : Subgroup.normalizer ((U : Subgroup L) : Set L) =
      (Subgroup.normalizer (rootGroup J hJ : Set _)).comap e'.toMonoidHom := by
    rw [← h1, Subgroup.comap_map_eq_self_of_injective e'.injective]
  rw [h2]
  exact (Subgroup.isCoatom_comap e').2 (UnitaryModel.isCoatom_normalizer_rootGroup J hJ hK hfix hq)

theorem kFactUnitarySylowStructure : KFactUnitarySylowStructure := by
  intro L _ _ p _ d hp2 hd h U
  obtain ⟨-, hf, -, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : CharP K p := UnitaryModel.charP_of_card Fact.out hK
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hU]
    exact UnitaryModel.card_rootGroup_eq J hJ hK hfix
  · ext x
    have h1 : x ∈ ⁅(U : Subgroup L), (U : Subgroup L)⁆ ↔
        e' x ∈ ⁅rootGroup J hJ, rootGroup J hJ⁆ := by
      rw [← hU, ← Subgroup.map_commutator, UnitaryModel.mem_map_iff]
    rw [h1, UnitaryModel.commutator_rootGroup J hJ hK hfix, Subgroup.mem_inf, Subgroup.mem_inf,
      ← hU, UnitaryModel.mem_map_iff, UnitaryModel.mem_centralizer_map_iff]
  · intro u hu
    have h1 : e' u ∈ rootGroup J hJ := by
      rw [← hU]
      exact (UnitaryModel.mem_map_iff e' _ u).2 hu
    have h2 := UnitaryModel.pow_prime_of_mem_rootGroup J hJ Fact.out hp2 h1
    rw [← map_pow, ← map_one e'] at h2
    exact e'.injective h2
  · obtain ⟨E, hER, hEab, hEcard⟩ :=
      UnitaryModel.exists_elemAbelian_rootGroup J hJ hK hfix Fact.out hp2
    refine ⟨E.map e'.symm.toMonoidHom, ?_, (UnitaryModel.isElemAbelian_map_iff e'.symm E).2 hEab,
      ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ : y ∈ (U : Subgroup L).map e'.toMonoidHom := hU ▸ hER hy
      show e'.symm (e' u) ∈ (U : Subgroup L)
      rw [MulEquiv.symm_apply_apply]
      exact hu
    · rw [Subgroup.card_map_of_injective (f := e'.symm.toMonoidHom) e'.symm.injective, hEcard]

end CFSG.AGLEmbedding
