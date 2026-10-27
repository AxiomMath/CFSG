module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27SmallU42
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27SmallJ2

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.J2Cover

theorem notU42
    (hcheck : Certificates.Seitz77Sec27.u42CensusCheck = true) : NotU42 := by
  intro N _ _ X t o h
  obtain ⟨e⟩ := equiv_of_lieModel h
  obtain ⟨M, hP, hA⟩ := exists_model e
  have hPA : M.P ≤ M.A := by
    rw [hP, hA, QP45_closure, QA45_closure]
    exact Subgroup.closure_mono
      (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  obtain ⟨ρ, hρ, hρA, hρP⟩ := exists_embedding_of_model o M hPA
  have census := u42CensusCheck_sound hcheck
  refine false_of_census_index_two o.loc ρ hρ M.A M.P hρA hρP ?_ ?_
  · rw [hA, hP, card_group QA45 QA45_ok, card_group QP45 QP45_ok, QA45_valid.2, QP45_valid.2]
  · intro h2 h1 h5
    have hc := census (ρ t) (by rw [← hA]; exact hρA t) h2 h1 (by rw [← hA]; exact h5)
    rw [hA, hP]
    exact hc


theorem notJ2
    (hcheck : Certificates.Seitz77Sec27.j2U0Check = true) : NotJ2 := by
  intro N _ _ X t o h
  obtain ⟨e⟩ := h
  let e' : ↥(layer N) ≃* P := e.trans nativeEquivP
  let M : AutModel ↥(layer N) (Equiv.Perm (Fin 315)) :=
    AutModel.ofRealization P R e' rAutEquiv (fun σ x => rConj_apply σ x)
  obtain ⟨ρ, hρ, hρR, hρP⟩ := exists_embedding_of_model o M P_le_R
  have census := j2Census hcheck
  exact false_of_census_J2 o.loc ρ hρ R P hρR hρP (by rw [card_R, card_P])
    census.1 census.2


end CFSG.OddStandard.Seitz77
