module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma37F_of_35_36 (h35 : Asc82Lemma35) (h36 : Asc82Lemma36) : Asc82Lemma37F := by
  intro G _ _ t L hS z g hz hw J hJ
  obtain ⟨hJcomp, hJF⟩ := hJ
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  obtain ⟨K, hP⟩ := exists_sec3PocketData_of_isI4PlusIn hS.involution hS.component
    (inFStar_of_inF hS.inF) hnorm hz
  have hP' := hP.conjugate g
  have htw : t ∈ centralizer ({g⁻¹ * z * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.1 hw t (Set.mem_singleton t)).symm
  have hJN : IsComponentIn J (centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * z * g} : Set G)) :=
    IsComponentIn.of_normal_inf_centralizer hS.component.le hnorm hJcomp
  have hJpair : IsComponentIn J (centralizer ({t, g⁻¹ * z * g} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact hJN
  exact h35 G t L hS (g⁻¹ * t * g) (CFSG.conjugate L g) (g⁻¹ * z * g)
    (CFSG.conjugate K g) t hP' hS.involution htw J ⟨hJpair, hJF⟩

end CFSG.OddStandard.SmallF3.Omega
