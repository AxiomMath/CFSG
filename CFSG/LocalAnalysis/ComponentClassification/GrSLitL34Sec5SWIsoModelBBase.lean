
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelBase
public import CFSG.LieType.Multipliers.L34

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem tabRep_yTab {t i : ℕ} (hi : i < 36) : TabRep (yTab t i) (yPerm t i) :=
  (tabRep_wordTab (tg t)).comp (tabRep_repTab hi)

theorem yPerm_mem_R (t i : ℕ) : yPerm t i ∈ R :=
  R.mul_mem (S_le_R (wordPerm_mem _)) (repPerm_mem i)

theorem sq_yTab_of {t i : ℕ} (hi : i < 36) (h2 : yPerm t i * yPerm t i = 1) :
    (comp 42 (yTab t i) (yTab t i) == idTab 42) = true :=
  (((tabRep_yTab hi).comp (tabRep_yTab hi)).beq_iff TabRep.idTab).2 h2

theorem outer_of_mem {p : ℕ × ℕ} (hp : p ∈ outerInvs) : p.1 < 64 ∧ p.2 < 36 ∧
    repInS.contains p.2 = false ∧ yPerm p.1 p.2 * yPerm p.1 p.2 = 1 := by
  obtain ⟨ht, hi⟩ := lt_of_mem_outerInvs hp
  simp only [outerInvs, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨i', -, hp⟩ := hp
  split_ifs at hp with hS
  · simp at hp
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hp
    refine ⟨ht, hi, by simpa using hS, ?_⟩
    exact (((tabRep_yTab hi).comp (tabRep_yTab hi)).beq_iff TabRep.idTab).1
      (List.mem_filter.mp ht').2

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
