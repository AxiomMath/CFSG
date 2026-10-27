module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_of_maximal_two_subgroup {N P : Subgroup X} (hP : IsPGroup 2 P)
    (hPN : P ≤ N) (hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → Q ≤ N → P ≤ Q → Q = P)
    (hnorm : normalizer (P : Set X) ≤ N) : ∃ T : Sylow 2 X, (T : Subgroup X) = P := by
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  refine ⟨T, le_antisymm ?_ hPT⟩
  by_contra hle
  have hlt : P < (T : Subgroup X) :=
    lt_of_le_of_ne hPT fun h => hle (le_of_eq h.symm)
  let P' : Subgroup (T : Subgroup X) := P.subgroupOf (T : Subgroup X)
  have hP'ne : P' ≠ ⊤ := by
    intro htop
    apply hle
    intro t ht
    have hmem : (⟨t, ht⟩ : (T : Subgroup X)) ∈ P' := by
      rw [htop]
      exact Subgroup.mem_top _
    simpa [P', Subgroup.mem_subgroupOf] using hmem
  have hP'lt : P' < ⊤ := lt_of_le_of_ne le_top hP'ne
  have hnc : NormalizerCondition (T : Subgroup X) := by
    haveI : Group.IsNilpotent (↑T : Subgroup X) := T.isPGroup'.isNilpotent
    exact normalizerCondition_of_isNilpotent
  obtain ⟨y, hyNorm, hyNotP'⟩ := IsConcreteLE.exists_of_lt (hnc P' hP'lt)
  have hyNormX : (y : X) ∈ normalizer (P : Set X) := by
    have hy : y ∈ (normalizer (P : Set X)).subgroupOf (T : Subgroup X) := by
      rw [Subgroup.subgroupOf_normalizer_eq hPT]
      exact hyNorm
    simpa [Subgroup.mem_subgroupOf] using hy
  have hyNotPX : (y : X) ∉ P := by
    intro hyP
    exact hyNotP' (by simpa [P', Subgroup.mem_subgroupOf] using hyP)
  let Q : Subgroup X := P ⊔ Subgroup.zpowers (y : X)
  have hQT : Q ≤ (T : Subgroup X) := by
    refine sup_le hPT ?_
    rw [Subgroup.zpowers_le]
    exact y.2
  have hQN : Q ≤ N := by
    refine sup_le hPN ?_
    rw [Subgroup.zpowers_le]
    exact hnorm hyNormX
  have hQgrp : IsPGroup 2 Q := T.isPGroup'.to_le hQT
  have hQeq : Q = P := hmax Q hQgrp hQN le_sup_left
  have hyQ : (y : X) ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact hyNotPX (hQeq ▸ hyQ)

end CFSG.EvenSporadicStandard.HNRecog.Harada

end
