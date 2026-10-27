module

import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isPGroup_center_subgroupOf {K Y : Subgroup X} (hKY : K ≤ Y) {p : ℕ}
    (h : IsPGroup p (center K)) : IsPGroup p (center (K.subgroupOf Y)) :=
  h.of_equiv (centerCongr (subgroupOfEquivOfLe hKY).symm)

omit [Finite X] in
theorem isCyclic_center_subgroupOf {K Y : Subgroup X} (hKY : K ≤ Y)
    (h : IsCyclic (center K)) : IsCyclic (center (K.subgroupOf Y)) :=
  isCyclic_of_surjective _ (centerCongr (subgroupOfEquivOfLe hKY).symm).surjective

omit [Finite X] in
theorem center_subgroupOf_ne_bot {K Y : Subgroup X} (hKY : K ≤ Y) {z : X} (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (hz1 : z ≠ 1) : center (K.subgroupOf Y) ≠ ⊥ := by
  have hmem : (⟨⟨z, hKY hzK⟩, mem_subgroupOf.2 hzK⟩ : K.subgroupOf Y) ∈
      center (K.subgroupOf Y) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (Subtype.ext (hzc _ (mem_subgroupOf.1 g.2)).symm)
  intro hbot
  rw [hbot, mem_bot] at hmem
  exact hz1 (congrArg (fun w : K.subgroupOf Y => ((w : Y) : X)) hmem)

theorem twoLocalOddRank_subgroupOf_le {K Y : Subgroup X} (hKY : K ≤ Y) :
    CFSG.twoLocalOddRank ↥(K.subgroupOf Y) ≤ CFSG.twoLocalOddRank X := by
  have hf : Function.Injective (K.subtype.comp (subgroupOfEquivOfLe hKY).toMonoidHom) :=
    K.subtype_injective.comp (subgroupOfEquivOfLe hKY).injective
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact CFSG.RankThree.PartOne.PlaneAux.evenRank_le_of_injective _ hf

theorem pRank_top_subgroupOf_le {K Y : Subgroup X} (hKY : K ≤ Y) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(K.subgroupOf Y)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hf : Function.Injective (K.subtype.comp (subgroupOfEquivOfLe hKY).toMonoidHom) :=
    K.subtype_injective.comp (subgroupOfEquivOfLe hKY).injective
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3 Nat.prime_three _ hf
    ⊤).trans (CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three le_top)

theorem not_le_normalizer_subgroupOf {P D Y : Subgroup X} (hPY : P ≤ Y) (hDP : D ≤ P)
    (hDn : ¬ P ≤ normalizer (D : Set X)) :
    ¬ P.subgroupOf Y ≤ normalizer ((D.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
  intro hle
  refine hDn fun g hg => mem_normalizer_fintype fun d hd => ?_
  have hgd : (⟨g, hPY hg⟩ : ↥Y) * ⟨d, hPY (hDP hd)⟩ * (⟨g, hPY hg⟩ : ↥Y)⁻¹ ∈
      (D.subgroupOf Y : Subgroup ↥Y) :=
    ((mem_normalizer_iff.1 (hle (mem_subgroupOf.2 hg))) _).1 (mem_subgroupOf.2 hd)
  exact mem_subgroupOf.1 hgd

end CFSG.LocalAnalysis.RankThreeTheoremC
