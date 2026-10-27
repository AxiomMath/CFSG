module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem sylow_of_sylow_normalizer_intersection
    (p : ℕ) (hp : p.Prime) (D W : Subgroup G) (hW : IsPGroup p W)
    (hWD : W ≤ D)
    (hnormal : ∃ P : Sylow p (D ⊓ Subgroup.normalizer (W : Set G) : Subgroup G),
      (P : Subgroup (D ⊓ Subgroup.normalizer (W : Set G) : Subgroup G)).map
        (D ⊓ Subgroup.normalizer (W : Set G)).subtype = W) :
    ∃ Q : Sylow p D, (Q : Subgroup D).map D.subtype = W := by
  let B := D ⊓ Subgroup.normalizer (W : Set G)
  obtain ⟨P, hP⟩ := hnormal
  have hWi : IsPGroup p (W.subgroupOf D) :=
    hW.comap_of_injective D.subtype D.subtype_injective
  obtain ⟨Q, hWQ⟩ := hWi.exists_le_sylow
  let V := (Q : Subgroup D).map D.subtype
  have hWV : W ≤ V := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWD]
    exact Subgroup.map_mono hWQ
  by_cases heq : V = W
  · exact ⟨Q, heq⟩
  have hstrict : W < V := lt_of_le_of_ne hWV (Ne.symm heq)
  let U := V ⊓ Subgroup.normalizer (W : Set G)
  have hgrowth : W < U :=
    pSubgroup_lt_normalizer_intersection p hp W V (Q.isPGroup'.map D.subtype) hstrict
  have hUB : U ≤ B := inf_le_inf (Subgroup.map_subtype_le _) le_rfl
  have hUp : IsPGroup p U := (Q.isPGroup'.map D.subtype).of_injective
    (Subgroup.inclusion (show U ≤ V from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hUi : IsPGroup p (U.subgroupOf B) :=
    hUp.comap_of_injective B.subtype B.subtype_injective
  have hPU : (P : Subgroup B) ≤ U.subgroupOf B := by
    intro x hx
    exact hgrowth.le (hP ▸ Subgroup.mem_map_of_mem B.subtype hx)
  have hsame := P.is_maximal' hUi hPU
  have hmap := congrArg (Subgroup.map B.subtype) hsame
  rw [hP, Subgroup.map_subgroupOf_eq_of_le hUB] at hmap
  exact (hgrowth.ne hmap.symm).elim

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
