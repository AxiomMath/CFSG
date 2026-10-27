module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.LieType.BorelTits (orthGroup)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open scoped commutatorElement

theorem statedOmega_quadPlus_two_le_range_jProd :
    StatedOmega (StatedQuadPlus 2 (ZMod 2)) ≤ (jProd (F := ZMod 2)).range := by
  have hidx : ((jProd (F := ZMod 2)).range.subgroupOf
      (orthGroup (StatedQuadPlus 2 (ZMod 2)))).index = 2 := relIndex_jProd_range
  show ⁅orthGroup (StatedQuadPlus 2 (ZMod 2)), orthGroup (StatedQuadPlus 2 (ZMod 2))⁆ ≤ _
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have key : ⁅(⟨g, hg⟩ : orthGroup (StatedQuadPlus 2 (ZMod 2))), ⟨h, hh⟩⁆ ∈
      (jProd (F := ZMod 2)).range.subgroupOf (orthGroup (StatedQuadPlus 2 (ZMod 2))) := by
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      inv_mem_iff, inv_mem_iff]
    tauto
  rw [Subgroup.mem_subgroupOf] at key
  simpa [commutatorElement_def] using key

theorem exists_commutatorElement_ne_one_SL2_zmod_two :
    ∃ x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), ⁅x, y⁆ ≠ 1 := by
  let x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ⟨Matrix.of ![![1, 1], ![0, 1]], by rw [Matrix.det_fin_two_of]; decide⟩
  let y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ⟨Matrix.of ![![1, 0], ![1, 1]], by rw [Matrix.det_fin_two_of]; decide⟩
  refine ⟨x, y, fun h => ?_⟩
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) (commutatorElement_eq_one_iff_mul_comm.mp h)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, x, y,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00
  revert h00
  decide

theorem not_isSimpleGroup_statedOmega_plus_two' :
    ¬ IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := by
  intro hS
  have hle := statedOmega_quadPlus_two_le_range_jProd
  have memΩ : ∀ x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      j1 ⁅x, y⁆ ∈ StatedOmega (StatedQuadPlus 2 (ZMod 2)) ∧
        j2 ⁅x, y⁆ ∈ StatedOmega (StatedQuadPlus 2 (ZMod 2)) := by
    intro x y
    rw [map_commutatorElement, map_commutatorElement]
    exact ⟨Subgroup.commutator_mem_commutator (j1_mem_orthGroup x) (j1_mem_orthGroup y),
      Subgroup.commutator_mem_commutator (j2_mem_orthGroup x) (j2_mem_orthGroup y)⟩
  let N : Subgroup ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
    (j1 (F := ZMod 2)).range.subgroupOf (StatedOmega (StatedQuadPlus 2 (ZMod 2)))
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hn
    obtain ⟨⟨a, b⟩, hab⟩ := MonoidHom.mem_range.mp (hle g.2)
    rw [jProd_apply] at hab
    refine MonoidHom.mem_range.mpr ⟨a * c * a⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hc, ← hab, map_mul, map_inv, mul_inv_rev]
    rw [mul_assoc (j1 a) (j2 b) (j1 c), ← (j1_j2_commute c b).eq]
    group
  obtain ⟨x, y, hxy⟩ := exists_commutatorElement_ne_one_SL2_zmod_two
  obtain ⟨h1, h2⟩ := memΩ x y
  rcases hS.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hmem : (⟨j1 ⁅x, y⁆, h1⟩ : ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2)))) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hxy
    apply j1_injective
    rw [map_one]
    exact congrArg Subtype.val hmem
  · have hmem : (⟨j2 ⁅x, y⁆, h2⟩ : ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2)))) ∈ N := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hmem
    exact hxy (eq_one_of_j1_eq_j2 hd).2

end CFSG.LieType.ChevTwo
