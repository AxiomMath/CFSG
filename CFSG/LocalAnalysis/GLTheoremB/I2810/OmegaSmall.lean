module

import CFSG.LieType.ChevTwo.OrthogonalPlusTwo
import CFSG.CharacterTheory.Burnside
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.OrthogonalForm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaSmall

theorem solvable_plus_two : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := by
  have hcard : Nat.card ↥(orthGroup (StatedQuadPlus 2 (ZMod 2))) = 2 ^ 3 * 3 ^ 2 := by
    rw [card_orthGroup_quadPlus_two, Nat.card_zmod]; norm_num
  haveI : Fintype ↥(orthGroup (StatedQuadPlus 2 (ZMod 2))) := Fintype.ofFinite _
  have hO : Group.IsSolvable ↥(orthGroup (StatedQuadPlus 2 (ZMod 2))) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
  have hle : StatedOmega (StatedQuadPlus 2 (ZMod 2)) ≤ orthGroup (StatedQuadPlus 2 (ZMod 2)) := by
    show ⁅orthGroup (StatedQuadPlus 2 (ZMod 2)), orthGroup (StatedQuadPlus 2 (ZMod 2))⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro g hg h hh
    simp only [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg))
      (Subgroup.inv_mem _ hh)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.injective

theorem nontrivial_plus_two : Nontrivial ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := by
  obtain ⟨x, y, hxy⟩ := CFSG.LieType.ChevTwo.exists_commutatorElement_ne_one_SL2_zmod_two
  have h1 : j1 ⁅x, y⁆ ∈ StatedOmega (StatedQuadPlus 2 (ZMod 2)) := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (j1_mem_orthGroup x) (j1_mem_orthGroup y)
  refine ⟨⟨⟨j1 ⁅x, y⁆, h1⟩, 1, fun h => hxy ?_⟩⟩
  apply j1_injective
  rw [map_one]
  exact congrArg Subtype.val h

theorem subsingleton_of_perfect_solvable {G H : Type*} [Group G] [Group H] (hG : commutator G = ⊤)
    (θ : G →* H) (hθ : Function.Surjective θ) [Group.IsSolvable H] : Subsingleton H := by
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  have h1 : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).map θ = ⁅(⊤ : Subgroup H), ⊤⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective θ hθ]
  have h2 : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := hG
  rw [h2, Subgroup.map_top_of_surjective θ hθ] at h1
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne h1.symm

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaSmall
