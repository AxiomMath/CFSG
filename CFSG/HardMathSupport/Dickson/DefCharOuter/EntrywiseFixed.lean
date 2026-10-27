module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
import CFSG.LieType.Chevalley.OddPinnedComponents

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement


theorem perfectInLayer_entrywiseAdjointAut (τ : Tag) {M : Type} [Field M] [Finite M]
    (hM : ringChar M ≠ 2) (σ : M ≃+* M) : PerfectInLayer (entrywiseAdjointAut τ σ) := by
  classical
  set β := entrywiseAdjointAut τ σ with hβ
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hM
    have := congrArg (fixSubfield σ).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨hs, hnc, -⟩ := odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2
  obtain ⟨-, -, -, hJΓ, -, hnormal, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure τ M hM σ
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ M := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup β), ((n : ↥(adjointGroup τ M)) : ModGL τ M) ∈
      entrywiseFixedGroup τ σ := fun n =>
    ⟨(n : ↥(adjointGroup τ M)).2, by
      have h1 : β n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup τ M) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ M)
    with hJ
  have hmemJ : ∀ x : ↥(adjointGroup τ M), x ∈ J ↔ (x : ModGL τ M) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup β := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  haveI hJn : (J.subgroupOf (fixSubgroup β)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup τ M)) : ModGL τ M), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup τ M)) : ModGL τ M), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  haveI := hs
  haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hq : CFSG.IsQuasisimple ↥J :=
    LieSemisimple.isQuasisimple_of_isSimpleGroup inferInstance hncJ
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥(fixSubgroup β)) : ↥(adjointGroup τ M)) : ModGL τ M) =
        ⁅(((y⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup τ M)) : ModGL τ M),
          (((x⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup τ M)) : ModGL τ M)⁆ := by
      simp [commutatorElement_def]
    rw [h2, ← hder]
    exact Subgroup.commutator_mem_commutator (hΓ _) (hΓ _)
  exact LieSemisimple.perfectInLayer_of_normal_quasisimple hJC hq hsol

end CFSG.HardMathSupport.Dickson.DefCharOuter
