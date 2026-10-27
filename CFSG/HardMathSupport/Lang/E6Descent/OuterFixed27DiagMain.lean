module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley DiagTorus
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


theorem e6DiagCase_unfolded :
    ∀ (K : Type) [Field K] [Finite K] (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ)
      (α : MulAut (adjointGroup Tag.E6 K)),
      3 ∣ Nat.card K - 1 → α = MulAut.conj g * rootDiagAut Tag.E6 K a → α ^ 3 = 1 →
      α ∉ inner (adjointGroup Tag.E6 K) → 27 ∣ Nat.card (fixedSubgroup α) := by
  classical
  intro K _ _ g a α h3 hα hα3 hαinn
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  set x : ModGL Tag.E6 K := (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a with hxdef
  have hαx : ∀ c : adjointGroup Tag.E6 K,
      ((α c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = x * c * x⁻¹ := by
    intro c
    rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_rootDiagAut, hxdef]
    group
  have hxA : x ∈ Dgrp K ⊔ adjointGroup Tag.E6 K :=
    mul_mem (Subgroup.mem_sup_right g.2) (Subgroup.mem_sup_left (rootDiagUnit_mem_Dgrp a))
  have hxC : x ∉ adjointGroup Tag.E6 K := by
    intro hx
    refine hαinn ⟨⟨x, hx⟩, ?_⟩
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [hαx c]
    rfl
  have hDC : ¬ Dgrp K ≤ adjointGroup Tag.E6 K := fun h =>
    hxC (by rw [sup_eq_right.2 h] at hxA; exact hxA)
  have hpowα : ∀ n : ℕ, ∀ c : adjointGroup Tag.E6 K,
      (((α ^ n) c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = x ^ n * c * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, MulAut.mul_apply, ih, hαx]
      group
  have hx3C : x ^ 3 ∈ adjointGroup Tag.E6 K := by
    have hN : ((adjointGroup Tag.E6 K).subgroupOf (Dgrp K ⊔ adjointGroup Tag.E6 K)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer Dgrp_le_normalizer_adjoint
    have hidx : ((adjointGroup Tag.E6 K).subgroupOf
        (Dgrp K ⊔ adjointGroup Tag.E6 K)).index = 3 := by
      change (adjointGroup Tag.E6 K).relIndex (Dgrp K ⊔ adjointGroup Tag.E6 K) = 3
      rw [DiagGroup.relIndex_sup_right_of_le_normalizer _ _ Dgrp_le_normalizer_adjoint,
        relIndex_adjoint_Dgrp h3 hDC]
    have h := Subgroup.pow_index_mem ((adjointGroup Tag.E6 K).subgroupOf
      (Dgrp K ⊔ adjointGroup Tag.E6 K)) (⟨x, hxA⟩ : ↥(Dgrp K ⊔ adjointGroup Tag.E6 K))
    rw [hidx] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hx3 : x ^ 3 = 1 := by
    have hcent : (⟨x ^ 3, hx3C⟩ : adjointGroup Tag.E6 K) ∈
        Subgroup.center (adjointGroup Tag.E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have h := hpowα 3 c
      rw [hα3, MulAut.one_apply] at h
      change (c : ModGL Tag.E6 K) * x ^ 3 = x ^ 3 * c
      have h' : x ^ 3 * (c : ModGL Tag.E6 K) = c * x ^ 3 := by
        have := congrArg (· * x ^ 3) h
        simp only [inv_mul_cancel_right] at this
        exact this.symm
      exact h'.symm
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have key := diag_main h3 hxA hxC hx3
  have hcard : Nat.card (fixedSubgroup α) =
      Nat.card ↥(Subgroup.centralizer {x} ⊓ adjointGroup Tag.E6 K) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : ModGL Tag.E6 K), ?_, c.1.2⟩
        invFun := fun z => ⟨⟨z.1, z.2.2⟩, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun z => rfl }
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h : α c.1 = c.1 := c.2
      have h2 := congrArg Subtype.val h
      rw [hαx] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    · have h := Subgroup.mem_centralizer_singleton_iff.1 z.2.1
      change α ⟨z.1, z.2.2⟩ = ⟨z.1, z.2.2⟩
      apply Subtype.ext
      rw [hαx]
      exact mul_inv_eq_iff_eq_mul.2 h.symm
  rw [hcard]
  exact key

end

end CFSG.HardMathSupport.Lang.E6Descent
