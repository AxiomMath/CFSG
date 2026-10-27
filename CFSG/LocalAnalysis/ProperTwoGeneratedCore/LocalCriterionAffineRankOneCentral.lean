module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneAction
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

universe u v

theorem central_involution_primitive_degree_le_two
    {F : Type u} [Group F] [Finite F]
    {Λ : Type v} [MulAction F Λ] [Finite Λ] [Nontrivial Λ]
    [MulAction.IsPretransitive F Λ] [FaithfulSMul F Λ]
    (a : Λ) (hmax : IsCoatom (MulAction.stabilizer F a))
    (t : F) (htcenter : t ∈ Subgroup.center F) (htorder : orderOf t = 2) :
    Nat.card Λ ≤ 2 := by
  have htne : t ≠ 1 := by
    intro h
    simp [h] at htorder
  have hTcenter : Subgroup.zpowers t ≤ Subgroup.center F :=
    Subgroup.zpowers_le.mpr htcenter
  let : (Subgroup.zpowers t).Normal := Subgroup.normal_of_le_center hTcenter
  have hTne : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    apply htne
    exact Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers t)
  let : MulAction.IsPretransitive (Subgroup.zpowers t) Λ :=
    normal_subgroup_pretransitive a hmax (Subgroup.zpowers t) hTne
  have hsurj : Function.Surjective (fun q : Subgroup.zpowers t => q • a) := by
    intro b
    exact MulAction.exists_smul_eq (Subgroup.zpowers t) a b
  calc
    Nat.card Λ ≤ Nat.card (Subgroup.zpowers t) :=
      Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := (Nat.card_zpowers t).trans htorder

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
