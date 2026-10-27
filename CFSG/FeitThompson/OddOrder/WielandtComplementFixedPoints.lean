module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.FrobeniusWielandtFixedPointOrder
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A K : Type*} [Group A] [Group K] {U W : Subgroup A}

theorem fixedPoints_range_le_fixedPoints_comp_subtype (ρ : A →* MulAut K) (B : Subgroup A) :
    FixedPoints.subgroup ρ.range K ≤ FixedPoints.subgroup (ρ.comp B.subtype).range K := by
  intro v hv
  rw [mem_fixedPoints_comp_subtype_iff]
  exact fun b _ => (mem_fixedPoints_range_iff ρ).mp hv b

section Main

variable [Finite A] [Finite K] [Group.IsSolvable A] [Group.IsSolvable K]

theorem fixedPoints_comp_subtype_ne_bot_of_ne_top (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hUne : FixedPoints.subgroup (ρ.comp U.subtype).range K ≠ ⊤) :
    FixedPoints.subgroup (ρ.comp W.subtype).range K ≠ ⊥ := by
  intro hW
  have hA : FixedPoints.subgroup ρ.range K = ⊥ :=
    le_bot_iff.mp (hW ▸ fixedPoints_range_le_fixedPoints_comp_subtype ρ W)
  have key := natCard_mul_natCard_fixedPoints_range_pow_natCard_eq ρ hcop hU hUW hC
  rw [hA, hW, Subgroup.card_bot, one_pow, mul_one, mul_one] at key
  exact hUne (Subgroup.eq_top_of_card_eq _ key.symm)

theorem exists_ne_one_fixed_of_exists_not_fixed (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hUne : ∃ v : K, ¬ ∀ b ∈ U, ρ b v = v) :
    ∃ v : K, v ≠ 1 ∧ ∀ b ∈ W, ρ b v = v := by
  have hUne' : FixedPoints.subgroup (ρ.comp U.subtype).range K ≠ ⊤ := by
    obtain ⟨v, hv⟩ := hUne
    intro h
    exact hv ((mem_fixedPoints_comp_subtype_iff ρ U).mp (h ▸ Subgroup.mem_top v))
  obtain ⟨v, hv, hv1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp
    ((Subgroup.nontrivial_iff_ne_bot _).mpr
      (fixedPoints_comp_subtype_ne_bot_of_ne_top ρ hcop hU hUW hC hUne'))
  exact ⟨v, hv1, (mem_fixedPoints_comp_subtype_iff ρ W).mp hv⟩

end Main

end CFSG.FeitThompson
