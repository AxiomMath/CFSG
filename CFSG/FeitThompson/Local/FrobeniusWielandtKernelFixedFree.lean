module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.FrobeniusWielandtFixedPointOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A K : Type*} [Group A] [Group K] {U W : Subgroup A}

theorem natCard_fixedPoints_eq_one (ρ : A →* MulAut K) (B : Subgroup A)
    (hC : ∀ v : K, (∀ b ∈ B, ρ b v = v) → v = 1) :
    Nat.card {v : K // ∀ b ∈ B, ρ b v = v} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext (by rw [hC x.1 x.2, hC y.1 y.2])⟩, ⟨⟨1, fun b _ => by simp⟩⟩⟩

section Main

variable [Finite A] [Finite K] [Group.IsSolvable A] [Group.IsSolvable K]

theorem natCard_eq_natCard_fixedPoints_pow_natCard (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hCU : ∀ v : K, (∀ b ∈ U, ρ b v = v) → v = 1) :
    Nat.card K = Nat.card {v : K // ∀ b ∈ W, ρ b v = v} ^ Nat.card W := by
  have key := natCard_mul_natCard_fixedPoints_pow_natCard_eq ρ hcop hU hUW hC
  rw [natCard_fixedPoints_eq_one ρ ⊤ (fun v hv => hCU v fun b _ => hv b trivial),
    natCard_fixedPoints_eq_one ρ U hCU, one_pow, mul_one, one_mul] at key
  exact key

theorem natCard_eq_natCard_fixedPoints_range_pow_natCard (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hCU : FixedPoints.subgroup (ρ.comp U.subtype).range K = ⊥) :
    Nat.card K = Nat.card (FixedPoints.subgroup (ρ.comp W.subtype).range K) ^ Nat.card W := by
  rw [natCard_fixedPoints_comp_subtype_eq_natCard_subtype]
  refine natCard_eq_natCard_fixedPoints_pow_natCard ρ hcop hU hUW hC fun v hv => ?_
  have hv' : v ∈ FixedPoints.subgroup (ρ.comp U.subtype).range K :=
    (mem_fixedPoints_comp_subtype_iff ρ U).2 hv
  rw [hCU, Subgroup.mem_bot] at hv'
  exact hv'

end Main

end CFSG.FeitThompson
