module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.FrobeniusWielandtFixedPointOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A K : Type*} [Group A] [Group K] {U W : Subgroup A}

section Main

variable [Finite A] [Finite K] [Group.IsSolvable A] [Group.IsSolvable K]

theorem le_ker_of_forall_fixedPoints_eq_one (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hCK : ∀ v : K, (∀ w ∈ W, ρ w v = v) → v = 1) :
    U ≤ ρ.ker := by
  have hcard : ∀ B : Subgroup A, W ≤ B → Nat.card {v : K // ∀ b ∈ B, ρ b v = v} = 1 := by
    intro B hB
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun v v' => Subtype.ext ?_⟩, ⟨⟨1, by simp⟩⟩⟩
    rw [hCK v fun w hw => v.2 w (hB hw), hCK v' fun w hw => v'.2 w (hB hw)]
  have key := natCard_mul_natCard_fixedPoints_pow_natCard_eq ρ hcop hU hUW hC
  rw [hcard ⊤ le_top, hcard W le_rfl, one_pow, mul_one, mul_one] at key
  have htop : FixedPoints.subgroup (ρ.comp U.subtype).range K = ⊤ :=
    Subgroup.eq_top_of_card_eq _ <| by
      rw [natCard_fixedPoints_comp_subtype_eq_natCard_subtype, ← key]
  intro u hu
  rw [MonoidHom.mem_ker]
  ext v
  exact (mem_fixedPoints_comp_subtype_iff ρ U).1 (htop ▸ Subgroup.mem_top v) u hu

theorem apply_eq_self_of_forall_fixedPoints_eq_one (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hCK : ∀ v : K, (∀ w ∈ W, ρ w v = v) → v = 1) :
    ∀ u ∈ U, ∀ v : K, ρ u v = v := by
  intro u hu v
  have hker := le_ker_of_forall_fixedPoints_eq_one ρ hcop hU hUW hC hCK hu
  rw [MonoidHom.mem_ker] at hker
  rw [hker, MulAut.one_apply]

theorem le_ker_of_fixedPoints_range_eq_bot (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hCK : FixedPoints.subgroup (ρ.comp W.subtype).range K = ⊥) :
    U ≤ ρ.ker :=
  le_ker_of_forall_fixedPoints_eq_one ρ hcop hU hUW hC fun _ hv =>
    Subgroup.mem_bot.1 (hCK ▸ (mem_fixedPoints_comp_subtype_iff ρ W).2 hv)

end Main

end CFSG.FeitThompson
