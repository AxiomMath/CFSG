module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm

@[expose] def kleinPred (x : alternatingGroup (Fin 4)) : Bool :=
  decide ((x : Perm (Fin 4)) = 1 ∨
    (x : Perm (Fin 4)) = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
    (x : Perm (Fin 4)) = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
    (x : Perm (Fin 4)) = Equiv.swap 0 3 * Equiv.swap 1 2)

theorem kleinPred_one : kleinPred 1 = true := by decide

theorem kleinPred_mul : ∀ x y : alternatingGroup (Fin 4),
    kleinPred x = true → kleinPred y = true → kleinPred (x * y) = true := by decide

theorem kleinPred_inv : ∀ x : alternatingGroup (Fin 4),
    kleinPred x = true → kleinPred x⁻¹ = true := by decide

theorem kleinPred_conj : ∀ g x : alternatingGroup (Fin 4),
    kleinPred x = true → kleinPred (g * x * g⁻¹) = true := by decide

@[expose] def kleinFour : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {x | kleinPred x = true}
  mul_mem' := fun {a b} ha hb => kleinPred_mul a b ha hb
  one_mem' := kleinPred_one
  inv_mem' := fun {x} hx => kleinPred_inv x hx

instance : kleinFour.Normal :=
  ⟨fun n hn g => kleinPred_conj g n hn⟩

@[expose] def altOf (σ : Perm (Fin 4)) (h : sign σ = 1) : alternatingGroup (Fin 4) :=
  ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr h⟩

theorem not_isSimpleGroup_alt_four : ¬ IsSimpleGroup (alternatingGroup (Fin 4)) := by
  intro h
  rcases Subgroup.Normal.eq_bot_or_eq_top kleinFour with hb | ht
  · have hmem : altOf (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide) ∈ kleinFour := by
      show kleinPred _ = true
      decide
    rw [hb, Subgroup.mem_bot] at hmem
    have h1 := congrArg Subtype.val hmem
    exact absurd h1 (by decide)
  · have hmem : altOf (Equiv.swap 0 1 * Equiv.swap 1 2) (by decide) ∈ kleinFour := by
      rw [ht]
      exact Subgroup.mem_top _
    have hk : kleinPred (altOf (Equiv.swap 0 1 * Equiv.swap 1 2) (by decide)) = true := hmem
    exact absurd hk (by decide)

theorem five_le_of_isSimpleGroup_alt {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) {n : ℕ} (e : S ≃* alternatingGroup (Fin n)) :
    5 ≤ n := by
  by_contra hlt
  push Not at hlt
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · have hc : IsMulCommutative (alternatingGroup (Fin n)) := by
      apply alternatingGroup.isMulCommutative_iff_card_le_three.mpr
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact hc.is_comm.comm _ _
  · have h4' : n = 4 := by omega
    subst h4'
    exact not_isSimpleGroup_alt_four ((MulEquiv.isSimpleGroup_congr e).mp inferInstance)

end CFSG.HardMathSupport.RichardWeiss.Proving

end
