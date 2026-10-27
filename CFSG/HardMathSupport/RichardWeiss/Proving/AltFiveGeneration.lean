module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm

@[expose] def altFiveUPerm : Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def altFiveVPerm : Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4

set_option maxRecDepth 100000 in
theorem words5 : ∀ σ : Perm (Fin 5), σ.support.card = 3 →
    ∃ a b c d e f : Fin 3, σ = altFiveUPerm ^ (a : ℕ) * altFiveVPerm ^ (b : ℕ) *
      altFiveUPerm ^ (c : ℕ) * altFiveVPerm ^ (d : ℕ) * altFiveUPerm ^ (e : ℕ) *
      altFiveVPerm ^ (f : ℕ) := by
  decide +kernel

@[expose] def altFiveU : alternatingGroup (Fin 5) :=
  ⟨altFiveUPerm, IsThreeCycle.mem_alternatingGroup (card_support_eq_three_iff.mp (by decide))⟩

@[expose] def altFiveV : alternatingGroup (Fin 5) :=
  ⟨altFiveVPerm, IsThreeCycle.mem_alternatingGroup (card_support_eq_three_iff.mp (by decide))⟩

theorem altFiveU_val : (altFiveU : Perm (Fin 5)) = altFiveUPerm := rfl

theorem altFiveV_val : (altFiveV : Perm (Fin 5)) = altFiveVPerm := rfl

theorem altFive_closure_pair_eq_top :
    Subgroup.closure ({altFiveU, altFiveV} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  rw [eq_top_iff, ← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
  intro σ hσ
  have hσ' : (σ : Perm (Fin 5)).IsThreeCycle := hσ
  obtain ⟨a, b, c, d, e, f, h⟩ := words5 _ hσ'.card_support
  have hu : altFiveU ∈ Subgroup.closure ({altFiveU, altFiveV} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.subset_closure (by simp)
  have hv : altFiveV ∈ Subgroup.closure ({altFiveU, altFiveV} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.subset_closure (by simp)
  have hword : σ = altFiveU ^ (a : ℕ) * altFiveV ^ (b : ℕ) * altFiveU ^ (c : ℕ) *
      altFiveV ^ (d : ℕ) * altFiveU ^ (e : ℕ) * altFiveV ^ (f : ℕ) :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, altFiveU, altFiveV]
      exact h)
  rw [SetLike.mem_coe, hword]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hu _) (pow_mem hv _))
    (pow_mem hu _)) (pow_mem hv _)) (pow_mem hu _)) (pow_mem hv _)

end CFSG.HardMathSupport.RichardWeiss.Proving

end
