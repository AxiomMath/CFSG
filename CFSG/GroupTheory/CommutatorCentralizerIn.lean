module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

def commutatorCentralizerIn (M C T : Subgroup G)
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) : Subgroup G where
  carrier := {x : G | x ∈ M ∧ ∀ t ∈ T, ⁅x, t⁆ ∈ C}
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun t ht => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hconj : x * ⁅y, t⁆ * x⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hMC hxM) _).mp (hy t ht)
    exact C.mul_mem hconj (hx t ht)
  one_mem' := by
    refine ⟨M.one_mem, fun t ht => ?_⟩
    simp
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun t ht => ?_⟩
    rw [commutatorElement_inv_left]
    have hconj : x⁻¹ * ⁅x, t⁆⁻¹ * (x⁻¹)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hMC (M.inv_mem hxM)) _).mp
        (C.inv_mem (hx t ht))
    simpa [commutatorElement_inv] using hconj

@[simp]
theorem mem_commutatorCentralizerIn {M C T : Subgroup G}
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) {x : G} :
    x ∈ commutatorCentralizerIn M C T hMC ↔ x ∈ M ∧ ∀ t ∈ T, ⁅x, t⁆ ∈ C :=
  Iff.rfl

end CFSG.GroupTheory

end
