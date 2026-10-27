module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHCentralCommutatorLaws.BCHCentralCommutatorLaws

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace BCHAddLaws

open scoped commutatorElement

open OddClassTwoBCH

variable {p : ℕ} {E : Type*} [Group E]

@[expose] def nsmul (n : ℕ) (x : BCH p E) : BCH p E :=
  Nat.rec zero (fun _ y => add y x) n

theorem nsmul_zero (x : BCH p E) : nsmul 0 x = zero := rfl

theorem nsmul_succ (n : ℕ) (x : BCH p E) : nsmul (n + 1) x = add (nsmul n x) x := rfl

theorem add_assoc (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
    (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) (x y z : BCH p E) :
    add (add x y) z = add x (add y z) :=
  BCHCentralCommutatorLaws.add_assoc hc x y z

theorem add_comm (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
    (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) (x y : BCH p E) :
    add x y = add y x :=
  BCHCentralCommutatorLaws.add_comm hc (hp.odd_of_ne_two hodd) hexp x y

theorem add_zero (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
    (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) (x : BCH p E) :
    add x zero = x :=
  BCHCentralCommutatorLaws.add_zero x

theorem zero_add (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
    (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) (x : BCH p E) :
    add zero x = x :=
  BCHCentralCommutatorLaws.zero_add x

theorem neg_add (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
    (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) (x : BCH p E) :
    add (neg x) x = zero :=
  BCHCentralCommutatorLaws.neg_add x

theorem toGroup_nsmul (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
    (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) (n : ℕ) (x : BCH p E) :
    toGroup (nsmul n x) = toGroup x ^ n := by
  induction n with
  | zero => simp [nsmul_zero]
  | succ n ih =>
    rw [nsmul_succ, toGroup_add, ih]
    have : ⁅toGroup x ^ n, toGroup x⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((Commute.refl _).pow_left n).eq
    rw [this, one_pow, inv_one, mul_one, pow_succ]

end BCHAddLaws
end ProofSupport
end CFSG.LocalAnalysis.RankThreeUC
