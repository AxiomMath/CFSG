module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace OddClassTwoBCH

@[expose] def BCH (p : ℕ) (E : Type*) [Group E] : Type _ := E

open scoped commutatorElement

variable {p : ℕ} {E : Type*} [Group E]

@[expose] def toGroup : BCH p E ≃ E := Equiv.refl _

@[expose] def ofGroup : E ≃ BCH p E := Equiv.refl _

@[expose] def add (x y : BCH p E) : BCH p E :=
  ofGroup ((toGroup x * toGroup y) *
    (⁅toGroup x, toGroup y⁆ ^ ((p + 1) / 2))⁻¹)

@[expose] def zero : BCH p E := ofGroup 1

@[expose] def neg (x : BCH p E) : BCH p E := ofGroup (toGroup x)⁻¹

theorem toGroup_add (x y : BCH p E) :
    toGroup (add x y) = (toGroup x * toGroup y) *
      (⁅toGroup x, toGroup y⁆ ^ ((p + 1) / 2))⁻¹ := rfl

@[simp] theorem toGroup_zero : toGroup (zero : BCH p E) = 1 := rfl

@[simp] theorem toGroup_neg (x : BCH p E) : toGroup (neg x) = (toGroup x)⁻¹ := rfl

end OddClassTwoBCH
end ProofSupport
end CFSG.LocalAnalysis.RankThreeUC
