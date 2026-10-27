module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def fzlD1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def fzlD2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def fzlV4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {x | x = 1 ∨ x = fzlD1 ∨ x = fzlD2 ∨ x = fzlD1 * fzlD2}
  one_mem' := by simp
  mul_mem' := by decide
  inv_mem' := by decide

instance fzlV4Decidable : DecidablePred (· ∈ fzlV4) := fun x =>
  decidable_of_iff (x = 1 ∨ x = fzlD1 ∨ x = fzlD2 ∨ x = fzlD1 * fzlD2) (by simp [fzlV4])

@[expose] def fzlK4 : Subgroup FzZ2xSigma4 :=
  (⊥ : Subgroup (Multiplicative (ZMod 2))).prod fzlV4

@[expose] def fzlK8 : Subgroup FzZ2xSigma4 :=
  (⊤ : Subgroup (Multiplicative (ZMod 2))).prod fzlV4

instance fzlK4Decidable : DecidablePred (· ∈ fzlK4) := fun x =>
  decidable_of_iff (x.1 = 1 ∧ x.2 ∈ fzlV4) (by simp [fzlK4, Subgroup.mem_prod])

instance fzlK8Decidable : DecidablePred (· ∈ fzlK8) := fun x =>
  decidable_of_iff (x.2 ∈ fzlV4) (by simp [fzlK8, Subgroup.mem_prod])

@[expose] def fzlKappa : FzZ2xSigma4 := (Multiplicative.ofAdd (1 : ZMod 2), 1)

structure FzF {G : Type} [Group G] (t x₁ x₂ : G)
    (f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4) : Prop where
  surj : Function.Surjective f
  ker : f.ker = (ctxW t x₁ x₂).subgroupOf (fzN2 t x₁ x₂)

end CFSG.OddStandard.SmallF3.FritzII
