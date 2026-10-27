module

public import CFSG.Quasithin.Background.G6Natural

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Quasithin

namespace Delta5Fix

local instance instDecidablePredMemCore : DecidablePred (· ∈ G6.coreMod 5) :=
  fun x => decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) G6.mem_coreMod.symm

def vec4 (a b c d : ZMod 2) : G6.coreMod 5 :=
  ⟨Multiplicative.ofAdd (![a, b, c, d, a + b + c + d] : Fin 5 → ZMod 2), by
    rw [G6.mem_coreMod]
    revert a b c d
    decide⟩

set_option synthInstance.maxSize 2000 in
theorem no_fixed : ∀ w : G6.coreMod 5,
    (∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → G6.coreAct 5 σ w = w) → w = 1 := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
theorem comm_closure : ∀ w : G6.coreMod 5, w ∈ Subgroup.closure
    {x : G6.coreMod 5 | ∃ σ : Equiv.Perm (Fin 5), ∃ u : G6.coreMod 5,
      Equiv.Perm.sign σ = 1 ∧ x = G6.coreAct 5 σ u * u⁻¹} := by
  let g : Fin 4 → G6.coreMod 5 := fun i =>
    ![vec4 1 0 0 0, vec4 0 1 0 0, vec4 0 0 1 0, vec4 0 0 0 1] i
  have hcover : ∀ w : G6.coreMod 5, ∃ a b c d : Bool,
      w = (if a then g 0 else 1) * (if b then g 1 else 1) * (if c then g 2 else 1) *
        (if d then g 3 else 1) := by
    decide +kernel
  have hgen : ∀ i : Fin 4, ∃ σ : Equiv.Perm (Fin 5), ∃ u : G6.coreMod 5,
      Equiv.Perm.sign σ = 1 ∧ g i = G6.coreAct 5 σ u * u⁻¹ := by
    decide +kernel
  intro w
  obtain ⟨a, b, c, d, rfl⟩ := hcover w
  have hite : ∀ (i : Fin 4) (t : Bool), (if t then g i else 1) ∈ Subgroup.closure
      {x : G6.coreMod 5 | ∃ σ : Equiv.Perm (Fin 5), ∃ u : G6.coreMod 5,
        Equiv.Perm.sign σ = 1 ∧ x = G6.coreAct 5 σ u * u⁻¹} := by
    intro i t
    cases t
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (hgen i)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hite 0 a) (hite 1 b))
    (hite 2 c)) (hite 3 d)

end Delta5Fix

end CFSG.CGT.PushingUpLit.SYMB
