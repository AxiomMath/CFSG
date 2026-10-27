module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Common
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUCore
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

theorem coverInv_psu_all (hGA : CFSG.Open.GriessAllModelsStatement) {n f : ℕ} (Q : Type) [Group Q]
    (hQ : StatedClassicalModel Q .PSU n 5 f) : CoverInv Q := by
  have hQ' := hQ
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hQ
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  refine coverInv_of_inverts hGA hf hQ' (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  refine invData_of_equiv e ?_
  rcases psu_inverts hn hf hKc (e w) hew1 hew2 with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

end CFSG.HardMathSupport.Foote.ModuleExclusions
