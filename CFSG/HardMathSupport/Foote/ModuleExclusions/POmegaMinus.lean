module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Common
public import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthModels
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

theorem coverInv_pomegaMinus (hGA : CFSG.Open.GriessAllModelsStatement) {n f : ℕ} (Q : Type)
    [Group Q] (hQ : StatedClassicalModel Q .POmegaMinus n 5 f) : CoverInv Q := by
  have hQ' := hQ
  obtain ⟨⟨-, hf, hn⟩, K, hKf, hKfin, hKc, b, c, hbc, ⟨e⟩⟩ := hQ
  have hcard : Nat.card K = 5 ^ f := hKc
  have : CharP K 5 := charP_five_of_card hcard
  refine coverInv_of_inverts hGA hf hQ' (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  exact invData_of_equiv e (pomegaMinus_involution hn hbc (e w) hew1 hew2)

end CFSG.HardMathSupport.Foote.ModuleExclusions
