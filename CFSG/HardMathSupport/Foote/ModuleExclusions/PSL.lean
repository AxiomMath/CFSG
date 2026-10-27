module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Common
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSLCore
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

theorem coverInv_psl (hGA : CFSG.Open.GriessAllModelsStatement) {n f : ℕ} (Q : Type) [Group Q]
    (hQ : StatedClassicalModel Q .PSL n 5 f) (hnf : 4 ≤ n ∨ 2 ≤ f) : CoverInv Q := by
  have hQ' := hQ
  obtain ⟨⟨-, hf, hn, -⟩, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hQ
  have hcard : Nat.card K = 5 ^ f := hKc
  have : CharP K 5 := charP_five_of_card hcard
  refine coverInv_of_inverts hGA hf hQ' (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  have hK5 : 4 ≤ n ∨ 5 < Nat.card K := by
    rcases hnf with h | h
    · exact Or.inl h
    · right
      rw [hcard]
      calc 5 < 5 ^ 2 := by norm_num
        _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨Φ, hΦ, hinv⟩ := psl_inverts hn hK5 (e w) hew1 hew2
  refine Or.inl ⟨e.symm.toMonoidHom.comp Φ, e.symm.injective.comp hΦ, fun u => ?_⟩
  have := congrArg e.symm (hinv u)
  simpa using this

end CFSG.HardMathSupport.Foote.ModuleExclusions
