module

public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup

variable (F : Type) [Field F]

structure BlockOps (S : Subgroup (GL (Fin 4) F)) where
  blk : Fin 4 → Fin 4 → Subgroup ↥S
  blk_symm : ∀ a b, blk a b = blk b a
  perfect : ∀ a b, a ≠ b → ⁅blk a b, blk a b⁆ = blk a b
  commute : ∀ a b c d, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∀ g ∈ blk a b, ∀ h ∈ blk c d, g * h = h * g
  comm_refl : ∀ a b c, a ≠ b → c ≠ a → c ≠ b → ∀ g ∈ blk a b,
    (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F)
  perfect_le : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ P : Subgroup ↥S, (∀ g ∈ P, (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) ∧
      (g : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (g : GL (Fin 4) F)) →
      ⁅P, P⁆ = P → P ≤ blk a b

end CFSG.GH74.Generic.S1
