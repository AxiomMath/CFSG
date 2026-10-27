module

public import CFSG.ClassicalInvolution.Q3.Q3ZACrossModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups commutatorElement
open Matrix

theorem hom_commute {H K : Type} [Group H] [Group K] (θ : H →* K) {a b : H}
    (h : a * b = b * a) : Commute (θ a) (θ b) := by
  show θ a * θ b = θ b * θ a
  rw [← map_mul, ← map_mul, h]

theorem comm_of_mul_eq {G' : Type} [Group G'] {q t c : G'} (h : q * t = c * t * q) :
    ⁅q, t⁆ = c := by
  have h1 : q * t * q⁻¹ = c * t := by
    rw [h]
    group
  rw [commutatorElement_def, h1]
  group

section Cross

variable {G : Type} [Group G]

theorem iota_lb0 (x : SL(2, F3)) : iotaHom (longBlock F3 2 0 x) = longBlock F3 2 0 x := by
  show longInv F3 2 0 * longBlock F3 2 0 x * (longInv F3 2 0)⁻¹ = longBlock F3 2 0 x
  rw [longInv, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  have hc : (-1 : SL(2, F3)) * x = x * (-1) := by
    ext i j
    simp
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem iota_lb1 (x : SL(2, F3)) : iotaHom (longBlock F3 2 1 x) = longBlock F3 2 1 x := by
  show longInv F3 2 0 * longBlock F3 2 1 x * (longInv F3 2 0)⁻¹ = longBlock F3 2 1 x
  rw [longInv]
  exact mul_inv_eq_iff_eq_mul.2
    (commute_longBlock_longBlock (zero_ne_one : (0 : Fin 2) ≠ 1) (-1) x).eq

end Cross

end CFSG.ClassicalInvolution.Q3.Q3ZA
