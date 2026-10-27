module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section
namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement Pointwise MatrixGroups
namespace TwinExact
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_alpha_bot_gen {A : Subgroup G} (hA : alphaOf A = ⊥) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {x y : G} (hx : x ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)))
    (hy : y ∈ A) : x * y = y * x := by
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ alphaOf A :=
    le_sup_left.trans' (le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl))
  have h1 := hle (Subgroup.commutator_mem_commutator hx hy)
  rw [hA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end TwinExact
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
