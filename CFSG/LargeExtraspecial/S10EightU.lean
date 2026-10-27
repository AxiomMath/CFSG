module

public import CFSG.LargeExtraspecial.S10EightT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem o3_of_space (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (hF : S6.FusionCtl S g)
    (h7 : 7 ≤ S.width)
    (hU : ∃ U : Submodule (ZMod 2) S.Qt, finrank (ZMod 2) U = 3 ∧ ∀ v ∈ U, v ≠ 0 →
      ∃ k : S.M, v = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∧
        ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆) :
    ∃ P : Subgroup S.O, P ≤ S.Mbar ∧ P ≠ ⊥ ∧ IsPGroup 3 P ∧
      ∀ m ∈ S.Mbar, ∀ p ∈ P, m * p * m⁻¹ ∈ P := by
  refine ⟨⁅Yb, Yb⁆, fun y hy => Rbar_le_Mbar (D.dec.le_Rbar_right
      ((D.dec.mem_commutator_iff).mp hy).1), D.dec.commutator_ne_bot,
    IsPGroup.of_card (n := 1) (by rw [D.dec.card_commutator, pow_one]), ?_⟩
  intro m hm p hp
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hm
  rw [← D.good_of_space hCE hP hF h7 hU k]
  exact ⟨p, hp, rfl⟩

end Dec108

end CFSG.LargeExtraspecial.S10
