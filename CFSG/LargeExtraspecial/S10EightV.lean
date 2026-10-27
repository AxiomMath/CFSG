module

public import CFSG.LargeExtraspecial.S10EightU
public import CFSG.LargeExtraspecial.S10EightOD

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

theorem o3 (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (hno : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → ¬ S.HasTypeAInL g')
    (h7 : 7 ≤ S.width) :
    ∃ P : Subgroup S.O, P ≤ S.Mbar ∧ P ≠ ⊥ ∧ IsPGroup 3 P ∧
      ∀ m ∈ S.Mbar, ∀ p ∈ P, m * p * m⁻¹ ∈ P :=
  D.o3_of_space hCE hP (fusionCtl_of_lemma_3_13 X.H hno) h7
    (D.exists_good_space hCE hP hno h7 fun _ _ hk₀ hkP =>
      D.map_commutator_eq_of_mem_clSub_mul hCE hP h7 hk₀ hkP)

end Dec108

theorem timmesfeld_10_8_o3
    (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (hno : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → ¬ S.HasTypeAInL g')
    (X : Hyp10 S g t) (h7 : 7 ≤ S.width) :
    ∃ P : Subgroup S.O, P ≤ S.Mbar ∧ P ≠ ⊥ ∧ IsPGroup 3 P ∧
      ∀ m ∈ S.Mbar, ∀ p ∈ P, m * p * m⁻¹ ∈ P := by
  obtain ⟨Xb, Yb, D⟩ := exists_dec108 hCE X (timmesfeld_10_4_self hCE X h7) h7
  exact D.o3 hCE hP hno h7

end CFSG.LargeExtraspecial.S10
