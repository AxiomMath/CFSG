module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

section Vocab

variable {G : Type} [Group G]

abbrev cA (S : Sylow 2 G) (R R' : Subgroup G) : Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)

@[expose] def BadElt (z a : G) : Prop :=
  z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))

@[expose] def BadSub (z : G) (D : Subgroup G) : Prop :=
  z ∉ zStarOf (Subgroup.centralizer (D : Set G))

theorem centralizer_zpowers (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute a x from h) k).eq

theorem badSub_zpowers_iff (z a : G) : BadSub z (Subgroup.zpowers a) ↔ BadElt z a := by
  unfold BadSub BadElt
  rw [centralizer_zpowers]

end Vocab

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
