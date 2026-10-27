module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6Pkg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Form

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
include H C ht

theorem apply_sub_mem_clSub_Wt {l : S.O} (hl : l ∈ S.Lbar g) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ S.clSub (S.QG ⊓ S.Qa g) :=
  apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hw hl

end Form

end CFSG.LargeExtraspecial.S9.RB

