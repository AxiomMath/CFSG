module

public import CFSG.ClassicalInvolution.Q3.Q3T6XCore
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4

section Free

variable {F : Type} [Group F] [Finite F]

theorem twoElementsNormalize_of_centralizer_le {K : Subgroup F} {z : F}
    (h : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)) :
    Hat2A7R.TwoElementsNormalize K z :=
  fun _ _ _ _ _ hg => h hg

end Free

section Branch

@[expose] def Fusion3MinBranchTwin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU 3 1 K z →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (satU (.sl2 3 1) K z : Set G) →
        Fusion3MinOn G (invClass z)

theorem fusion3MinBranchTwin_of_branch (h : Fusion3MinBranch) : Fusion3MinBranchTwin :=
  fun G _ _ _ K z hb _ => h G K z hb

end Branch

theorem hypOmegaModDU_three_of_fusionMinTwin (h : Fusion3MinBranchTwin) : HypOmegaModDU 3 1 := by
  intro G _ _ _ K z hb
  have hm := hb.member_satU
  have hi := hb.intrinsic_satU
  by_cases hN :
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (satU (.sl2 3 1) K z : Set G)
  · exact hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) hm hi
      (omega5At_of_twoElementsNormalize hm (twoElementsNormalize_of_centralizer_le hN))
  · exact hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) hm hi
      (omega5At_of_twoElementsNormalize hm
        (twoElementsNormalize_of_min ⟨hm, hi⟩ (h G K z hb hN)))

end CFSG.ClassicalInvolution.Q3.Q3T6X
