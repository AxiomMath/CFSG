module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootQd
public import CFSG.LocalAnalysis.EvenBN.TwoF4.Main

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open CFSG.Blueprint

section Conditional


theorem twoF4CenterlessExclusion_of_gms (hGMS : GMSK.GMSSuzukiSharpKRankOneStatement) :
    TwoF4CenterlessExclusion := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ f _ _ hm
  obtain ⟨h, -, -⟩ := exists_setup hnonab hL hcore S hS hm
  obtain ⟨d⟩ := h.nonempty_levelOneData hGMS hK
  exact d.false_of_gms hGMS hK

end Conditional

section Certified


theorem twoF4CenterlessExclusion : TwoF4CenterlessExclusion :=
  twoF4CenterlessExclusion_of_gms GMSK.gmsSuzukiSharpKRankOne

theorem bnFamily_twistedF4 :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ LieModel X .twistedF4 0 2 f :=
  bnFamily_twistedF4_of_exclusion twoF4CenterlessExclusion

end Certified

end CFSG.LocalAnalysis.EvenBN.TwoF4
