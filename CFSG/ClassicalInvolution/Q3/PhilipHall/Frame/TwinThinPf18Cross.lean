module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossSetting

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem exists_vector_five
    (J : AEIdent (fam K (conjSub g (piGen π))) 5) :
    ∀ J' ∈ π, ∀ u : G, IsUniqueInvolution J' u →
      ∃ w : Wr 5, Cross.InducedBy J u w ∧ w.perm = 1 := by
  intro J' hJ' u hu
  have hm : 5 ≤ 5 := le_rfl
  have htw : S.TwinLab 5 := S.twinLab_of_ne_eight hm (by norm_num)
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  obtain ⟨w, hw, hfix⟩ := S.exists_induced_fix hm (Cross.aeAut_of_five_le hm) htw J hJ' hu hlab
  exact ⟨w, hw, TwinThinPf18.perm_eq_one_of_fix_four_fin5 w.perm α h hfix⟩

theorem thinCrossPair_five
    (J : AEIdent (fam K (conjSub g (piGen π))) 5) : ThinCrossPair K π g := by
  have hm : 5 ≤ 5 := le_rfl
  have hm8 : (5 : ℕ) ≠ 8 := by norm_num
  obtain ⟨hO', hO⟩ := S.pCoreOf_le_Dz_of_odd hm (by norm_num) J
  exact S.thinCrossPair_of_vector hm (Cross.aeAut_of_five_le hm) (S.twinLab_of_ne_eight hm hm8) J
    hO' hO (S.exists_vector_five J)

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
