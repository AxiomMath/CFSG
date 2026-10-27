module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TI4mCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TI4mCov
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TI4mOut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84FactI4m_holds : Sec8T84FactI4m := by
  intro G _ _ L hL s hs2 hsn hind A hA
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ := hind
  obtain ⟨ρ, hρ⟩ := ff6m_cover_of_model hL hdim hs hs2
  obtain ⟨E, hEn, hLie, hP⟩ := ff6m_N1_layerModel hQ hdim hsgn hx
  haveI : E.Normal := hEn
  obtain ⟨hEs, hEnc⟩ := ff_simple_of_lieModel_psl2 hLie
  obtain ⟨ε, u, hu2, hεu⟩ := sec8t84t_KN1_char hQ hdim hsgn hx
  haveI : Group.IsPerfect ↥E := (ff_isQuasisimple_of_simple hEs hEnc).1
  have huE : u ∉ E := sec8t84t_not_mem_of_char E ε (by rw [hεu]; decide)
  exact sec8t84t_outer_of_cover hρ E hEs hP
    (fun c hc => sec8t84t_centB_eq_one hQ hdim hsgn E hEs hEnc hP hc) hu2 huE hA

end CFSG.OddStandard.SmallF3.Omega
