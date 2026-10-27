module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84V1Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84V2Cmp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84V2Dec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84V2Lay
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84V3Typ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84V4Om5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step84End_of (F : Sec8T84Base) (hGi : Sec8T84FactGamInner) (hI4 : Sec8T84FactI4m)
    (hO5t : Sec8T84FactOm5Tab) : Asc82Step84End := by
  intro G _ _ t L S z g B γ K U h
  have hLM : IsOm6M L := ⟨h.ctx.component.isQuasisimple, h.ctx.omega6m⟩
  have hγ2 : γ * γ = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq h.inv)
  have hdec := sec8t84v_cent_decomp F h.ctx h.mem h.gen
  obtain ⟨hL29, -⟩ := sec8t84g_K0_comp F h.ctx h.mem h.inv h.outer
  have hK0 := sec8t84v_K0_comp_inf F h
  have htK := sec8t84v_t_mem_normalizer h
  have hinner : ∀ u ∈ K ⊓ centralizer ({t} : Set G), orderOf u = 2 →
      InnerOn (layerCent L γ) u := by
    intro u hu hu2
    refine sec8t84v_inner_of_sq hGi hLM hγ2 h.outer (sec8t84v_gamma_mem_normalizer F h) hdec u
      ⟨h.comp.le hu.1, hu.2⟩ ?_
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hu2)
  rcases sec8t84v_cls F h with hK | hK
  · exact sec8t84v_om5_false hO5t hK h.ctx.involution htK hK0 hL29 hinner
  · exact sec8t84v_om6m_false F.hM hI4 hK h.ctx.involution htK hK0 hL29 h.U_e16 h.U_le h.t_norm
      hinner

end CFSG.OddStandard.SmallF3.Omega
