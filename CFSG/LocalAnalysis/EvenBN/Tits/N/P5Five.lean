module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Base
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5StarG

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem pv2_inv_x5 : d.pv 2 * d.x₅ * (d.pv 2)⁻¹ = d.x₅⁻¹ := by
  obtain ⟨-, -, hconj, -, hH, -⟩ := Model.parrottV_two_facts
  have hVD : Model.parrottV 2 ∈ titsD := titsH_le_titsD hH
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD Model.hatX_facts.1
  have h1 := d.lift_conj hVD hXD
  rw [hconj, d.lift_inv hXD] at h1
  exact h1.symm

theorem pv2_mem_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.pv 2 ∈ Hg d :=
  M_le_Hg h49 hd (sylT_le_M hd (pv2_mem_sylT hd))

theorem star_pv2_inv_x5 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    star d (d.pv 2) * star d d.x₅ * (star d (d.pv 2))⁻¹ = (star d d.x₅)⁻¹ := by
  rw [star_eq, star_eq, ← actFun_conj d.s56V (pv2_mem_Hg h49 hd) (x5_mem_Hg h49 hd), pv2_inv_x5,
    actFun_inv d.s56V (x5_mem_Hg h49 hd)]

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
