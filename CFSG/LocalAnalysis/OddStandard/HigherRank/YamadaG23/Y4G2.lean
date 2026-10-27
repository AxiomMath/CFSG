module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y43a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_normT2_F (c : Ctx4 s e) (h42 : IsSylowIn 2 (⊤ : Subgroup G) s.T₂) :
    ∀ x ∈ s.T₂, x ∈ normalizer (s.fr.F : Set G) → x ∈ s.T := by
  intro x hxT2 hxN
  have hH : F33Hyp s e := c.toF33
  obtain ⟨v, hvV, hv⟩ := f3_tX_sub hH x (y4_T2_le_X c hxT2)
  have hvF : v ∈ s.fr.F := y54_V_le_F hH hvV
  have hxX : x ∈ f4X s := by
    refine y4_mem_normalizer_of_conj_mem (H := f4P s) ?_
    intro p hp
    rcases y54_mem_P s hp with hpF | ⟨f, hfF, rfl⟩
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxN p).mp hpF)
    · have hf' : x * f * x⁻¹ ∈ s.fr.F := (Subgroup.mem_normalizer_iff.mp hxN f).mp hfF
      have hcalc : x * (f * s.t) * x⁻¹ = ((x * f * x⁻¹) * v) * s.t := by
        calc x * (f * s.t) * x⁻¹ = (x * f * x⁻¹) * (x * s.t * x⁻¹) := by group
          _ = (x * f * x⁻¹) * (v * s.t) := by rw [hv]
          _ = ((x * f * x⁻¹) * v) * s.t := by group
      rw [hcalc]
      exact mul_mem (Subgroup.mem_sup_left (s.fr.F.mul_mem hf' hvF))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have hxH : x ∈ s.H := y4_f4X_le_H c h42 hxX
  rw [← y4_T2_inf_H c]
  exact ⟨hxH, hxT2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
