module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Quo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutH74
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NC

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

section


namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem contradiction (hG : Sec4Glob G) : False := by
  have h𝒱 : IsPGroup 2 (ctxVN t tau x₁ x₂ lam rho) := hw.toCtx4Z.isPGroup_ctxVN
  obtain ⟨ℰ, hℰsyl, hVℰ⟩ :=
    S4B.exists_isSylowIn_of_le (K := ⊤) (U := ctxVN t tau x₁ x₂ lam rho) le_top h𝒱
  have hℰ : IsPGroup 2 ℰ := hℰsyl.2.1
  have hℰidx : ¬ 2 ∣ ℰ.index := by
    simpa only [Subgroup.relIndex_top_right] using hℰsyl.2.2
  have htV : t ∈ ctxVN t tau x₁ x₂ lam rho :=
    hw.toCtx4Z.E8_le_ctxVN (Subgroup.subset_closure (by simp))
  have hlamV : lam ∈ ctxVN t tau x₁ x₂ lam rho :=
    hw.toCtx4Z.E8_le_ctxVN (Subgroup.subset_closure (by simp))
  have htℰ : t ∈ ℰ := hVℰ htV
  have hlamℰ : lam ∈ ℰ := hVℰ hlamV
  have ht2 : t * t = 1 := hw.t_mul_self
  have hlam2 : lam * lam = 1 := hw.lam_mul_self
  have hE0 : t ∉ ctxE0N t tau x₁ x₂ rho ∧ lam ∉ ctxE0N t tau x₁ x₂ rho ∧
      t * lam ∉ ctxE0N t tau x₁ x₂ rho :=
    ⟨hw.t_not_mem_E0, hw.lam_not_mem_E0, hw.tlam_not_mem_E0⟩
  have hcomm : t * lam * t⁻¹ * lam⁻¹ ∈ ctxE0N t tau x₁ x₂ rho := by
    have h1 : t * lam = lam * t := hw.t_lam_comm
    rw [show t * lam * t⁻¹ * lam⁻¹ = 1 by rw [h1]; group]
    exact one_mem _
  obtain ⟨M₁, hM₁le, hM₁idx, htM₁, hinv⟩ :=
    S4B.exists_index_two_of_fusion (ℰ := ℰ) (E₀ := ctxE0N t tau x₁ x₂ rho) hℰ
      (hw.exit_normal hℰ hVℰ) htℰ hlamℰ ht2 hlam2
      (hw.exit_hexp hℰ hVℰ) hE0.1 hE0.2.1 hE0.2.2 hcomm
      (hw.exit_hC hℰ hVℰ) (fun x _ e he => hw.F2 x e he)
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨x₁ ^ 2, lam, fun hcommv => ?_⟩
    have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
      rw [← hcommv]; group
    exact hw.y_ne_x₂_sq (hconj.symm.trans hw.nGood.lam_conj_y)
  haveI : IsSimpleGroup G := hG.simple
  obtain ⟨w, hwM₁, -, -⟩ :=
    Outside.H74_of_simple hnab hℰ hℰidx hM₁le hM₁idx htℰ htM₁ ht2
  have hu2 : (w * t * w⁻¹) * (w * t * w⁻¹) = 1 := by
    rw [show (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ by group, ht2]
    group
  rcases hinv (w * t * w⁻¹) hwM₁ hu2 with huE0 | ⟨e, he, hue⟩
  · exact (hw.toCtx4Z.tG_not_mem_E0 w) huE0
  · exact (hw.F2 w e he) hue

end ZNW4

end

theorem l411_znotsyl_holds : L411ZNotSylStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG _ hz hnot
  exact ((hz.znw hnot).znw4).contradiction hG

end CFSG.OddStandard.SmallF3.HarrisU33
