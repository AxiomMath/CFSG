module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbX17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Quo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutH74

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_false (hG : Sec4Glob G) (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) : False := by
  have h𝒮 : IsPGroup 2 𝒮 := hc.sylow.2.1
  obtain ⟨ℰ, hℰsyl, h𝒮ℰ⟩ := exists_isSylowIn_of_le (K := ⊤) (U := 𝒮) le_top h𝒮
  have hℰ : IsPGroup 2 ℰ := hℰsyl.2.1
  have hℰidx : ¬ 2 ∣ ℰ.index := by
    simpa only [Subgroup.relIndex_top_right] using hℰsyl.2.2
  have hT := l17_T_le_sylow hc
  have htℰ : t ∈ ℰ := h𝒮ℰ hT.1
  have hlamℰ : lam ∈ ℰ := h𝒮ℰ hT.2.2.2
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have hlam2 : lam * lam = 1 := by
    have h := (ctx13_lam_facts hc.toCtx13).1
    simpa [pow_two] using h
  have hE0 := l17_not_mem_E0 hc.toCtx13
  have hcomm : t * lam * t⁻¹ * lam⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om := by
    have h1 : t * lam = lam * t := (l17_lam_comm hc.toCtx13).1.symm
    rw [show t * lam * t⁻¹ * lam⁻¹ = 1 by rw [h1]; group]
    exact one_mem _
  obtain ⟨M₁, hM₁le, hM₁idx, htM₁, hinv⟩ :=
    exists_index_two_of_fusion (ℰ := ℰ) (E₀ := ctxE0 t tau x₁ x₂ rho om) hℰ
      (l17_exit_normal hc hℰ h𝒮ℰ) htℰ hlamℰ ht2 hlam2
      (l17_exit_hexp hc hℰ h𝒮ℰ) hE0.1 hE0.2.1 hE0.2.2 hcomm
      (l17_exit_hC hc hℰ h𝒮ℰ) (fun x _ e he => l17_F2 hc x he)
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨x₁ ^ 2, lam, fun hcommv => ?_⟩
    have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
      rw [← hcommv]; group
    have hly := l17_lam_y hc.toCtx13
    have h2 : x₁ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hconj.symm.trans hly
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      calc (x₁ * x₂) ^ 2 = (x₁ ^ 2)⁻¹ * (x₁ ^ 2 * (x₁ * x₂) ^ 2) := by group
        _ = (x₁ ^ 2)⁻¹ * x₁ ^ 2 := by rw [← h2]
        _ = 1 := by group
    exact (l17_yz_ne hc.toCtx13).2.1 hz1
  haveI : IsSimpleGroup G := hG.simple
  obtain ⟨w, hwM₁, -, -⟩ :=
    Outside.H74_of_simple hnab hℰ hℰidx hM₁le hM₁idx htℰ htM₁ ht2
  have hu2 : (w * t * w⁻¹) * (w * t * w⁻¹) = 1 := by
    rw [show (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ by group, ht2]
    group
  rcases hinv (w * t * w⁻¹) hwM₁ hu2 with huE0 | ⟨e, he, hue⟩
  · exact (l17_F1 hc.toCtx13 w) huE0
  · exact (l17_F2 hc w he) hue

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem lemma4_17 : Lemma4_17Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om hG hc 𝒮 h𝒮 hU hK
  exact (S4B.l17_false hG ⟨hc, h𝒮, hU, hK⟩).elim

end CFSG.OddStandard.SmallF3.HarrisU33
