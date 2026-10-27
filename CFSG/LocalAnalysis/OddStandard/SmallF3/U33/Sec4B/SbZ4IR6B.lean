module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR6A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutH74
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NL

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


theorem z4i_e4_false (hG : Sec4Glob G) (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
    (hsyl : IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho))
    (hrel : (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 4) : False := by
  obtain ⟨N, hNn, V', hD⟩ := hz.z4iData hsyl hrel
  haveI : N.Normal := hNn
  obtain ⟨P, M, t', hP2, hmax, hQf, hMP, hM2, ht'P, ht'M, ht'sq, ⟨g₀, hg₀⟩, hinv⟩ :=
    hD.exists_syl
  obtain ⟨Sy, hSy⟩ :=
    z4i_isSylow_map (Qg := ctxQ t tau x₁ x₂ rho) (L := ctxNQ t tau x₁ x₂ rho) rfl P hP2
      hmax hQf
  set Pg : Subgroup G := P.map (ctxNQ t tau x₁ x₂ rho).subtype with hPg
  set Mg : Subgroup G := M.map (ctxNQ t tau x₁ x₂ rho).subtype with hMg
  set tg : G := (t' : G) with htg
  have hPg2 : IsPGroup 2 Pg := by rw [hPg]; exact hP2.map _
  have hPgi : ¬ 2 ∣ Pg.index := by simpa [hSy] using Sy.not_dvd_index
  have hMgP : Mg ≤ Pg := by rw [hMg, hPg]; exact Subgroup.map_mono hMP
  have hMg2 : Mg.relIndex Pg = 2 := by
    rw [hMg, hPg,
      Subgroup.relIndex_map_map_of_injective M P (fun a b h => Subtype.ext h), hM2]
  have htgP : tg ∈ Pg := by
    rw [htg, hPg]; exact Subgroup.mem_map_of_mem _ ht'P
  have htgMg : tg ∉ Mg := by
    rw [htg, hMg]
    intro hmem
    obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp hmem
    exact ht'M (Subtype.ext hm ▸ hmM)
  have htg2 : tg * tg = 1 := by
    rw [htg]
    have h := congrArg (fun z : ↥(ctxNQ t tau x₁ x₂ rho) => (z : G)) ht'sq
    simpa using h
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨x₁ ^ 2, lam, fun hcv => ?_⟩
    have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [← hcv]; group
    exact hz.y_ne_x₂_sq (hconj.symm.trans hz.nGood.lam_conj_y)
  haveI : IsSimpleGroup G := hG.simple
  obtain ⟨w, hwM, -, -⟩ :=
    Outside.H74_of_simple hnab hPg2 hPgi hMgP hMg2 htgP htgMg htg2
  rw [hMg] at hwM
  obtain ⟨u, huM, hu_eq⟩ := Subgroup.mem_map.mp hwM
  have htg_eq : tg = (g₀ : G) * t * (g₀ : G)⁻¹ := by
    rw [htg]
    have h := congrArg (fun z : ↥(ctxNQ t tau x₁ x₂ rho) => (z : G)) hg₀
    simpa [Ctx4Z.z4iT] using h
  set c : G := w * (g₀ : G) with hc
  have hu_c : (u : G) = c * t * c⁻¹ := by
    have h1 : (u : G) = w * tg * w⁻¹ := hu_eq
    rw [h1, htg_eq, hc]; group
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    change (u : G) * (u : G) = 1
    rw [hu_c]
    rw [show (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, hz.t_mul_self]
    group
  rcases hinv u huM hu2 with hcent | ⟨g, hg⟩ | ⟨g, hg⟩
  · refine hz.z4i_tG_not_cent_Y c (fun y hy => ?_)
    have hyL : y ∈ ctxNQ t tau x₁ x₂ rho := hz.z4i_Q_le_NQ (hz.Y_le_Q hy)
    have hmem : (⟨y, hyL⟩ : ↥(ctxNQ t tau x₁ x₂ rho)) ∈
        hz.z4iSub (ctxYq t tau x₁ x₂ rho) :=
      (hz.z4i_mem_sub (ctxYq t tau x₁ x₂ rho) ⟨y, hyL⟩).mpr hy
    have h' : (u : G) * y = y * (u : G) := by
      have h := congrArg (fun z : ↥(ctxNQ t tau x₁ x₂ rho) => (z : G))
        (hcent ⟨y, hyL⟩ hmem)
      simpa using h
    rw [hu_c] at h'
    exact h'.symm
  · have hconj : ((g : G)⁻¹ * c) * t * ((g : G)⁻¹ * c)⁻¹ = lam := by
      have hg' : (u : G) = (g : G) * lam * (g : G)⁻¹ := by
        have h := congrArg (fun z : ↥(ctxNQ t tau x₁ x₂ rho) => (z : G)) hg
        simpa [Ctx4Z.z4iLam] using h
      rw [hu_c] at hg'
      calc ((g : G)⁻¹ * c) * t * ((g : G)⁻¹ * c)⁻¹
          = (g : G)⁻¹ * (c * t * c⁻¹) * (g : G) := by group
        _ = (g : G)⁻¹ * ((g : G) * lam * (g : G)⁻¹) * (g : G) := by rw [hg']
        _ = lam := by group
    exact hz.not_conj_t_lam ((g : G)⁻¹ * c) hconj
  · have hconj : ((g : G)⁻¹ * c) * t * ((g : G)⁻¹ * c)⁻¹ = lam * tau := by
      have hg' : (u : G) = (g : G) * (lam * tau) * (g : G)⁻¹ := by
        have h := congrArg (fun z : ↥(ctxNQ t tau x₁ x₂ rho) => (z : G)) hg
        simpa [Ctx4Z.z4iTau, Ctx4Z.z4iLam, hz.tau_lam] using h
      rw [hu_c] at hg'
      calc ((g : G)⁻¹ * c) * t * ((g : G)⁻¹ * c)⁻¹
          = (g : G)⁻¹ * (c * t * c⁻¹) * (g : G) := by group
        _ = (g : G)⁻¹ * ((g : G) * (lam * tau) * (g : G)⁻¹) * (g : G) := by rw [hg']
        _ = lam * tau := by group
    exact hz.not_conj_t_lamtau ((g : G)⁻¹ * c) hconj

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
