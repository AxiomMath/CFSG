module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem charIn_of_map {𝒬 A : Subgroup G} {A₀ : Subgroup ↥𝒬} (hA : A ≤ 𝒬)
    (hmap : A₀.map 𝒬.subtype = A) (hchar : A₀.Characteristic) : CharIn A 𝒬 := by
  unfold CharIn
  refine ⟨hA, ?_⟩
  have h : A.subgroupOf 𝒬 = A₀ := by
    rw [Subgroup.subgroupOf, ← hmap]
    exact Subgroup.comap_map_eq_self_of_injective 𝒬.subtype_injective A₀
  rwa [h]

theorem lemma4_16_proof (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Lemma4_16Concl t tau x₁ x₂ rho om := by
  let 𝒬 : Subgroup G := ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)
  let Q0 : Subgroup ↥𝒬 := (ctxQ t tau x₁ x₂ rho).subgroupOf 𝒬
  let Y0 : Subgroup ↥𝒬 := (ctxYq t tau x₁ x₂ rho).subgroupOf 𝒬
  let τ0 : ↥𝒬 := ⟨tau, Ctx13.tau_mem_QQ hc⟩
  let ω0 : ↥𝒬 := ⟨om, Ctx13.om_mem_QQ hc⟩
  have hs : Setting16 Q0 Y0 τ0 ω0 := setting16_of_ctx13 hc
  have hQle : ctxQ t tau x₁ x₂ rho ≤ 𝒬 := le_sup_left
  have hYle : ctxYq t tau x₁ x₂ rho ≤ 𝒬 := ctxYq_le_ctxQ.trans le_sup_left
  have hQ0map : Q0.map 𝒬.subtype = ctxQ t tau x₁ x₂ rho :=
    Subgroup.map_subgroupOf_eq_of_le hQle
  have hY0map : Y0.map 𝒬.subtype = ctxYq t tau x₁ x₂ rho :=
    Subgroup.map_subgroupOf_eq_of_le hYle
  have hτ : 𝒬.subtype τ0 = tau := rfl
  have hω : 𝒬.subtype ω0 = om := rfl
  have himg : 𝒬.subtype '' ({τ0, ω0} : Set ↥𝒬) = ({tau, om} : Set G) := by
    rw [Set.image_pair, hτ, hω]
  have hQ0τmap : (Q0 ⊔ zpowers τ0).map 𝒬.subtype = ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    rw [Subgroup.map_sup, hQ0map, MonoidHom.map_zpowers, hτ]
  have hE6map : (closure ({τ0, ω0} : Set ↥𝒬) ⊔ Y0).map 𝒬.subtype =
      closure ({tau, om} : Set G) ⊔ ctxYq t tau x₁ x₂ rho := by
    rw [Subgroup.map_sup, MonoidHom.map_closure, himg, hY0map]
  have hτYmap : (zpowers τ0 ⊔ Y0).map 𝒬.subtype = zpowers tau ⊔ ctxYq t tau x₁ x₂ rho := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hτ, hY0map]
  unfold Lemma4_16Concl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact charIn_of_map hYle hY0map hs.char_Y
  · exact charIn_of_map hQle hQ0map hs.char_Q
  · refine charIn_of_map (A₀ := Q0 ⊔ zpowers τ0) ?_ hQ0τmap hs.char_Qtau
    exact sup_le hQle (Subgroup.zpowers_le.mpr (Ctx13.tau_mem_QQ hc))
  · refine charIn_of_map (A₀ := closure ({τ0, ω0} : Set ↥𝒬) ⊔ Y0) ?_ hE6map hs.char_E6
    refine sup_le ?_ hYle
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ctx13.tau_mem_QQ hc
    · exact Ctx13.om_mem_QQ hc
  · refine charIn_of_map (A₀ := zpowers τ0 ⊔ Y0) ?_ hτYmap hs.char_tauY
    exact sup_le (Subgroup.zpowers_le.mpr (Ctx13.tau_mem_QQ hc)) hYle

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
