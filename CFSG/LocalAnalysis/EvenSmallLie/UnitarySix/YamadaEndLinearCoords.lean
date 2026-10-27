module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndLinear
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem sY_mem_msigma (F : Type) [Field F] [Finite F] [CharP F 2] :
    sY F 0 * sY F 2 ∈ msigma F ∧ sY F 1 ∈ msigma F := by
  refine ⟨?_, ?_⟩
  · change sigmaSL F (sY F 0 * sY F 2) = sY F 0 * sY F 2
    rw [map_mul, sigmaSL_sY_zero, sigmaSL_sY_two]
    exact (blockSL2_comm 3 0 2 (by decide) _ _).symm
  · exact sigmaSL_sY_one F

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {d : YamadaData G}

namespace YamadaSection4

variable (h : YamadaSection4 F d)
include h

theorem L₁_linear (hL : ∃ _ : (d.D₁.subgroupOf d.N₁).Normal,
    ∃ ψ : SL(4, F) →* d.N₁ ⧸ d.D₁.subgroupOf d.N₁,
      Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) :
    ∃ ψ : SL(4, F) →* d.L₁, Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F) := by
  obtain ⟨hn, ψ, hψ, hker⟩ := hL
  obtain ⟨e⟩ := nonempty_quotientEquiv (L := d.L₁) h.D₁_le h.N₁_eq.le h.L₁_facts.2
    (inf_le_left.trans h.N₁_norm)
  let e' : d.L₁ ≃* d.N₁ ⧸ d.D₁.subgroupOf d.N₁ :=
    (MulEquiv.subgroupCongr (inf_of_le_left (inf_le_left : d.L₁ ≤ d.N₁))).symm.trans e
  refine ⟨e'.symm.toMonoidHom.comp ψ, e'.symm.surjective.comp hψ, fun x hx => hker ?_⟩
  have h1 : e'.symm (ψ x) = 1 := hx
  exact (MulEquiv.map_eq_one_iff e'.symm).mp h1

theorem exists_coords (hL44 : L44Input) (hL : ∃ _ : (d.D₁.subgroupOf d.N₁).Normal,
    ∃ ψ : SL(4, F) →* d.N₁ ⧸ d.D₁.subgroupOf d.N₁,
      Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) :
    ∃ φ : SL(4, F) →* G, Function.Injective φ ∧ φ.range = d.L₁ ∧
      φ (sY F 0 * sY F 2) = d.w₂ ∧ φ (sY F 1) = d.w₃ ∧
      (∀ A, d.t * φ A * d.t⁻¹ = φ (sigmaSL F A)) ∧ (pstd F).map φ = d.P₁ := by
  obtain ⟨ψ, hψ, hker⟩ := h.L₁_linear hL
  obtain ⟨χ, hχ₂, hχ₃, hχS⟩ := h.K₁_model
  let χ' : msigma F ≃* (d.L₁ ⊓ centralizer ({d.t} : Set G) : Subgroup G) :=
    χ.trans (MulEquiv.subgroupCongr h.L₁_facts.1.symm)
  have hS : ∀ A : msigma F, (A : SL(4, F)) ∈ pstd F → (χ' A : G) ∈ d.P₁ := fun A hA =>
    (h.P₁_inf_H ▸ hχS A hA : (χ A : G) ∈ d.P₁ ⊓ d.H).1
  obtain ⟨φ, hφ, hφL, hφχ, hφσ, hφP⟩ := hL44 F h.card_field G d.L₁ ψ hψ hker d.t h.t_sq h.t_L₁
    χ' d.P₁ h.P₁_facts.2.2 hS
  obtain ⟨hu, hv⟩ := sY_mem_msigma F
  refine ⟨φ, hφ, hφL, ?_, ?_, hφσ, hφP⟩
  · exact (hφχ ⟨_, hu⟩).trans (hχ₂ ⟨_, hu⟩ rfl)
  · exact (hφχ ⟨_, hv⟩).trans (hχ₃ ⟨_, hv⟩ rfl)

theorem coords_facts {φ : SL(4, F) →* G} (hφ : Function.Injective φ)
    (hw₂ : φ (sY F 0 * sY F 2) = d.w₂) (hw₃ : φ (sY F 1) = d.w₃)
    (hσ : ∀ A, d.t * φ A * d.t⁻¹ = φ (sigmaSL F A)) (hP : (pstd F).map φ = d.P₁) :
    d.Yb = (blockSL2 F 3 0).range.map φ ⊔ (blockSL2 F 3 2).range.map φ ∧
      d.Yc = (blockSL2 F 3 1).range.map φ ∧
      conjR ((blockSL2 F 3 0).range.map φ) d.t = (blockSL2 F 3 2).range.map φ := by
  have hmapP : ∀ g : SL(4, F),
      (pstd F ⊓ conjR (pstd F) g).map φ = d.P₁ ⊓ conjR d.P₁ (φ g) := fun g => by
    rw [Subgroup.map_inf_eq _ _ φ hφ, map_conjR, hP]
  have hb0 : rootSL F 1 0 ⊔ rootSL F 0 1 = (blockSL2 F 3 0).range :=
    rootSL_sup_rootSL_eq_range F 0
  have hb1 : rootSL F 2 1 ⊔ rootSL F 1 2 = (blockSL2 F 3 1).range :=
    rootSL_sup_rootSL_eq_range F 1
  have hb2 : rootSL F 3 2 ⊔ rootSL F 2 3 = (blockSL2 F 3 2).range :=
    rootSL_sup_rootSL_eq_range F 2
  refine ⟨?_, ?_, ?_⟩
  · have hUb : d.Ub = (rootSL F 1 0 ⊔ rootSL F 3 2).map φ := by
      rw [← h.P₁_cbc, ← pstd_inf_conjR_b, hmapP, map_mul, map_mul, hw₂, hw₃]
    have hYb : d.Yb = d.Ub ⊔ conjR d.Ub d.w₂ := rfl
    rw [hYb, hUb, ← hw₂, ← map_conjR, ← Subgroup.map_sup, conjR_sup, conjR_rootSL_one_zero,
      conjR_rootSL_three_two, sup_sup_sup_comm, hb0, hb2, Subgroup.map_sup]
  · have hUc : d.Uc = (rootSL F 2 1).map φ := by
      rw [← pstd_inf_conjR_c, hmapP, map_mul, map_mul, hw₂, hw₃]
      rfl
    have hYc : d.Yc = d.Uc ⊔ conjR d.Uc d.w₃ := rfl
    rw [hYc, hUc, ← hw₃, ← map_conjR, ← Subgroup.map_sup, conjR_rootSL_two_one, hb1]
  · rw [conjR, h.t_inv, Subgroup.map_map, ← map_sigmaSL_range_zero, Subgroup.map_map]
    congr 1
    ext A
    exact hσ A

theorem linearCase
    (hL44 : L44Input) (hL : ∃ _ : (d.D₁.subgroupOf d.N₁).Normal,
    ∃ ψ : SL(4, F) →* d.N₁ ⧸ d.D₁.subgroupOf d.N₁,
      Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) : LinearCase F d.G₀ := by
  obtain ⟨φ, hφ, hφL, hw₂, hw₃, hσ, hP⟩ := h.exists_coords hL44 hL
  obtain ⟨hYb, hYc, hswap⟩ := h.coords_facts hφ hw₂ hw₃ hσ hP
  exact h.linearCase_of_coords φ hφ hφL hYb hYc hswap

end YamadaSection4

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
