module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5k
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem case_non (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω)
    (hΩ : ∀ b ∈ B, b * b = 1 → b ∈ fourGrp x₁ x₂) :
    NormalIn (ctxN ω x₁ x₂) (ctxLO t tau x₁ x₂) := by
  have hc := ha.toCtx4L.toCtx4Q
  have hP : ∀ p ∈ ctxPL t tau x₁ x₂, ∀ q ∈ B, p * q * p⁻¹ ∈ B := by
    intro p hp q hq
    have hpc := hB.P_comm q hq p hp
    have h : p * q * p⁻¹ = (q * p * q⁻¹ * p⁻¹)⁻¹ * q := by group
    rw [h]
    exact B.mul_mem (B.inv_mem (hB.V_le hpc)) hq
  have hLB : ∀ g ∈ ctxLO t tau x₁ x₂, ∀ q ∈ B, g * q * g⁻¹ ∈ B := by
    rw [ha.L_eq]
    exact normalizes_of_sup B (ctxPL t tau x₁ x₂) rho (lam * t) hP hB.rho_mem hB.sig_mem
  have hNle : ctxN ω x₁ x₂ ≤ ctxLO t tau x₁ x₂ := by
    rw [ctxN, closure_le]
    intro a ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
    rcases ha' with rfl | rfl | rfl
    · exact Subgroup.le_normalizer (T_le_O hc hB.ω_mem)
    · exact Subgroup.le_normalizer (V_le_O hc (Subgroup.subset_closure (by simp)))
    · exact Subgroup.le_normalizer (V_le_O hc (Subgroup.subset_closure (by simp)))
  have hVleN : fourGrp x₁ x₂ ≤ ctxN ω x₁ x₂ := by
    rw [fourGrp, ctxN]
    exact Subgroup.closure_mono (by intro a ha; simp at ha ⊢; tauto)
  have hωN : ω ∈ ctxN ω x₁ x₂ := Subgroup.subset_closure (by simp)
  refine ⟨hNle, fun g hg k hk => ?_⟩
  refine conj_mem_closure (S := ({ω, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G)) (g := g) ?_ k hk
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs | hs
  ·
    rw [hs]
    have huO : g * ω * g⁻¹ ∈ ctxO t tau x₁ x₂ :=
      (Subgroup.mem_normalizer_iff.mp hg ω).mp (T_le_O hc hB.ω_mem)
    have hω2 : ω * ω = 1 := T_sq hc ω hB.ω_mem
    have hu2 : (g * ω * g⁻¹) * (g * ω * g⁻¹) = 1 := by
      rw [show (g * ω * g⁻¹) * (g * ω * g⁻¹) = g * (ω * ω) * g⁻¹ by group, hω2]
      group
    have huc : ∀ b ∈ B, (g * ω * g⁻¹) * b = b * (g * ω * g⁻¹) := by
      intro b hb
      have hb' : g⁻¹ * b * g ∈ B := by
        have h := hLB g⁻¹ (inv_mem hg) b hb
        simpa [inv_inv] using h
      have hcomm : ω * (g⁻¹ * b * g) = (g⁻¹ * b * g) * ω := hB.ω_comm _ hb'
      calc (g * ω * g⁻¹) * b
          = g * (ω * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * ω) * g⁻¹ := by rw [hcomm]
        _ = b * (g * ω * g⁻¹) := by group
    obtain ⟨b₀, hb₀, h | h⟩ := cent_decomp ha hB (g * ω * g⁻¹) huO huc
    · have hb₀2 : b₀ * b₀ = 1 := by rw [← h]; exact hu2
      have hb₀V : b₀ ∈ fourGrp x₁ x₂ := hΩ b₀ hb₀ hb₀2
      rw [h]
      exact hVleN hb₀V
    · have hb₀2 : b₀ * b₀ = 1 := by
        have huu : (b₀ * ω) * (b₀ * ω) = 1 := by rw [← h]; exact hu2
        have h1 : (b₀ * ω) * (b₀ * ω) = (b₀ * b₀) * (ω * ω) := by
          rw [show (b₀ * ω) * (b₀ * ω) = b₀ * (ω * b₀) * ω by group,
            hB.ω_comm b₀ hb₀]
          group
        rw [h1, hω2, mul_one] at huu
        exact huu
      have hb₀V : b₀ ∈ fourGrp x₁ x₂ := hΩ b₀ hb₀ hb₀2
      rw [h]
      exact mul_mem (hVleN hb₀V) hωN
  · rw [hs]
    exact hVleN (LO_conj_V ha g hg (x₁ ^ 2) (Subgroup.subset_closure (by simp)))
  · rw [hs]
    exact hVleN (LO_conj_V ha g hg ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp)))

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
