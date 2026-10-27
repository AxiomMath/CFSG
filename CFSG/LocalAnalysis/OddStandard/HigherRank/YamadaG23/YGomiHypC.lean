module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiHypA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Gomi6Data

variable {A V C₀ C₁ : Subgroup G} {t u : G} (h : Gomi6Data A V C₀ C₁ t u)

include h

theorem hyp_sylow :
    IsSylowIn 2 (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V) (A ⊔ V) := by
  have hP_cent : A ⊔ V ≤ centralizer (V : Set G) := h.AV_le_cent
  have hP_K : A ⊔ V ≤ centralizerSection (A ⊔ V) V := by
    intro x hx
    exact ⟨Subgroup.le_normalizer hx,
      Subgroup.centralizer_le_normalizer (V : Set G) (hP_cent hx),
      fun k hk => h.hyp_comm k hk x hx⟩
  have hPGK : A ⊔ V ≤ centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V :=
    le_inf hP_cent hP_K
  have hV_C1 : V ≤ C₁ := h.V_le_C0.trans (h.C1_eq ▸ le_sup_right)
  have hP_C1 : A ⊔ V ≤ C₁ := sup_le h.A_le_C1 hV_C1
  refine ⟨hPGK, h.four2a.2.1.to_le hP_C1, ?_⟩
  have hGK : centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V ≤
      centralizerSection (A ⊔ V) V := inf_le_right
  have hC1K : C₁ ≤ centralizerSection (A ⊔ V) V := h.four2a.1
  have hcent : (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V).relIndex
      (centralizerSection (A ⊔ V) V) = 2 :=
    h.relIndex_cent h.K_le_normalizer_V h.t_mem_K
  have h1 : (A ⊔ V).relIndex (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V) * 2 =
      (A ⊔ V).relIndex (centralizerSection (A ⊔ V) V) := by
    rw [← Subgroup.relIndex_mul_relIndex (A ⊔ V)
      (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V)
      (centralizerSection (A ⊔ V) V) hPGK hGK, hcent]
  have h2 : 2 * C₁.relIndex (centralizerSection (A ⊔ V) V) =
      (A ⊔ V).relIndex (centralizerSection (A ⊔ V) V) := by
    rw [← Subgroup.relIndex_mul_relIndex (A ⊔ V) C₁
      (centralizerSection (A ⊔ V) V) hP_C1 hC1K, h.AV_relIndex_C1]
  have heq : (A ⊔ V).relIndex (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V) * 2 =
      C₁.relIndex (centralizerSection (A ⊔ V) V) * 2 := by
    rw [h1, mul_comm (C₁.relIndex (centralizerSection (A ⊔ V) V)), ← h2]
  have hxy : (A ⊔ V).relIndex (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V) =
      C₁.relIndex (centralizerSection (A ⊔ V) V) :=
    Nat.mul_right_cancel (by norm_num) heq
  rw [hxy]
  exact h.four2a.2.2

theorem hyp_seven :
    ∀ n ∈ normIn (centralizer (V : Set G)) (A ⊔ V),
      ∃ m ∈ normIn (centralizer (V : Set G)) (A ⊔ V),
        ∃ c ∈ centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V,
          n = m * c ∧ ⁅m, t⁆ ∈ A ⊔ V := by
  intro n hn
  obtain ⟨hnG, hnP⟩ := Subgroup.mem_inf.mp hn
  have hnPK : n ∈ normalizer (C₁ : Set G) ⊔ centralizerSection (A ⊔ V) V := by
    rw [← h.four2b]
    exact hnP
  obtain ⟨y, hy, k, hk, hnk⟩ :=
    h.mem_sup_K (X := normalizer (C₁ : Set G)) h.N_C1_le hnPK
  have hyP : y ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) := h.N_C1_le hy
  have hyV : y ∈ normalizer (V : Set G) := h.N_AV_le hyP
  rcases h.mem_cent_or_mul_t hyV with hyC | hytC
  · refine ⟨y, Subgroup.mem_inf.mpr ⟨hyC, hyP⟩, k, Subgroup.mem_inf.mpr ⟨?_, hk⟩, hnk,
      h.comm_t_mem hy⟩
    have hk_eq : k = y⁻¹ * n := by rw [hnk]; group
    rw [hk_eq]
    exact (centralizer (V : Set G)).mul_mem ((centralizer (V : Set G)).inv_mem hyC) hnG
  · have hmC1 : y * t ∈ normalizer (C₁ : Set G) :=
      (normalizer (C₁ : Set G)).mul_mem hy h.t_mem_normalizer_C1
    have hmP : y * t ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) := h.N_C1_le hmC1
    have hcK : t⁻¹ * k ∈ centralizerSection (A ⊔ V) V :=
      (centralizerSection (A ⊔ V) V).mul_mem
        ((centralizerSection (A ⊔ V) V).inv_mem h.t_mem_K) hk
    have hcG : t⁻¹ * k ∈ centralizer (V : Set G) := by
      have hc_eq : t⁻¹ * k = (y * t)⁻¹ * n := by rw [hnk]; group
      rw [hc_eq]
      exact (centralizer (V : Set G)).mul_mem
        ((centralizer (V : Set G)).inv_mem hytC) hnG
    refine ⟨y * t, Subgroup.mem_inf.mpr ⟨hytC, hmP⟩, t⁻¹ * k,
      Subgroup.mem_inf.mpr ⟨hcG, hcK⟩, ?_, h.comm_t_mem hmC1⟩
    rw [hnk]; group

end Gomi6Data

end CFSG.OddStandard.HigherRank.YamadaG23
