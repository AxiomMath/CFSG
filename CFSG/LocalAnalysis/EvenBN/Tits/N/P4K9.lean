module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K8

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section Generic

variable {Γ : Type*} [Group Γ]

theorem isElemAbQuot_of_comm_sq {K W : Subgroup Γ} (hWK : W ≤ K) (hsq : ∀ k ∈ K, k * k ∈ W)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ W) {n : ℕ} (hn : W.relIndex K = 2 ^ n) :
    IsElemAbQuot K W n := by
  refine ⟨hWK, ⟨fun w hw g => ?_⟩, hsq, hcomm, hn⟩
  rw [Subgroup.mem_subgroupOf] at hw ⊢
  have hwK : (w : Γ) ∈ K := hWK hw
  have h1 := hcomm (g : Γ) g.2 w hwK
  have e : ((g * w * g⁻¹ : ↥K) : Γ) = ((g : Γ) * w * (g : Γ)⁻¹ * (w : Γ)⁻¹) * w := by
    show (g : Γ) * w * (g : Γ)⁻¹ = ((g : Γ) * w * (g : Γ)⁻¹ * (w : Γ)⁻¹) * w
    group
  rw [e]
  exact W.mul_mem h1 hw

end Generic

section K9

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem img_Kg_inf_centralizer (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    img d (Kg d ⊓ centralizer ({d.t} : Set G)) = img d (CMt d) := by
  apply le_antisymm
  · intro k hk
    obtain ⟨g, hg, hgN, rfl⟩ := (mem_imgIn_iff d.s56V _).1 hk
    obtain ⟨hgK, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgH : g ∈ Hg d := (mem_Kg_iff.1 hgK).1
    rw [h17.2.2.2.1]
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun h hh => ?_, actFun_mem_imgIn hgH hgN⟩
    rw [Set.mem_singleton_iff.1 hh]
    have hc : d.t * g = g * d.t := mem_centralizer_iff.1 hgC d.t rfl
    exact (actFun_comm_of_comm d.s56V hc.symm).symm
  · apply imgIn_mono
    intro g hg
    refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hg).2⟩
    exact mem_Kg_iff.2 ⟨CMt_le_Hg h49 hd hg,
      C_le_Ks h49 hd hz h10 h17s hy (actFun_mem_imgIn hg (CMt_le_Hg h49 hd hg))⟩

theorem node19_conj2 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    U0s d ≤ W0s d ∧ IsElemAbQuot (W0s d) (U0s d) 4 ∧
      centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ W0s d = U0s d ∧
      (∀ x ∈ DeltaS d, ∃ w ∈ W0s d, w * star d d.t * w⁻¹ = x) ∧
      (W0s d : Set (MulAut ↥d.s56V)) *
        (img d (Kg d ⊓ centralizer ({d.t} : Set G)) : Set (MulAut ↥d.s56V)) =
          (Ks d : Set (MulAut ↥d.s56V)) := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  obtain ⟨hF, hCe, hCbot, hCt⟩ := C_data h49 hd hz h10 h17s hy
  have htU : ∀ u ∈ Us d, star d d.t * u = u * star d d.t := fun u hu =>
    hCt u (IsF20.U_le_Pgrp _ _ _ hu)
  have htnU : star d d.t ∉ Us d := by
    have := h17.2.2.2.2.2 1 (one_mem _)
    simpa using this
  have hU0card : Nat.card ↥(U0s d) = 32 := card_U0 hF (star_t_mul_self h49 hd) htU htnU
  have hDelta : ∀ x ∈ DeltaS d, ∃ w ∈ W0s d, w * star d d.t * w⁻¹ = x := by
    intro x hx
    rw [h18.2.2.2] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact hWtr u hu
  refine ⟨hU0W, ?_, ?_, hDelta, ?_⟩
  · refine isElemAbQuot_of_comm_sq hU0W hWsq hWcomm ?_
    have h := Subgroup.relIndex_mul_card (H := U0s d) (K := W0s d)
    rw [inf_eq_left.2 hU0W, hU0card, hWcard] at h
    omega
  · ext w
    constructor
    · rintro ⟨hwC, hwW⟩
      exact hWreg w hwW (mem_centralizer_iff.1 hwC _ rfl).symm
    · intro hw
      refine ⟨mem_centralizer_iff.2 fun h hh => ?_, hU0W hw⟩
      rw [Set.mem_singleton_iff.1 hh]
      have hle : U0s d ≤ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) := by
        refine sup_le (fun u hu => mem_centralizer_iff.2 fun h' hh' => ?_) (zpowers_le.2 ?_)
        · rw [Set.mem_singleton_iff.1 hh']
          exact htU u hu
        · exact mem_centralizer_iff.2 fun h' hh' => by rw [Set.mem_singleton_iff.1 hh']
      exact mem_centralizer_iff.1 (hle hw) _ rfl
  ·
    have hA := img_Kg_inf_centralizer h49 hd hz h10 h17s h17 hy
    rw [hA]
    ext k
    constructor
    · rintro ⟨w, hw, c, hc, hwc⟩
      have hwc' : w * c = k := hwc
      rw [← hwc']
      exact mul_mem (hWK hw) (C_le_Ks h49 hd hz h10 h17s hy hc)
    · intro hk
      have h1 : star d d.t ∈ DeltaS d := by
        rw [h18.2.2.2]
        exact ⟨1, (Us d).one_mem, mul_one _⟩
      obtain ⟨w, hw, hwk⟩ := hDelta _ (Ks_conj_DeltaS h49 hd hk h1)
      have hc : w⁻¹ * k ∈ img d (CMt d) := by
        rw [h17.2.2.2.1]
        refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun h hh => ?_, ?_⟩
        · rw [Set.mem_singleton_iff.1 hh]
          have e : w⁻¹ * k * star d d.t * (w⁻¹ * k)⁻¹ = star d d.t := by
            calc w⁻¹ * k * star d d.t * (w⁻¹ * k)⁻¹
                = w⁻¹ * (k * star d d.t * k⁻¹) * w := by group
              _ = w⁻¹ * (w * star d d.t * w⁻¹) * w := by rw [hwk]
              _ = star d d.t := by group
          rw [mul_inv_eq_iff_eq_mul] at e
          exact e.symm
        · exact mul_mem (inv_mem ((hWK hw).2)) hk.2
      exact ⟨w, hw, w⁻¹ * k, hc, by group⟩

end K9

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
