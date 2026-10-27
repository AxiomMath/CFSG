module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_centralizer_of_le_normalizer {A B K : Subgroup G}
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hAK : A ≤ Subgroup.centralizer (K : Set G)) :
    ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  have hcomm : ⁅B, A⁆ ≤ Subgroup.centralizer (K : Set G) := by
    have hKA : ⁅K, A⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hAK)
    have hKBA : ⁅K, B⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hBK
    have h1 : ⁅⁅A, K⁆, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm A K, hKA, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅K, B⁆, A⁆ = ⊥ :=
      le_bot_iff.mp (hKA ▸ Subgroup.commutator_mono hKBA le_rfl)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
  intro b hb a ha
  have h1 : ⁅b, a⁆ ∈ Subgroup.centralizer (K : Set G) :=
    hcomm (Subgroup.commutator_mem_commutator hb ha)
  have h2 : a ∈ Subgroup.centralizer (K : Set G) := hAK ha
  have e : b * a * b⁻¹ = ⁅b, a⁆ * a := by rw [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.centralizer (K : Set G)).mul_mem h1 h2

theorem commutator_commutator_le_of_rotate_normal {M A B N : Subgroup G}
    (hAM : A ≤ M) (hBM : B ≤ M) (hNM : N ≤ M)
    (hNMnorm : M ≤ Subgroup.normalizer (N : Set G))
    (h1 : ⁅⁅A, B⁆, A⁆ ≤ N) (h2 : ⁅⁅B, A⁆, A⁆ ≤ N) :
    ⁅⁅A, A⁆, B⁆ ≤ N := by
  let Am : Subgroup M := A.subgroupOf M
  let Bm : Subgroup M := B.subgroupOf M
  let Nm : Subgroup M := N.subgroupOf M
  have hNm : Nm.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNMnorm
  have h1m : ⁅⁅Am, Bm⁆, Am⁆ ≤ Nm := by
    rw [← Subgroup.map_le_map_iff_of_injective M.subtype_injective,
      Subgroup.map_commutator, Subgroup.map_commutator]
    simpa only [Am, Bm, Nm, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAM,
      inf_eq_left.2 hBM, inf_eq_left.2 hNM] using h1
  have h2m : ⁅⁅Bm, Am⁆, Am⁆ ≤ Nm := by
    rw [← Subgroup.map_le_map_iff_of_injective M.subtype_injective,
      Subgroup.map_commutator, Subgroup.map_commutator]
    simpa only [Am, Bm, Nm, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAM,
      inf_eq_left.2 hBM, inf_eq_left.2 hNM] using h2
  let π : ↥M →* ↥M ⧸ Nm := QuotientGroup.mk' Nm
  have h1q : ⁅⁅Am.map π, Bm.map π⁆, Am.map π⁆ = ⊥ := by
    have h : (⁅⁅Am, Bm⁆, Am⁆).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact h1m
    simpa [Subgroup.map_commutator] using h
  have h2q : ⁅⁅Bm.map π, Am.map π⁆, Am.map π⁆ = ⊥ := by
    have h : (⁅⁅Bm, Am⁆, Am⁆).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact h2m
    simpa [Subgroup.map_commutator] using h
  have h3q : ⁅⁅Am.map π, Am.map π⁆, Bm.map π⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1q h2q
  have h3m : ⁅⁅Am, Am⁆, Bm⁆ ≤ Nm := by
    have hmap : (⁅⁅Am, Am⁆, Bm⁆).map π = ⊥ := by
      simpa [Subgroup.map_commutator] using h3q
    have h := (Subgroup.map_eq_bot_iff (⁅⁅Am, Am⁆, Bm⁆) (f := π)).mp hmap
    rwa [QuotientGroup.ker_mk'] at h
  have h3 := Subgroup.map_mono (f := M.subtype) h3m
  rw [Subgroup.map_commutator, Subgroup.map_commutator] at h3
  simpa only [Am, Bm, Nm, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAM,
    inf_eq_left.2 hBM, inf_eq_left.2 hNM] using h3

theorem commutator_eq_bot_of_commutator_le_of_centralizer {A V V₀ : Subgroup G}
    (hAV : ⁅A, V⁆ ≤ V₀) (hA₀ : A ≤ Subgroup.centralizer (V₀ : Set G))
    (hA : ⁅A, A⁆ = A) : ⁅A, V⁆ = ⊥ := by
  have h1 : ⁅⁅A, V⁆, A⁆ = ⊥ := by
    refine le_bot_iff.1 ((Subgroup.commutator_mono hAV le_rfl).trans ?_)
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hA₀).le
  have h2 : ⁅⁅V, A⁆, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm V A]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := V) h1 h2
  rwa [hA] at h3

end CFSG.GroupTheory
