module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageNextFam
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}
  (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem exists_perm_eq (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) (c : K) :
    ∃ n : normalizer (U : Set G), H.perm n 0 = c := by
  by_cases hc0 : c = 0
  · exact ⟨1, by rw [map_one, Equiv.Perm.one_apply, hc0]⟩
  obtain ⟨g, hgN, hgU, P, hP2, hUP, hgP⟩ :=
    exists_normalizer_not_mem_of_not_isSylow H.stage.isPGroup_U hU
  set c₀ := H.perm ⟨g, hgN⟩ 0 with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    rw [hc₀, H.perm_zero] at h0
    have hV := H.stage.mem_V_of_X_eq_zero H.card_K H.coords H.nu (H.comm_t_mem_V₁ hgN) h0
    exact hgU (H.stage.mem_U_of_comm_t_mem hP2 hUP hgP hV)
  obtain ⟨m, hm⟩ := H.gen (c / c₀) (div_ne_zero hc0 hc₀0)
  set δ : normalizer (U : Set G) := ⟨d⁻¹, inv_mem H.d_mem_normalizer_U⟩ with hδ
  have key : ∀ j : ℕ, H.perm (δ ^ j * ⟨g, hgN⟩) 0 = μ ^ j * c₀ := by
    intro j
    induction j with
    | zero => simp [hc₀]
    | succ j ih =>
      rw [pow_succ', mul_assoc, map_mul, Equiv.Perm.mul_apply, ih, H.perm_d_inv]
      ring
  exact ⟨δ ^ m * ⟨g, hgN⟩, by rw [key, hm, div_mul_cancel₀ c hc₀0]⟩

theorem perm_two_transitive (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∀ a₁ b₁ c₁ e₁ : K, a₁ ≠ b₁ → c₁ ≠ e₁ → ∃ x ∈ H.perm.range, x a₁ = c₁ ∧ x b₁ = e₁ :=
  SzC1.two_transitive_of_transitive H.perm H.gen (δ := ⟨d⁻¹, inv_mem H.d_mem_normalizer_U⟩)
    H.perm_d_inv (H.exists_perm_eq hU)

theorem mem_U₁_mul_centralizer (n : normalizer (U : Set G)) (h0 : H.perm n 0 = 0) :
    ∃ x ∈ U₁, x⁻¹ * (n : G) ∈ centralizer ({t} : Set G) := by
  rw [H.perm_zero] at h0
  have hcV : (n : G) * t * (n : G)⁻¹ * t⁻¹ ∈ V :=
    H.stage.mem_V_of_X_eq_zero H.card_K H.coords H.nu (H.comm_t_mem_V₁ n.2) h0
  obtain ⟨x, hx, hxσ⟩ := H.stage.exists_comm_t_eq H.card_K H.coords H.gen hcV
  refine ⟨x, hx, mem_centralizer_singleton_iff.mpr ?_⟩
  have e : x * t * x⁻¹ = (n : G) * t * (n : G)⁻¹ := by
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
      _ = ((n : G) * t * (n : G)⁻¹ * t⁻¹) * t := by rw [hxσ]
      _ = (n : G) * t * (n : G)⁻¹ := by group
  calc x⁻¹ * (n : G) * t = x⁻¹ * ((n : G) * t * (n : G)⁻¹) * (n : G) := by group
    _ = x⁻¹ * (x * t * x⁻¹) * (n : G) := by rw [e]
    _ = t * (x⁻¹ * (n : G)) := by group

theorem perm_zero_of_mem_centralizer (n : normalizer (U : Set G))
    (hn : (n : G) ∈ centralizer ({t} : Set G)) : H.perm n 0 = 0 := by
  rw [H.perm_zero, mem_centralizer_singleton_iff.mp hn, mul_inv_cancel_right, mul_inv_cancel,
    one_pow, H.coords.v_one]

end U3C1Next

end CFSG.SeitzReduction.RankOne
