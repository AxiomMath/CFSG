module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionGraphAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionGraphFive

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def IsTransvectionOrJ2 (y : projectiveSL n K) : Prop :=
  IsInvolutionClass 1 y ∨ IsInvolutionClass 2 y

theorem IsTransvectionOrJ2.conjAut {y : projectiveSL n K} (h : IsTransvectionOrJ2 y)
    (A : GL (Fin n) K) : IsTransvectionOrJ2 (LinearFlag.conjAut n K A y) :=
  h.imp (fun h1 => h1.conjAut A) (fun h2 => h2.conjAut A)

theorem perfectTwistedFusionIn_conjAut_mul_dualAut_of_not_alt_of_dualAut {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) {Q : projectiveSL n K → Prop}
    (hQ : ∀ (A : GL (Fin n) K) y, Q y → Q (LinearFlag.conjAut n K A y))
    (hδ : PerfectTwistedFusionIn (dualAut n K) Q) (A : GL (Fin n) K)
    (hα : (LinearFlag.conjAut n K A * dualAut n K) ^ 2 = 1)
    (halt : ¬∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0) :
    PerfectTwistedFusionIn (LinearFlag.conjAut n K A * dualAut n K) Q := by
  obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα
  rcases hC with ⟨hC1, -⟩ | ⟨r, -, -, halt'⟩
  · have hC1' : C = 1 := Units.ext hC1
    refine PerfectTwistedFusionIn.of_conj (ψ := (LinearFlag.conjAut n K H)⁻¹)
      (β := dualAut n K) ?_ (fun x hx => ?_) hδ
    · rw [hH, hC1', map_one, one_mul]
      group
    · rw [inv_inv]
      exact hQ H x hx
  · exact absurd halt' halt

theorem perfectTwistedFusionIn_of_not_mem_range_conj_of_dualAut {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (hnf : ¬(n = 4 ∧ f = 1))
    (hδ : PerfectTwistedFusionIn (dualAut n K) IsTransvectionOrJ2)
    {x : MulAut (projectiveSL n K)}
    (hxX : x ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (hx2 : x ^ 2 = 1) : PerfectTwistedFusionIn x IsTransvectionOrJ2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := n) (by omega)).2 x
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at hxX hx2 ⊢
    by_cases hσ : σ = 1
    · exfalso
      subst hσ
      rw [map_one, mul_one] at hxX hx2
      by_cases h1 : LinearFlag.conjAut n K A = 1
      · exact hxX (h1 ▸ one_mem _)
      · obtain ⟨s, -, hs⟩ :=
          CFSG.ComponentClassification.OutcomeLocal.exists_involution_eq_conjAut (by omega) A
            hx2 h1
        exact hxX ⟨s, hs.symm⟩
    · exact (perfectTwistedFusionIn_conjAut_mul_fieldAut hf hK (by omega) A σ hσ hx2).mono
        fun y hy => Or.inl hy
  · rw [pow_one] at hxX hx2 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hx2 ⊢
      by_cases halt : ∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0
      · exact (perfectTwistedFusionIn_conjAut_mul_dualAut_of_alt hf hK (by omega) hnf A hx2
          halt).mono fun y hy => Or.inr hy
      · exact perfectTwistedFusionIn_conjAut_mul_dualAut_of_not_alt_of_dualAut hf hK (by omega)
          (fun B y hy => hy.conjAut B) hδ A hx2 halt
    · exact (perfectTwistedFusionIn_conjAut_mul_fieldAut_mul_dualAut hf hK (by omega)
        (by omega) A σ hσ hx2).mono fun y hy => Or.inl hy

theorem perfectTwistedFusionIn_dualAut_of_ne {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (hnf : (n, f) ≠ (4, 1)) :
    PerfectTwistedFusionIn (dualAut n K) IsTransvectionOrJ2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  by_cases hf2 : 2 ≤ f
  · have hK4 : ∃ s : Finset K, s.card = 4 := by
      have := Fintype.ofFinite K
      have h4 : 4 ≤ (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
      exact ⟨s, hs⟩
    exact (perfectTwistedFusionIn_dualAut hK4 (by omega)).mono fun y hy => Or.inl hy
  · have h5 : 5 ≤ n := by
      by_contra h
      exact hnf (by rw [show n = 4 by omega, show f = 1 by omega])
    exact (perfectTwistedFusionIn_dualAut_of_five_le h5).mono fun y hy => Or.inr hy

theorem perfectTwistedFusionIn_of_not_mem_range_conj {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (hnf : (n, f) ≠ (4, 1))
    {x : MulAut (projectiveSL n K)}
    (hxX : x ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (hx2 : x ^ 2 = 1) : PerfectTwistedFusionIn x IsTransvectionOrJ2 :=
  perfectTwistedFusionIn_of_not_mem_range_conj_of_dualAut hf hK hn
    (fun h => hnf (by rw [h.1, h.2])) (perfectTwistedFusionIn_dualAut_of_ne hf hK hn hnf) hxX hx2

theorem forall_perfectTwistedFusion_of_mulEquiv_projectiveSL {X : Type*} [Group X] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (hnf : (n, f) ≠ (4, 1))
    (e : X ≃* projectiveSL n K) (α : MulAut X) (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : X →* MulAut X).range) :
    PerfectTwistedFusion α :=
  F4Pilot.forall_perfectTwistedFusion_of_mulEquiv e
    (fun _ hβ hβo =>
      (perfectTwistedFusionIn_of_not_mem_range_conj hf hK hn hnf hβo hβ).perfectTwistedFusion)
    α hα hαo

end CFSG.SeitzReduction.LinearPilot
