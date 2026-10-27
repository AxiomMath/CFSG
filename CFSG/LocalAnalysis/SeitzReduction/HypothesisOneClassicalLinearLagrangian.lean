module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearLagrangianGraph
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearInner

public noncomputable section

namespace CFSG.SeitzReduction.ClassicalLinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open Lagrangian

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_lagrangian_basis [CharP K 2] {s : GL (Fin n) K} (hs : s * s = 1)
    (hWL : LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) =
      LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))) :
    ∃ (ℓ : ℕ) (b : Module.Basis (Fin ℓ ⊕ (Fin ℓ ⊕ Fin 0)) K (Fin n → K)),
      (∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i))) ∧
      (∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) ∧ n = 2 * ℓ := by
  set N := (s : Matrix (Fin n) (Fin n) K) - 1 with hNdef
  have hs' : (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, hs, Units.val_one]
  have hNN : N * N = 0 := by
    calc N * N = (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) + 1 -
          ((s : Matrix (Fin n) (Fin n) K) + (s : Matrix (Fin n) (Fin n) K)) := by
          rw [hNdef]; noncomm_ring
      _ = 0 := by
          rw [hs', ← two_smul K (1 : Matrix (Fin n) (Fin n) K),
            ← two_smul K (s : Matrix (Fin n) (Fin n) K), CharTwo.two_eq_zero, zero_smul,
            zero_smul, sub_zero]
  set F := Matrix.mulVecLin N with hF
  have hF2 : F ∘ₗ F = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, hF, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_mulVec,
      hNN, zero_mulVec, LinearMap.zero_apply]
  obtain ⟨r, b, hb1, hb2⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_basis_sq_eq_zero F hF2
  have hcard := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun] at hcard
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hrank := LinearMap.finrank_range_add_finrank_ker F
  rw [Module.finrank_fin_fun] at hrank
  have hRK : Module.finrank K (LinearMap.range F) = Module.finrank K (LinearMap.ker F) := by
    rw [hF, hWL]
  have hr : r = 0 := by omega
  subst hr
  exact ⟨_, b, hb1, hb2, by omega⟩

theorem involutionCriterion_conjAut_of_eq {f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hnf : ¬(n = 4 ∧ f = 1)) {s : GL (Fin n) K} (hs : s * s = 1)
    (hWL : LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) =
      LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))) :
    InvolutionCriterion (conjAut n K s) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hn3 : 3 ≤ n := by omega
  obtain ⟨ℓ, b, hbX, hbL, hnℓ⟩ := exists_lagrangian_basis hs hWL
  intro β _ hβc
  have hfix : ∀ d ∈ closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)},
      β d = d := fun d hd => apply_eq_self_of_mem_closure (fun c hc => hβc c hc.1 hc.2) hd
  obtain ⟨A, φ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn3).2 β
  have hdot : ∀ i j : Fin ℓ, ∀ c : K, dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0 :=
    fun i j c => by rw [dotProduct_smul, dualVec_inl_dotProduct_inr, smul_zero]
  have hdotE : ∀ {i₀ i₁ : Fin ℓ}, (dualVec b (.inl i₁) - dualVec b (.inl i₀)) ⬝ᵥ
      (b (.inr (.inl i₀)) + b (.inr (.inl i₁))) = 0 := fun {i₀ i₁} => by
    simp only [sub_dotProduct, dotProduct_add, dualVec_inl_dotProduct_inr, add_zero, sub_zero]
  have hone : ∀ i j : Fin ℓ, ∀ (h : dualVec b (.inl i) ⬝ᵥ b (.inr (.inl j)) = 0),
      rankOne (b (.inr (.inl j))) (dualVec b (.inl i)) h =
        rankOne ((1 : K) • b (.inr (.inl j))) (dualVec b (.inl i)) (hdot i j 1) :=
    fun i j h => rankOne_eq (one_smul K _).symm rfl h _
  rcases (show ℓ = 2 ∨ 3 ≤ ℓ by omega) with rfl | hℓ
  ·
    have hf2 : 2 ≤ f := by
      by_contra hcon
      exact hnf ⟨by omega, by omega⟩
    obtain ⟨t, ht0, ht2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K (by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hDtwo : ∀ g ∈ twoSet b h01, proj n K g ∈
        closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} :=
      fun g hg => twoSet_mem_closure_odd_fixed b hbX hbL h01 ht0 ht2 hg
    have hoffD : ∀ i j : Fin 2, i ≠ j → ∀ (c : K)
        (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0),
        proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h) ∈
          closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
      intro i j hij c h
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hDtwo _ (Or.inr (Or.inl ⟨c, h, rfl⟩))
      · exact hDtwo _ (Or.inl ⟨c, h, rfl⟩)
      · exact absurd rfl hij
    have hextD : ∀ h : (dualVec b (.inl 1) - dualVec b (.inl 0)) ⬝ᵥ
        (b (.inr (.inl 0)) + b (.inr (.inl 1))) = 0,
        proj n K (rankOne (b (.inr (.inl 0)) + b (.inr (.inl 1)))
          (dualVec b (.inl 1) - dualVec b (.inl 0)) h) ∈
          closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := fun h =>
      extra_mem_closure_odd_fixed b hbX hbL h01 (dualVec_inl_dotProduct_inr b 1 0)
        (by rw [hone]; exact hoffD 1 0 h01.symm 1 _) h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero, mul_one] at hfix ⊢
      exact sq_eq_one_of_fix_conjAut_mul_fieldAut b hn3 h01
        (fun i j hij c h => hfix _ (hoffD i j hij c h)) (fun h => hfix _ (hextD h))
    · rw [pow_one] at hfix ⊢
      exact sq_eq_one_of_fix_dualAut_two b hn3
        (fun i j hij c h => hfix _ (hoffD i j hij c h)) (fun h => hfix _ (hextD h))
        (hfix _ (hDtwo _ (Or.inr (Or.inr ⟨1, rfl⟩))))
  ·
    set i₀ : Fin ℓ := ⟨0, by omega⟩
    set i₁ : Fin ℓ := ⟨1, by omega⟩
    set i₂ : Fin ℓ := ⟨2, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
    have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
    have hoffD : ∀ i j : Fin ℓ, i ≠ j → ∀ (c : K)
        (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0),
        proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h) ∈
          closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} :=
      fun i j hij c h =>
        offDiag_mem_closure_odd_fixed b hbX hbL hℓ (rankOne_mem_offDiag b hij c h)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero, mul_one] at hfix ⊢
      exact sq_eq_one_of_fix_conjAut_mul_fieldAut b hn3 h01
        (fun i j hij c h => hfix _ (hoffD i j hij c h))
        (fun h => hfix _ (extra_mem_closure_odd_fixed b hbX hbL h01
          (dualVec_inl_dotProduct_inr b i₁ i₀)
          (by rw [hone]; exact hoffD i₁ i₀ h01.symm 1 _) h))
    · rw [pow_one] at hfix
      exact (false_of_fix_dualAut b hn3 h12
        (fun h => hfix _ (by rw [hone]; exact hoffD i₀ i₁ h01 1 _))
        (fun h => hfix _ (by rw [hone]; exact hoffD i₀ i₂ h02 1 _))).elim

theorem involutionCriterion_of_mem_inner {f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hnf : ¬(n = 4 ∧ f = 1)) {t : MulAut (projectiveSL n K)}
    (htI : t ∈ inner (projectiveSL n K)) (ht : orderOf t = 2) : InvolutionCriterion t := by
  rcases involutionCriterion_or_lagrangian hn hf hK htI ht with h | ⟨s, rfl, hss, -, hWL⟩
  · exact h
  · exact involutionCriterion_conjAut_of_eq hn hf hK hnf hss hWL

end CFSG.SeitzReduction.ClassicalLinear
