module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR7iiiMatrix
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutUBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

section Proj

theorem proj_four_injective [CharP K 2] : Function.Injective (proj 4 K) := by
  intro A B h
  rw [proj_eq_proj_iff] at h
  obtain ⟨c, hc4, hc⟩ := mem_scalars.1 h
  have hc4' : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
  have hc1 : (c : K) = 1 :=
    eq_one_of_sq_eq_one (eq_one_of_sq_eq_one (by rw [← pow_mul]; exact hc4'))
  have h1 : A⁻¹ * B = 1 := Subtype.ext (by rw [hc, hc1, map_one]; rfl)
  calc A = A * (A⁻¹ * B) := by rw [h1, mul_one]
    _ = B := by group

end Proj

section OddOrder

variable {n : ℕ}

theorem mem_semilinearAutGroup_of_pow_eq_one_of_odd [Finite K] (hn : 3 ≤ n)
    {β : MulAut (projectiveSL n K)} {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1) :
    β ∈ semilinearAutGroup n K := by
  have hR : β ∈ standardAutGroup n K := by
    rw [(automorphism_generation hn).1]
    exact mem_top β
  have hδδ : dualAut n K * dualAut n K = 1 :=
    (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
  have hsq : β * β ∈ semilinearAutGroup n K := by
    rcases mem_or_mul_dualAut_mem hR with h | h
    · exact mul_mem h h
    · have e : β * β = (β * dualAut n K) * (dualAut n K * (β * dualAut n K) * dualAut n K) := by
        calc β * β = β * 1 * β * 1 := by group
          _ = β * (dualAut n K * dualAut n K) * β * (dualAut n K * dualAut n K) := by rw [hδδ]
          _ = _ := by group
      rw [e]
      exact mul_mem h (dualAut_mul_mul_dualAut_mem h)
  obtain ⟨k, rfl⟩ := hm
  have h2 : (β * β) ^ (k + 1) = β := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hβ, one_mul]
  rw [← h2]
  exact pow_mem hsq _

theorem eq_one_and_commute_of_fix_transvection (A : GL (Fin n) K) (σ : K ≃+* K) {i j : Fin n}
    (hij : i ≠ j)
    (h : ∀ c : K, (conjAut n K A * fieldAut n K σ)
        (proj n K (SpecialLinearGroup.transvection hij c)) =
      proj n K (SpecialLinearGroup.transvection hij c)) :
    σ = 1 ∧ Commute (single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := by
  have h1 := single_mul_eq_of_conjAut_mul_fieldAut_apply A σ hij 1 1 (h 1)
  rw [map_one] at h1
  have hcom : Commute (single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := h1
  refine ⟨?_, hcom⟩
  have hdiag : (A : Matrix (Fin n) (Fin n) K) i i = (A : Matrix (Fin n) (Fin n) K) j j :=
    diag_eq_of_commute_single hcom
  have hcol : ∀ k, k ≠ i → (A : Matrix (Fin n) (Fin n) K) k i = 0 :=
    fun k hk => col_eq_zero_of_commute_single hcom hk
  have hii : (A : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    intro h0
    have hdet : (A : Matrix (Fin n) (Fin n) K).det = 0 := by
      refine det_eq_zero_of_col (j := i) fun k => ?_
      by_cases hk : k = i
      · rw [hk, h0]
      · exact hcol k hk
    exact (Matrix.GeneralLinearGroup.det_ne_zero A) hdet
  refine RingEquiv.ext fun c => ?_
  have hc := congrFun (congrFun (single_mul_eq_of_conjAut_mul_fieldAut_apply A σ hij c c (h c)) i) j
  rw [single_mul_apply_same, mul_single_apply_same, ← hdiag] at hc
  have hc' : (σ c - c) * (A : Matrix (Fin n) (Fin n) K) i i = 0 := by linear_combination -hc
  rcases mul_eq_zero.1 hc' with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 hii

end OddOrder

section Four

variable [CharP K 2]

theorem exists_pow_eq_smul_one_of_conjAut_pow_eq_one (A : GL (Fin 4) K) {m : ℕ}
    (h : conjAut 4 K A ^ m = 1) :
    ∃ ν : K, ν ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) K) ^ m = ν • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [← map_pow] at h
  set B : GL (Fin 4) K := A ^ m with hB
  have hcomm : Pairwise fun i j : Fin 4 =>
      Commute (single i j (1 : K)) (B : Matrix (Fin 4) (Fin 4) K) := by
    intro i j hij
    have h1 := congrArg (fun φ : MulAut (projectiveSL 4 K) =>
      φ (proj 4 K (SpecialLinearGroup.transvection hij 1))) h
    simp only [MulAut.one_apply, conjAut_proj] at h1
    have h2 := congrArg (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K))
      (proj_four_injective h1)
    simp only [coe_slConjugation, SpecialLinearGroup.transvection_coe] at h2
    set E : Matrix (Fin 4) (Fin 4) K := 1 + single i j (1 : K) with hEdef
    have h3 : (B : Matrix (Fin 4) (Fin 4) K) * E = E * (B : Matrix (Fin 4) (Fin 4) K) := by
      calc (B : Matrix (Fin 4) (Fin 4) K) * E
          = (B : Matrix (Fin 4) (Fin 4) K) * E *
              (((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                (B : Matrix (Fin 4) (Fin 4) K)) := by
            rw [Units.inv_mul, Matrix.mul_one]
        _ = ((B : Matrix (Fin 4) (Fin 4) K) * E *
              ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
                (B : Matrix (Fin 4) (Fin 4) K) := by
            simp only [Matrix.mul_assoc]
        _ = E * (B : Matrix (Fin 4) (Fin 4) K) := by rw [h2]
    rw [hEdef] at h3
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj] at h3
    exact h3.symm
  obtain ⟨ν, hν⟩ := mem_range_scalar_of_commute_single hcomm
  have hBm : (B : Matrix (Fin 4) (Fin 4) K) = (A : Matrix (Fin 4) (Fin 4) K) ^ m := by
    rw [hB, Units.val_pow_eq_pow_val]
  refine ⟨ν, ?_, ?_⟩
  · rintro rfl
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero B
    rw [← hν, map_zero, det_zero] at hdet
    exact hdet rfl
  · rw [← hBm, ← hν, scalar_apply, smul_one_eq_diagonal]

theorem exists_conjAut_blockSL_fix [Finite K] (P : InvPlacement 4 1)
    {β : MulAut (projectiveSL 4 K)} {m : ℕ} (hm : Odd m) (hβm : β ^ m = 1)
    (hβR : ∀ c : K, β (proj 4 K (SpecialLinearGroup.transvection (P.u_ne_w 0 0) c)) =
      proj 4 K (SpecialLinearGroup.transvection (P.u_ne_w 0 0) c))
    {R : SpecialLinearGroup (Fin 4) K} (hR : R ∈ P.radical K)
    (hRQ : ∃ i j, (R : Matrix (Fin 4) (Fin 4) K) i j ≠ (1 : Matrix (Fin 4) (Fin 4) K) i j ∧
      ¬ (i = P.u 0 ∧ j = P.w 0))
    (hβr : β (proj 4 K R) = proj 4 K R) :
    ∃ (g : GL (Fin 4) K) (b : Fin 4), ∀ x ∈ blockSL (K := K) ({b}ᶜ : Finset (Fin 4)),
      β (conjAut 4 K g x) = conjAut 4 K g x := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1
    (mem_semilinearAutGroup_of_pow_eq_one_of_odd (by norm_num) hm hβm)
  obtain ⟨rfl, hE⟩ := eq_one_and_commute_of_fix_transvection A σ (P.u_ne_w 0 0) hβR
  rw [map_one, mul_one] at hβm hβr ⊢
  obtain ⟨ν, hν, hAm⟩ := exists_pow_eq_smul_one_of_conjAut_pow_eq_one A hβm
  set M := (A : Matrix (Fin 4) (Fin 4) K) with hM
  have hAR : M * (R : Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) * M := by
    rw [conjAut_proj] at hβr
    have h2 := congrArg (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K))
      (proj_four_injective hβr)
    simp only [coe_slConjugation] at h2
    calc M * (R : Matrix (Fin 4) (Fin 4) K)
        = M * (R : Matrix (Fin 4) (Fin 4) K) *
            (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * M) := by
          rw [hM, Units.inv_mul, Matrix.mul_one]
      _ = (M * (R : Matrix (Fin 4) (Fin 4) K) *
            ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * M := by
          simp only [Matrix.mul_assoc]
      _ = (R : Matrix (Fin 4) (Fin 4) K) * M := by rw [hM, h2]
  set N := (R : Matrix (Fin 4) (Fin 4) K) - 1 with hN
  have hNM : Commute N M := by
    show N * M = M * N
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAR]
  have hNsupp : ∀ i j, N i j ≠ 0 → (i = P.u 0 ∧ j ≠ P.u 0) ∨ (j = P.w 0 ∧ i ≠ P.w 0) := by
    intro i j hij
    have hlt : P.level i < P.level j := by
      by_contra hle
      push Not at hle
      apply hij
      rw [hN, Matrix.sub_apply, hR i j hle, sub_self]
    have hj2 := P.level_le_two j
    rcases Nat.lt_or_ge (P.level i) 1 with hi0 | hi1
    · obtain ⟨a, ha⟩ := (P.level_eq_zero_iff (i := i)).1 (by omega)
      left
      refine ⟨by rw [← ha, Subsingleton.elim a 0], fun hju => ?_⟩
      rw [hju, P.level_u] at hlt
      omega
    · obtain ⟨a, ha⟩ := (P.level_eq_two_iff (i := j)).1 (by omega)
      right
      refine ⟨by rw [← ha, Subsingleton.elim a 0], fun hiw => ?_⟩
      rw [hiw, P.level_w] at hlt
      omega
  have hN' : ∃ i j, N i j ≠ 0 ∧ ¬ (i = P.u 0 ∧ j = P.w 0) := by
    obtain ⟨i, j, hij, hne⟩ := hRQ
    exact ⟨i, j, by rw [hN, Matrix.sub_apply]; exact sub_ne_zero.2 hij, hne⟩
  obtain ⟨g, b, hg, hcomm⟩ :=
    exists_commute_conj_of_commute_single (P.u_ne_w 0 0) hE hNM hNsupp hN' hm hν hAm
  set G : GL (Fin 4) K := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.2 hg) with hG
  have hGc : (G : Matrix (Fin 4) (Fin 4) K) = g := rfl
  have hGi : ((G⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = g⁻¹ := rfl
  refine ⟨G, b, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  rw [conjAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_slConjugation, hGc, hGi]
  have hc := hcomm (h : Matrix (Fin 4) (Fin 4) K) fun i j hij => hh i j (by
    rcases hij with rfl | rfl <;> simp)
  rw [← hM, hc.eq, Matrix.mul_assoc _ M, hM, Units.mul_inv, Matrix.mul_one]

end Four

end CFSG.SeitzReduction.LinearPilot
