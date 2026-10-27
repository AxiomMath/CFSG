module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResMatrix
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial

section Hermitian

variable {f : ℕ} {K : Type} [Field K]

theorem exists_opposite_hermitian (h : UnitaryFieldData 2 f K)
    {A N : Matrix (Fin 3) (Fin 3) K} (hAu : (A.map h.bar)ᵀ * A = 1)
    (hN2 : N * N = 0) (hN0 : N ≠ 0) (hNs : (N.map h.bar)ᵀ = N) (hAN : A * N = N * A)
    {lam : K} (hlam : lam ≠ 0) (hA3 : A * A * A = lam • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ N' : Matrix (Fin 3) (Fin 3) K, N' * N' = 0 ∧ (N'.map h.bar)ᵀ = N' ∧ N * N' * N = N ∧
      N' * N * N' = N' ∧ A * N' = N' * A := by
  classical
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  have hbar0 : ∀ x : K, h.bar x = 0 ↔ x = 0 := fun x => by simp
  obtain ⟨c, ℓ, hN, hc0, hℓ0, hℓc⟩ := exists_vecMulVec_of_sq_zero hN2 hN0
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc0 (funext hcon)
  obtain ⟨j₀, hj₀⟩ : ∃ j, ℓ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hℓ0 (funext hcon)
  have hs : ∀ i j, h.bar (c j) * h.bar (ℓ i) = c i * ℓ j := by
    intro i j
    have := congrFun₂ hNs i j
    simpa [hN, vecMulVec_apply, map_mul] using this
  obtain ⟨k, hk0, hℓk⟩ : ∃ k : K, k ≠ 0 ∧ ∀ j, ℓ j = k * h.bar (c j) := by
    set μ : K := h.bar (c j₀) / ℓ j₀ with hμ
    have hcμ : ∀ i, c i = μ * h.bar (ℓ i) := by
      intro i
      have := hs i j₀
      rw [hμ]
      field_simp
      linear_combination -this
    have hμ0 : μ ≠ 0 := by
      intro hμ0
      apply hi₀
      rw [hcμ i₀, hμ0, zero_mul]
    have hbμ0 : h.bar μ ≠ 0 := fun hh => hμ0 ((hbar0 μ).1 hh)
    refine ⟨(h.bar μ)⁻¹, inv_ne_zero hbμ0, fun j => ?_⟩
    have := congrArg h.bar (hcμ j)
    rw [map_mul, hbb] at this
    rw [this]
    field_simp
  have hiso : ∑ j, h.bar (c j) * c j = 0 := by
    have : ∑ j, ℓ j * c j = 0 := hℓc
    simp only [hℓk, mul_assoc, ← Finset.mul_sum] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hk0
    · exact h0
  have hbk : h.bar k = k := by
    have h1 := hs i₀ i₀
    rw [hℓk, map_mul, hbb] at h1
    have hne : c i₀ * h.bar (c i₀) ≠ 0 := mul_ne_zero hi₀ (fun hh => hi₀ ((hbar0 _).1 hh))
    apply mul_right_cancel₀ hne
    linear_combination h1
  set cs : (Fin 3 → K) → (Fin 3 → K) := fun v i => h.bar (v i) with hcs
  have cs_cs : ∀ v, cs (cs v) = v := fun v => funext fun i => hbb (v i)
  have cs_add : ∀ v w, cs (v + w) = cs v + cs w := fun v w => funext fun i => map_add _ _ _
  have cs_smul : ∀ (a : K) v, cs (a • v) = h.bar a • cs v := fun a v =>
    funext fun i => by simp [hcs]
  have cs_mulVec : ∀ (M : Matrix (Fin 3) (Fin 3) K) v, cs (M *ᵥ v) = cs v ᵥ* (M.map h.bar)ᵀ := by
    intro M v
    funext j
    simp only [hcs, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.vecMul,
      Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have bar_dot : ∀ v w, h.bar (cs w ⬝ᵥ v) = cs v ⬝ᵥ w := by
    intro v w
    simp only [hcs, dotProduct, map_sum, map_mul, hbb]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have csc0 : cs c ≠ 0 := fun hh => hi₀ ((hbar0 _).1 (congrFun hh i₀))
  have hℓ_eq : ℓ = k • cs c := funext hℓk
  obtain ⟨β, hAc, hℓA⟩ := eigen_of_commute_vecMulVec hc0 hℓ0 (hN ▸ hAN)
  have hcsA : cs c ᵥ* A = β • cs c := by
    rw [hℓ_eq, Matrix.smul_vecMul, smul_smul, mul_comm, ← smul_smul] at hℓA
    exact smul_right_injective _ hk0 hℓA
  have hstar : ∀ w, A *ᵥ w = β • w → cs w = h.bar β • (cs w ᵥ* A) := by
    intro w hw
    have e1 : cs (A *ᵥ w) = cs w ᵥ* (A.map h.bar)ᵀ := cs_mulVec A w
    rw [hw, cs_smul] at e1
    have e2 : (cs w ᵥ* (A.map h.bar)ᵀ) ᵥ* A = cs w := by
      rw [Matrix.vecMul_vecMul, hAu, Matrix.vecMul_one]
    rw [← e1, Matrix.smul_vecMul] at e2
    exact e2.symm
  have hββ : h.bar β * β = 1 := by
    have e := hstar c hAc
    rw [hcsA, smul_smul] at e
    have : (h.bar β * β - 1) • cs c = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 csc0
  have hβ3 : β ^ 3 = lam := by
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, c k₀ ≠ 0 := ⟨i₀, hi₀⟩
    have h1 : (A * A * A) *ᵥ c = lam • c := by
      rw [hA3, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2' : (A * A * A) *ᵥ c = (β ^ 3) • c := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAc]
      simp [Matrix.mulVec_smul, hAc, smul_smul, pow_succ, mul_assoc]
    have := congrFun (h2'.symm.trans h1) k₀
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hk₀ this
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, mul_zero] at hββ
    exact zero_ne_one hββ
  obtain ⟨π, hAπ, hπA, hπw, hπu⟩ := exists_eigen_projection hβ0 (hβ3 ▸ hA3)
  have hne0 : h.bar (c i₀) ≠ 0 := fun hh => hi₀ ((hbar0 _).1 hh)
  set v : Fin 3 → K := Pi.single i₀ (h.bar (c i₀))⁻¹ with hv
  have hcsv : cs c ⬝ᵥ v = 1 := by
    simp [hcs, hv, dotProduct_single, hne0]
  set c'' : Fin 3 → K := π *ᵥ v with hc''
  have hAc'' : A *ᵥ c'' = β • c'' := by
    rw [hc'', Matrix.mulVec_mulVec, hAπ, Matrix.smul_mulVec]
  have hcsc'' : cs c ⬝ᵥ c'' = 1 := by
    rw [hc'', Matrix.dotProduct_mulVec, hπu _ hcsA, hcsv]
  have hcsc0 : cs c ⬝ᵥ c = 0 := hiso
  set ρ : K := cs c'' ⬝ᵥ c'' with hρ
  have hρb : h.bar ρ = ρ := by rw [hρ, bar_dot]
  obtain ⟨s, hsρ⟩ : ∃ s : K, s + h.bar s = ρ := by
    obtain ⟨s, hs'⟩ := h.traceLin_surjective ⟨ρ, h.mem_fixedField.2 hρb⟩
    exact ⟨s, by simpa [UnitaryFieldData.trace] using congrArg Subtype.val hs'⟩
  set c' : Fin 3 → K := c'' + s • c with hc'
  have hAc' : A *ᵥ c' = β • c' := by
    rw [hc', Matrix.mulVec_add, Matrix.mulVec_smul, hAc, hAc'', smul_add, smul_comm]
  have hcsc' : cs c ⬝ᵥ c' = 1 := by
    rw [hc', dotProduct_add, dotProduct_smul, hcsc'', hcsc0, smul_zero, add_zero]
  have hc'sc : cs c' ⬝ᵥ c = 1 := by
    rw [← bar_dot c' c, hcsc', map_one]
  have hc''sc : cs c'' ⬝ᵥ c = 1 := by
    rw [← bar_dot c'' c, hcsc'', map_one]
  have hiso' : cs c' ⬝ᵥ c' = 0 := by
    rw [hc', cs_add, cs_smul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hcsc0, hcsc'', hc''sc, ← hρ]
    linear_combination hsρ + ρ * h2
  have hcs'A : cs c' ᵥ* A = β • cs c' := by
    have e := hstar c' hAc'
    calc cs c' ᵥ* A = (β * h.bar β) • (cs c' ᵥ* A) := by rw [mul_comm, hββ, one_smul]
      _ = β • (h.bar β • (cs c' ᵥ* A)) := by rw [smul_smul]
      _ = β • cs c' := by rw [← e]
  have hNk : N = k • vecMulVec c (cs c) := by rw [hN, hℓ_eq, vecMulVec_smul]
  set N' : Matrix (Fin 3) (Fin 3) K := k⁻¹ • vecMulVec c' (cs c') with hN'
  have hNN' : N * N' = vecMulVec c (cs c') := by
    rw [hNk, hN', Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hcsc', one_smul,
      smul_smul, mul_inv_cancel₀ hk0, one_smul]
  have hN'N : N' * N = vecMulVec c' (cs c) := by
    rw [hNk, hN', Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hc'sc, one_smul,
      smul_smul, inv_mul_cancel₀ hk0, one_smul]
  refine ⟨N', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN', Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hiso', zero_smul]
    simp
  · ext a b
    simp only [hN', Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, map_mul, map_inv₀, hbk, hcs, hbb]
    ring
  · rw [hNN', hNk, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hc'sc, one_smul]
  · rw [hN'N, hN', Matrix.mul_smul, vecMulVec_mul_vecMulVec, hcsc', one_smul]
  · rw [hN', Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, hAc', hcs'A,
      smul_vecMulVec, vecMulVec_smul]

end Hermitian

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
