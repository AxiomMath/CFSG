module

public import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.GH74.GLS.Stage2.OddAut.KerFlag

open Matrix Polynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem matrix_ext_mulVec {M M' : Matrix ι ι K} (h : ∀ x, M *ᵥ x = M' *ᵥ x) : M = M' := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem mulVec_pow_succ' (M : Matrix ι ι K) (j : ℕ) (x : ι → K) :
    (M ^ (j + 1)) *ᵥ x = M *ᵥ ((M ^ j) *ᵥ x) := by
  rw [pow_succ', Matrix.mulVec_mulVec]

theorem nilpotent_of_scalar_on_ker {N B : Matrix ι ι K} {a : K} {m : ℕ} (hN : N ^ m = 0)
    (hcomm : B * N = N * B) (hker : ∀ x, N *ᵥ x = 0 → B *ᵥ x = a • x) :
    (B - a • (1 : Matrix ι ι K)) ^ m = 0 := by
  set D : Matrix ι ι K := B - a • 1 with hD
  have hDN : D * N = N * D := by
    rw [hD, sub_mul, mul_sub, hcomm]
    simp
  have hD1 : ∀ x, N *ᵥ x = 0 → D *ᵥ x = 0 := by
    intro x hx
    rw [hD, Matrix.sub_mulVec, hker x hx]
    simp [Matrix.smul_mulVec]
  have key : ∀ j : ℕ, ∀ x, (N ^ j) *ᵥ x = 0 → (D ^ j) *ᵥ x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have h1 : (N ^ j) *ᵥ (N *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, ← pow_succ]; exact hx
      have h2 := ih _ h1
      have h3 : N *ᵥ ((D ^ j) *ᵥ x) = 0 := by
        have hc : N * D ^ j = D ^ j * N :=
          (Commute.pow_right (show Commute N D from hDN.symm) j).eq
        rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
        exact h2
      rw [mulVec_pow_succ']
      exact hD1 _ h3
  exact matrix_ext_mulVec fun x => by
    rw [Matrix.zero_mulVec]
    exact key m x (by rw [hN, Matrix.zero_mulVec])

theorem exists_ker_range {N : Matrix ι ι K} {m : ℕ} (hN : N ^ m = 0) (hne : N ≠ 0) :
    ∃ y w : ι → K, y ≠ 0 ∧ N *ᵥ y = 0 ∧ N *ᵥ w = y := by
  classical
  have hex : ∃ k, N ^ (k + 1) = 0 := ⟨m, by rw [pow_succ, hN, zero_mul]⟩
  have hk : N ^ (Nat.find hex + 1) = 0 := Nat.find_spec hex
  have hk1 : 1 ≤ Nat.find hex := by
    by_contra h
    have h0 : Nat.find hex = 0 := by omega
    rw [h0] at hk
    exact hne (by simpa using hk)
  have hnk : N ^ (Nat.find hex) ≠ 0 := by
    intro h
    apply Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel hk1]
    exact h
  obtain ⟨x, hx⟩ : ∃ x, (N ^ (Nat.find hex)) *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnk (matrix_ext_mulVec fun x => by rw [hcon x, Matrix.zero_mulVec])
  refine ⟨(N ^ (Nat.find hex)) *ᵥ x, (N ^ (Nat.find hex - 1)) *ᵥ x, hx, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, ← pow_succ', hk, Matrix.zero_mulVec]
  · rw [Matrix.mulVec_mulVec, ← pow_succ', Nat.sub_add_cancel hk1]

theorem linear_eq_dotProduct (g : (ι → K) →ₗ[K] K) (x : ι → K) :
    g x = (fun i => g (Pi.single i 1)) ⬝ᵥ x := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : K) : ι → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, dotProduct, smul_eq_mul, mul_comm]

theorem exists_dual_vanishing {N : Matrix ι ι K} {y w : ι → K} (hy : y ≠ 0)
    (hNy : N *ᵥ y = 0) (hw : N *ᵥ w = y) :
    ∃ ψ : ι → K, ψ ≠ 0 ∧ (∀ x, ψ ⬝ᵥ (N *ᵥ x) = 0) ∧ (∀ x, N *ᵥ x = 0 → ψ ⬝ᵥ x = 0) := by
  classical
  let f : (ι → K) →ₗ[K] (ι → K) := Matrix.mulVecLin N
  have hlt : LinearMap.range f ⊔ LinearMap.ker f < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.ker f)
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    rw [htop, finrank_top] at h1
    have h3 : Module.finrank K (↥(LinearMap.range f ⊓ LinearMap.ker f)) = 0 := by omega
    have h4 : LinearMap.range f ⊓ LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp h3
    have h5 : y ∈ LinearMap.range f ⊓ LinearMap.ker f := ⟨⟨w, hw⟩, hNy⟩
    rw [h4] at h5
    exact hy ((Submodule.mem_bot K).mp h5)
  obtain ⟨g, hg0, hgle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  refine ⟨fun i => g (Pi.single i 1), ?_, ?_, ?_⟩
  · intro h
    apply hg0
    refine LinearMap.ext fun x => ?_
    rw [linear_eq_dotProduct g x, h]
    simp
  · intro x
    rw [← linear_eq_dotProduct]
    exact hgle (le_sup_left (a := LinearMap.range f) (b := LinearMap.ker f) ⟨x, rfl⟩)
  · intro x hx
    rw [← linear_eq_dotProduct]
    exact hgle (le_sup_right (a := LinearMap.range f) (b := LinearMap.ker f) hx)

@[expose] def TN (N : Matrix ι ι K) : Submodule K (Matrix ι ι K) where
  carrier := {θ | N * θ = 0 ∧ θ * N = 0 ∧ ∀ x, N *ᵥ x = 0 → θ *ᵥ x = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨by rw [mul_add, ha1, hb1, add_zero], by rw [add_mul, ha2, hb2, add_zero],
      fun x hx => ?_⟩
    rw [Matrix.add_mulVec, ha3 x hx, hb3 x hx, add_zero]
  zero_mem' := ⟨by simp, by simp, fun x _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    refine ⟨by rw [Matrix.mul_smul, ha1, smul_zero], by rw [Matrix.smul_mul, ha2, smul_zero],
      fun x hx => ?_⟩
    rw [Matrix.smul_mulVec, ha3 x hx, smul_zero]

theorem TN_mul_eq_zero {N θ θ' : Matrix ι ι K} (hθ : θ ∈ TN N) (hθ' : θ' ∈ TN N) :
    θ * θ' = 0 := by
  refine matrix_ext_mulVec fun x => ?_
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
  apply hθ.2.2
  rw [Matrix.mulVec_mulVec, hθ'.1, Matrix.zero_mulVec]

omit [DecidableEq ι] in
theorem vecMulVec_mulVec_field (u v w : ι → K) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

theorem vecMulVec_mem_TN {N : Matrix ι ι K} {e ψ : ι → K} (he : N *ᵥ e = 0)
    (hψ1 : ∀ x, ψ ⬝ᵥ (N *ᵥ x) = 0) (hψ2 : ∀ x, N *ᵥ x = 0 → ψ ⬝ᵥ x = 0) (c : K) :
    Matrix.vecMulVec e (c • ψ) ∈ TN N := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mul_vecMulVec, he]
    ext i j; simp
  · rw [Matrix.vecMulVec_mul]
    have : (c • ψ) ᵥ* N = 0 := by
      rw [Matrix.smul_vecMul]
      have h0 : ψ ᵥ* N = 0 := by
        ext j
        have := hψ1 (Pi.single j 1)
        rw [Matrix.mulVec_single_one] at this
        exact this
      rw [h0, smul_zero]
    rw [this]
    ext i j; simp
  · rw [vecMulVec_mulVec_field, smul_dotProduct, hψ2 x hx]
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem map_vecMulVec (σ : K ≃+* K) (u v : ι → K) :
    (Matrix.vecMulVec u v).map σ = Matrix.vecMulVec (σ ∘ u) (σ ∘ v) := by
  ext i j
  simp [Matrix.vecMulVec_apply]

theorem sigma_one_and_scalar {N B B' : Matrix ι ι K} {σ : K ≃+* K} {y ψ : ι → K}
    (hy : y ≠ 0) (hNy : N *ᵥ y = 0) (hψ0 : ψ ≠ 0)
    (hψ1 : ∀ x, ψ ⬝ᵥ (N *ᵥ x) = 0) (hψ2 : ∀ x, N *ᵥ x = 0 → ψ ⬝ᵥ x = 0)
    (hBB : B' * B = 1) (hfix : ∀ θ ∈ TN N, B * θ.map σ = θ * B) :
    σ = 1 ∧ ∃ a : K, ∀ x, N *ᵥ x = 0 → B *ᵥ x = a • x := by
  have hE : ∀ e, N *ᵥ e = 0 → ∀ c : K, ∀ i j, (B *ᵥ (σ ∘ e)) i * (σ c * σ (ψ j)) =
      e i * (c * (ψ ᵥ* B) j) := by
    intro e he c i j
    have h := hfix _ (vecMulVec_mem_TN he hψ1 hψ2 c)
    rw [map_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at h
    have := congrFun (congrFun h i) j
    simpa [Matrix.vecMulVec_apply, Matrix.smul_vecMul] using this
  obtain ⟨j₀, hj₀⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hψ0 (funext hcon)
  have hσ : ∀ c : K, σ c = c := by
    intro c
    have hu : B *ᵥ (σ ∘ y) ≠ 0 := by
      intro h0
      apply hy
      have h1 : B' *ᵥ (B *ᵥ (σ ∘ y)) = σ ∘ y := by
        rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h1
      funext i
      have := congrFun h1 i
      simpa using this.symm
    obtain ⟨i, hi⟩ : ∃ i, (B *ᵥ (σ ∘ y)) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (funext hcon)
    have h1 := hE y hNy 1 i j₀
    have h2 := hE y hNy c i j₀
    rw [map_one] at h1
    have key : (B *ᵥ (σ ∘ y)) i * σ (ψ j₀) * (σ c - c) = 0 := by
      linear_combination h2 - c * h1
    have hs : σ (ψ j₀) ≠ 0 := (map_ne_zero σ).mpr hj₀
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (mul_ne_zero hi hs)
    · exact sub_eq_zero.mp h
  refine ⟨RingEquiv.ext fun c => by simpa using hσ c, (ψ ᵥ* B) j₀ / ψ j₀, fun e he => ?_⟩
  funext i
  have h := hE e he 1 i j₀
  have hσe : (σ ∘ e) = e := funext fun i => hσ (e i)
  rw [hσe, hσ 1, hσ (ψ j₀)] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination h

theorem one_add_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP K p] {M : Matrix ι ι K} {m e : ℕ}
    (hM : M ^ m = 0) (hm : m ≤ p ^ e) : ((1 : Matrix ι ι K) + M) ^ (p ^ e) = 1 := by
  have h := congrArg (Polynomial.aeval M) (add_pow_char_pow (R := K[X]) (p := p) (1 : K[X]) X e)
  simp only [map_pow, map_add, map_one, aeval_X] at h
  rw [h]
  have : M ^ (p ^ e) = 0 := by
    have : p ^ e = m + (p ^ e - m) := by omega
    rw [this, pow_add, hM, zero_mul]
  rw [this, one_pow, add_zero]

end CFSG.GH74.GLS.Stage2.OddAut.KerFlag
