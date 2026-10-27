module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODMono

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open Matrix Module

theorem prod_pow_fin_eq_one {K : Type*} [CommMonoid K] {p : ℕ} (hodd : Odd p) {τ : K}
    (hτ : τ ^ p = 1) : ∏ j : Fin p, τ ^ (j : ℕ) = 1 := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) p]
  have h := Finset.sum_range_id_mul_two p
  obtain ⟨q, hq⟩ := hodd
  have h2 : (∑ i ∈ Finset.range p, i) = p * q := by
    have h3 : (∑ i ∈ Finset.range p, i) * 2 = (p * q) * 2 := by
      rw [h, hq]
      simp only [Nat.add_sub_cancel]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  rw [h2, pow_mul, hτ, one_pow]

theorem exists_twist {p : ℕ} (hp : p.Prime) (hodd : Odd p) {K : Type*} [Field K]
    {M : Matrix (Fin p) (Fin p) K} {ω : K} (hM : M ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) {τ : K} (hτ : τ ^ p = 1) :
    ∃ Φ : Matrix (Fin p) (Fin p) K, Φ.det = 1 ∧ Φ ^ p = 1 ∧ Φ * M = τ • (M * Φ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hT : (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin p → K)) ω := by
    have hc := AlgEquiv.commutes (Matrix.toLinAlgEquiv' (R := K) (n := Fin p)) ω
    rw [show (Matrix.toLin' M) = Matrix.toLinAlgEquiv' M from rfl, ← map_pow, hM]
    exact hc
  obtain ⟨m, b, u, hb⟩ := CFSG.LocalAnalysis.RankFourTheoremC.I294OD.exists_monomial_basis hp hω hT
  set d : Fin p × Fin m → K := fun x => τ ^ (x.1 : ℕ) with hd
  let D : Module.End K (Fin p → K) := b.constr K (fun x => d x • b x)
  have hD : ∀ x, D (b x) = d x • b x := fun x => by simp [D]
  have hdsucc : ∀ x : Fin p × Fin m, d (x.1 + 1, x.2) = τ * d x := by
    intro x
    simp only [hd]
    have hval : ((x.1 + 1 : Fin p) : ℕ) = ((x.1 : ℕ) + 1) % p := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hp.one_lt]
    rw [hval]
    by_cases h : (x.1 : ℕ) + 1 < p
    · rw [Nat.mod_eq_of_lt h, pow_succ']
    · have h1 : (x.1 : ℕ) + 1 = p := by have := x.1.2; omega
      rw [← pow_succ', h1, Nat.mod_self, pow_zero, hτ]
  have hDT : D * Matrix.toLin' M = τ • (Matrix.toLin' M * D) := by
    refine b.ext fun x => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hD, hb, map_smul, smul_smul, hdsucc]
    congr 1
    ring
  have hmat : LinearMap.toMatrix b b D = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hD, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases h : j = i
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hdet : LinearMap.det D = 1 := by
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Fintype.prod_prod_type]
    simp only [hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow, prod_pow_fin_eq_one hodd hτ, one_pow]
  have hDp : D ^ p = 1 := by
    have h1 : ∀ (n : ℕ) (x : Fin p × Fin m), (D ^ n) (b x) = d x ^ n • b x := by
      intro n x
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Module.End.mul_apply, hD, map_smul, ih, smul_smul, ← pow_succ']
    refine b.ext fun x => ?_
    rw [h1, Module.End.one_apply]
    have : d x ^ p = 1 := by
      simp only [hd]
      rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
    rw [this, one_smul]
  refine ⟨LinearMap.toMatrix' D, ?_, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix', hdet]
  · have h1 := congrArg (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin p)) hDp
    rw [map_pow, map_one] at h1
    exact h1
  · have h1 := congrArg (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin p)) hDT
    rw [map_mul, map_smul, map_mul] at h1
    have h2 : LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin p) (Matrix.toLin' M) = M :=
      LinearMap.toMatrix'_toLin' M
    rw [h2] at h1
    exact h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
