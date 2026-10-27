module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292T

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open P614K292
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type} [Field K]

theorem exists_fixed_line [Finite K] {R : Subgroup (GL (Fin 3) K)} (hR : IsPGroup 2 R) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ r ∈ R, ∃ c : K, (r : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (ℙ K (Fin 3 → K)) = 1 + Nat.card K * (Nat.card K + 1) := by
    rw [Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    ring
  have hodd : ¬ 2 ∣ Nat.card (ℙ K (Fin 3 → K)) := by
    rw [hcard]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 (Nat.even_mul_succ_self _).one_add)
  obtain ⟨x, hx⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card (ℙ K (Fin 3 → K)) hodd
  refine ⟨x.rep, x.rep_nonzero, fun r hr => ?_⟩
  have h := MulAction.mem_fixedPoints.1 hx ⟨r, hr⟩
  rw [← Projectivization.mk_rep x] at h
  change Projectivization.mk K ((r : Matrix (Fin 3) (Fin 3) K) *ᵥ x.rep) _ = _ at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).1 h
  exact ⟨a, ha.symm⟩

theorem eq_of_eig {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {g h : GL (Fin 3) K}
    {e : Fin 3 → K} (hg : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = e i • b i)
    (hh : ∀ i, (h : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = e i • b i) : g = h := by
  obtain ⟨P, hP⟩ := isUnit_colMat hb
  have h1 : (g : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
      (h : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) := by
    rw [hP, mul_colMat_eq hg, mul_colMat_eq hh]
  exact Units.ext ((Units.mul_left_inj P).1 h1)

theorem det_eq_of_eig {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {g : GL (Fin 3) K}
    {e : Fin 3 → K} (hg : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = e i • b i) :
    (g : Matrix (Fin 3) (Fin 3) K).det = e 0 * e 1 * e 2 := by
  have hd := congrArg Matrix.det (mul_colMat_eq hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three] at hd
  have hP := ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_colMat hb)).ne_zero
  exact mul_left_cancel₀ hP (by rw [← hd]; ring)

theorem eig_mulVec {R : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K}
    (hyR : ∀ r ∈ R, y⁻¹ * r * y ∈ R) {w : Fin 3 → K}
    (hw : ∀ r ∈ R, ∃ c : K, (r : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w) :
    ∀ r ∈ R, ∃ c : K, (r : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
      c • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  intro r hr
  obtain ⟨c, hc⟩ := hw _ (hyR r hr)
  refine ⟨c, ?_⟩
  have h : ((r * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((y * (y⁻¹ * r * y) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    congr 1
    group
  rw [Units.val_mul, Units.val_mul] at h
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]

theorem conj_eig {y g : GL (Fin 3) K} {ℓ : K} (hℓ : ℓ ≠ 0)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) {v e : Fin 3 → K}
    (hg : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i = e i • yFrame y v i) :
    ∀ i, ((y * g * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i =
      ![e 2, e 0, e 1] i • yFrame y v i := by
  set Y := (y : Matrix (Fin 3) (Fin 3) K) with hYdef
  set G := (g : Matrix (Fin 3) (Fin 3) K) with hGdef
  set G' := ((y * g * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hG'def
  have hc : G' * Y = Y * G := by
    rw [hG'def, hYdef, hGdef, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  have key : ∀ w, G' *ᵥ (Y *ᵥ w) = Y *ᵥ (G *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  have h2 : Y *ᵥ (Y *ᵥ v) = (Y ^ 2) *ᵥ v := by rw [Matrix.mulVec_mulVec, sq]
  have h3 : Y *ᵥ ((Y ^ 2) *ᵥ v) = ℓ • v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hy, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [yFrame_eq] at hg ⊢
  have e0 : G *ᵥ v = e 0 • v := hg 0
  have e1 : G *ᵥ (Y *ᵥ v) = e 1 • (Y *ᵥ v) := hg 1
  have e2 : G *ᵥ ((Y ^ 2) *ᵥ v) = e 2 • ((Y ^ 2) *ᵥ v) := hg 2
  intro i
  fin_cases i
  · show G' *ᵥ v = e 2 • v
    have h : ℓ • (G' *ᵥ v) = ℓ • (e 2 • v) := by
      calc ℓ • (G' *ᵥ v) = G' *ᵥ (Y *ᵥ ((Y ^ 2) *ᵥ v)) := by rw [h3, Matrix.mulVec_smul]
        _ = e 2 • (Y *ᵥ ((Y ^ 2) *ᵥ v)) := by rw [key, e2, Matrix.mulVec_smul]
        _ = ℓ • (e 2 • v) := by rw [h3, smul_comm]
    exact smul_right_injective _ hℓ h
  · show G' *ᵥ (Y *ᵥ v) = e 0 • (Y *ᵥ v)
    rw [key, e0, Matrix.mulVec_smul]
  · show G' *ᵥ ((Y ^ 2) *ᵥ v) = e 1 • ((Y ^ 2) *ᵥ v)
    rw [← h2, key, e1, Matrix.mulVec_smul]

@[expose] def sgnAt (k i : Fin 3) : K := if i = k then 1 else -1

theorem sgnAt_rot (k : Fin 3) :
    ![sgnAt k 2, sgnAt k 0, sgnAt k 1] = (sgnAt (k + 1) : Fin 3 → K) := by
  funext i
  fin_cases k <;> fin_cases i <;> simp [sgnAt]

theorem eig_cases (h2 : (2 : K) ≠ 0) {e : Fin 3 → K} (he : ∀ i, e i ^ 2 = 1)
    (hdet : e 0 * e 1 * e 2 = 1) : e = (fun _ => 1) ∨ ∃ k, e = sgnAt k := by
  have hn : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have he3 : e = ![e 0, e 1, e 2] := by
    funext i
    fin_cases i <;> rfl
  rw [he3]
  rcases sq_eq_one_iff.1 (he 0) with h0 | h0 <;> rcases sq_eq_one_iff.1 (he 1) with h1 | h1 <;>
    rcases sq_eq_one_iff.1 (he 2) with h2' | h2' <;> rw [h0, h1, h2'] at hdet ⊢
  · exact Or.inl (by funext i; fin_cases i <;> rfl)
  · exact (hn (by linear_combination hdet)).elim
  · exact (hn (by linear_combination hdet)).elim
  · exact Or.inr ⟨0, by funext i; fin_cases i <;> simp [sgnAt]⟩
  · exact (hn (by linear_combination hdet)).elim
  · exact Or.inr ⟨1, by funext i; fin_cases i <;> simp [sgnAt]⟩
  · exact Or.inr ⟨2, by funext i; fin_cases i <;> simp [sgnAt]⟩
  · exact (hn (by linear_combination hdet)).elim

theorem herm_mulVec {p f : ℕ} (h : UnitaryFieldData p f K) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : (A.map h.bar)ᵀ * A = 1) (u w : Fin 3 → K) :
    ∑ k, (A *ᵥ u) k ^ p ^ f * (A *ᵥ w) k = ∑ k, u k ^ p ^ f * w k := by
  have hmap : (fun k => (A *ᵥ u) k ^ p ^ f) = A.map h.bar *ᵥ fun k => u k ^ p ^ f := by
    funext k
    exact RingHom.map_mulVec h.bar A u k
  change (fun k => (A *ᵥ u) k ^ p ^ f) ⬝ᵥ (A *ᵥ w) = (fun k => u k ^ p ^ f) ⬝ᵥ w
  rw [hmap, ← Matrix.vecMul_transpose (A.map h.bar), ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292T
