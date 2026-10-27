module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.CubicFrame

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix

variable {K : Type} [Field K] {n : ℕ}

theorem exists_dotProduct_eq {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → K)
    (hv : LinearIndependent K v) (t : ι → K) : ∃ ψ : Fin n → K, ∀ i, ψ ⬝ᵥ v i = t i := by
  classical
  let M : Matrix ι (Fin n) K := Matrix.of v
  have hrank : M.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card (show LinearIndependent K M.row from hv)]
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank]
    simp
  have : t ∈ LinearMap.range M.mulVecLin := by
    rw [hrange]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨ψ, fun i => ?_⟩
  have := congrFun hψ i
  simp only [Matrix.mulVecLin_apply] at this
  rw [dotProduct_comm]
  exact this

theorem aeval_mulVec_mem (B : Matrix (Fin n) (Fin n) K) (S : Submodule K (Fin n → K))
    (hS : ∀ x ∈ S, B *ᵥ x ∈ S) (q : Polynomial K) :
    ∀ x ∈ S, (Polynomial.aeval B q) *ᵥ x ∈ S := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro x hx
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact S.smul_mem _ hx
  | add p q hp hq =>
    intro x hx
    rw [map_add, Matrix.add_mulVec]
    exact S.add_mem (hp x hx) (hq x hx)
  | monomial m a ih =>
    intro x hx
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, ← Matrix.mulVec_mulVec]
    exact ih _ (hS x hx)

theorem exists_poly_inv (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    (c : Fin 3 → K) (hc : c ≠ 0) :
    ∃ b : Polynomial K, Polynomial.aeval B b *
      (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) = 1 := by
  classical
  have hirr := CFSG.HardMathSupport.Lang.Proving.irreducible_X_pow_three_sub_C hl
  set g : Polynomial K := Polynomial.C (c 2) * Polynomial.X ^ 2 + Polynomial.C (c 1) * Polynomial.X +
    Polynomial.C (c 0) with hg
  have hcoef : ∀ k, g.coeff k = if k = 0 then c 0 else if k = 1 then c 1 else if k = 2 then c 2
      else 0 := by
    intro k
    simp only [hg, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    rcases k with _ | _ | _ | k <;> simp
  have hg0 : g ≠ 0 := by
    intro h0
    apply hc
    ext i
    have := hcoef i
    rw [h0, Polynomial.coeff_zero] at this
    fin_cases i <;> simpa using this.symm
  have hdeg : g.natDegree < 3 := by
    have : g.natDegree ≤ 2 := Polynomial.natDegree_quadratic_le
    omega
  have hndvd : ¬ (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) ∣ g := fun hd => by
    have := Polynomial.natDegree_le_of_dvd hd hg0
    rw [Polynomial.natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
  have hp0 : Polynomial.aeval B (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) = 0 := by
    simp [hB3, Algebra.algebraMap_eq_smul_one]
  have hgB : Polynomial.aeval B g = c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2 := by
    simp [hg, Algebra.algebraMap_eq_smul_one]
    abel
  have h1 := congrArg (Polynomial.aeval B) hab
  rw [map_add, map_mul, map_mul, hp0, mul_zero, zero_add, map_one] at h1
  rw [hgB] at h1
  exact ⟨b, h1⟩

theorem exists_six_independent (hn : 6 ≤ n) (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ u u' : Fin n → K, LinearIndependent K
      (fun p : Fin 2 × Fin 3 => (B ^ (p.2 : ℕ)) *ᵥ (![u, u'] p.1)) := by
  classical
  have hn0 : 0 < n := by omega
  let u : Fin n → K := Pi.single ⟨0, hn0⟩ 1
  have hu : u ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn0⟩
    simp [u] at this
  let S : Submodule K (Fin n → K) := Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])
  have hSB : ∀ x ∈ S, B *ᵥ x ∈ S := by
    intro x hx
    have : S ≤ S.comap B.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show B *ᵥ _ ∈ S
      fin_cases i
      · exact Submodule.subset_span ⟨1, rfl⟩
      · refine ?_
        simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val]
        rw [Matrix.mulVec_mulVec, ← pow_two]
        exact Submodule.subset_span ⟨2, rfl⟩
      · simp only [Fin.reduceFinMk, Matrix.cons_val]
        rw [Matrix.mulVec_mulVec, ← pow_succ', pow_three_mulVec hB3]
        exact S.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩)
    exact this hx
  have hSu : u ∈ S := Submodule.subset_span ⟨0, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ S := by
    by_contra hall
    push Not at hall
    have htop : S = ⊤ := eq_top_iff.2 fun x _ => hall x
    have h1 : Module.finrank K S ≤ 3 := by
      refine (finrank_range_le_card (R := K) ![u, B *ᵥ u, (B ^ 2) *ᵥ u]).trans ?_
      simp
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  refine ⟨u, u', ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, Matrix.one_mulVec, pow_one] at hg
  have hrel : (g (0, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (0, 1) • B + g (0, 2) • B ^ 2) *ᵥ u +
      (g (1, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (1, 1) • B + g (1, 2) • B ^ 2) *ᵥ u' = 0 := by
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, add_assoc, add_left_comm, add_comm] using hg
  have hc : (fun k : Fin 3 => g (1, k)) = 0 := by
    by_contra hc0
    obtain ⟨b, hb⟩ := exists_poly_inv B hB3 hl _ hc0
    have hmem : (g (0, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (0, 1) • B + g (0, 2) • B ^ 2) *ᵥ u
        ∈ S := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      refine S.add_mem (S.add_mem (S.smul_mem _ hSu) (S.smul_mem _ ?_)) (S.smul_mem _ ?_)
      · exact Submodule.subset_span ⟨1, rfl⟩
      · exact Submodule.subset_span ⟨2, rfl⟩
    have h2 := aeval_mulVec_mem B S hSB b _ hmem
    apply hu'
    have e : u' = -(Polynomial.aeval B b *ᵥ
        ((g (0, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (0, 1) • B + g (0, 2) • B ^ 2) *ᵥ u)) := by
      have h3 : (g (1, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (1, 1) • B + g (1, 2) • B ^ 2) *ᵥ u'
          = -((g (0, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (0, 1) • B + g (0, 2) • B ^ 2) *ᵥ u) :=
        eq_neg_of_add_eq_zero_right hrel
      calc u' = (Polynomial.aeval B b *
          (g (1, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (1, 1) • B + g (1, 2) • B ^ 2)) *ᵥ u' := by
            rw [hb, Matrix.one_mulVec]
        _ = _ := by rw [← Matrix.mulVec_mulVec, h3, Matrix.mulVec_neg]
    rw [e]
    exact S.neg_mem h2
  have hc' : ∀ k : Fin 3, g (1, k) = 0 := fun k => congrFun hc k
  have hA : ∑ i : Fin 3, g (0, i) • ![u, B *ᵥ u, (B ^ 2) *ᵥ u] i = 0 := by
    rw [hc' 0, hc' 1, hc' 2] at hg
    simpa [Fin.sum_univ_three] using hg
  have hind := cyc_linearIndependent B hB3 hl hu
  rw [Fintype.linearIndependent_iff] at hind
  have ha := hind (fun k => g (0, k)) hA
  intro ⟨j, k⟩
  fin_cases j
  · exact ha k
  · exact hc' k

theorem exists_lin_frame (hn : 6 ≤ n) (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ u u' ψ ψ' : Fin n → K,
      (∀ k : ℕ, k < 3 → ψ ⬝ᵥ ((B ^ k) *ᵥ u) = 0) ∧
      (∀ k : ℕ, k < 3 → ψ' ⬝ᵥ ((B ^ k) *ᵥ u') = 0) ∧
      (∀ k : ℕ, k < 3 → ψ ⬝ᵥ ((B ^ k) *ᵥ u') = if k = 0 then 1 else 0) ∧
      (∀ k : ℕ, k < 3 → ψ' ⬝ᵥ ((B ^ k) *ᵥ u) = if k = 0 then 1 else 0) := by
  classical
  obtain ⟨u, u', hind⟩ := exists_six_independent hn B hB3 hl
  obtain ⟨ψ, hψ⟩ := exists_dotProduct_eq _ hind
    (fun p : Fin 2 × Fin 3 => if p.1 = 1 ∧ (p.2 : ℕ) = 0 then (1 : K) else 0)
  obtain ⟨ψ', hψ'⟩ := exists_dotProduct_eq _ hind
    (fun p : Fin 2 × Fin 3 => if p.1 = 0 ∧ (p.2 : ℕ) = 0 then (1 : K) else 0)
  refine ⟨u, u', ψ, ψ', ?_, ?_, ?_, ?_⟩
  · intro k hk
    have := hψ (0, ⟨k, hk⟩)
    simpa using this
  · intro k hk
    have := hψ' (1, ⟨k, hk⟩)
    simpa using this
  · intro k hk
    have := hψ (1, ⟨k, hk⟩)
    simpa using this
  · intro k hk
    have := hψ' (0, ⟨k, hk⟩)
    simpa using this

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
