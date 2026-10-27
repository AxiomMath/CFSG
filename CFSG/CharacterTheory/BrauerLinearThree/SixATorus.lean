module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral

public section

namespace CFSG.BrauerLinearThree

open Polynomial Matrix CFSG.DesarguesianPlanes

variable {F : Type} [Field F]

omit [Field F] in
theorem eq_add_smul_of_commute [Field F] {A B : Matrix (Fin 2) (Fin 2) F} (hB : B 1 0 ≠ 0)
    (h : A * B = B * A) :
    A = (A 0 0 - A 1 0 / B 1 0 * B 0 0) • (1 : Matrix (Fin 2) (Fin 2) F) +
      (A 1 0 / B 1 0) • B := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · linear_combination h00
  · linear_combination h10

variable [Finite F]

structure IsNonsplitTorus {K : Type} [Field K] (μ : Kˣ →* GL (Fin 2) F) : Prop where
  injective : Function.Injective μ
  card : Nat.card Kˣ = Nat.card F ^ 2 - 1
  neg_one : μ (-1) = -1
  frob : ∀ x : Kˣ, diagGL 1 (-1) * μ x * (diagGL 1 (-1))⁻¹ = μ (x ^ Nat.card F)
  scalar_mem : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ μ.range
  commutant : ∀ x : Kˣ, (∀ c : Fˣ, μ x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c) →
    ∀ A : GL (Fin 2) F, A * μ x = μ x * A → A ∈ μ.range
  fusion : ∀ x y : Kˣ, ∀ N : GL (Fin 2) F, N * μ x * N⁻¹ = μ y → y = x ∨ y = x ^ Nat.card F

theorem exists_nonsplit_torus (hq : Nat.card F % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (μ : Kˣ →* GL (Fin 2) F), IsNonsplitTorus μ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hfdef⟩ : ∃ f : F[X], f = X ^ 2 - C (-1 : F) := ⟨_, rfl⟩
  have : Fact (Irreducible f) := ⟨hfdef ▸ irreducible_X_sq_sub_C_neg_one hq⟩
  let K := AdjoinRoot f
  have hf : f ≠ 0 := hfdef ▸ X_pow_sub_C_ne_zero two_pos _
  have hdeg : f.natDegree = 2 := hfdef ▸ natDegree_X_pow_sub_C
  let b : Module.Basis (Fin 2) F K := (AdjoinRoot.powerBasis hf).basis.reindex (finCongr hdeg)
  have hb : ∀ i : Fin 2, b i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rfl
  have : Finite K := CFSG.Wreathed.CentralSL2.finite_of_basis F K b
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Nat.card K = Nat.card F ^ 2 := CFSG.Wreathed.CentralSL2.card_extension F K b
  have hcard : Nat.card Kˣ = Nat.card F ^ 2 - 1 := by rw [Nat.card_units, hcardK]
  set i := AdjoinRoot.root f with hi
  have hi2 : i ^ 2 = -1 := by
    have h : AdjoinRoot.mk f (X ^ 2 - C (-1)) = 0 := by rw [← hfdef]; exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_neg, map_one, ← hi] at h
    linear_combination h
  have hiq : i ^ Nat.card F = -i := by
    have h4 : Nat.card F = 2 * (2 * (Nat.card F / 4) + 1) + 1 := by omega
    rw [h4, pow_succ i, pow_mul i, hi2, (odd_two_mul_add_one _).neg_one_pow, neg_one_mul]
  have hS : CFSG.Wreathed.CentralSL2.frobMatrix F K b =
      ((diagGL 1 (-1) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have h0 : FiniteField.frobeniusAlgHom F K (b 0) = b 0 := by
      rw [CFSG.Wreathed.CentralSL2.frobeniusAlgHom_apply', hb]
      simp
    have h1 : FiniteField.frobeniusAlgHom F K (b 1) = -b 1 := by
      rw [CFSG.Wreathed.CentralSL2.frobeniusAlgHom_apply', hb]
      simpa using hiq
    ext r s
    rw [CFSG.Wreathed.CentralSL2.frobMatrix, LinearMap.toMatrix_apply]
    fin_cases s
    · change (b.repr (FiniteField.frobeniusAlgHom F K (b 0))) r = _
      rw [h0, Module.Basis.repr_self]
      fin_cases r <;> simp [diagGL]
    · change (b.repr (FiniteField.frobeniusAlgHom F K (b 1))) r = _
      rw [h1, map_neg, Module.Basis.repr_self]
      fin_cases r <;> simp [diagGL]
  set μ := CFSG.Wreathed.CentralSL2.mulGL F K b with hμ
  have hμval : ∀ x : Kˣ, ((μ x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix b (x : K) := fun x => rfl
  have hμinj : Function.Injective μ := by
    intro x y hxy
    have h := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hxy
    simp only [hμval] at h
    exact Units.ext (CFSG.Wreathed.CentralSL2.mulMatrix_injective F K b h)
  have hscal : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c =
      μ (Units.map (algebraMap F K).toMonoidHom c) := by
    intro c
    apply Units.ext
    rw [hμval]
    change _ = Algebra.leftMulMatrix b (algebraMap F K (c : F))
    rw [AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext r s
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hb0 : b 0 = 1 := by rw [hb]; simp
  have hcoord : ∀ x : Kˣ, (∀ c : Fˣ, μ x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c) →
      (Algebra.leftMulMatrix b (x : K)) 1 0 ≠ 0 := by
    intro x hx h0
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one] at h0
    have hx' : (x : K) = algebraMap F K (b.repr x 0) := by
      have := b.sum_repr (x : K)
      rw [Fin.sum_univ_two, h0, zero_smul, add_zero, hb0, Algebra.smul_def, mul_one] at this
      exact this.symm
    have hne : b.repr x 0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hx'
      exact x.ne_zero hx'
    apply hx (Units.mk0 _ hne)
    rw [hscal]
    congr 1
    apply Units.ext
    exact hx'
  refine ⟨K, inferInstance, inferInstance, μ, hμinj, hcard, ?_, ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    rw [hμval, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, map_neg, map_one]
  ·
    intro x
    apply Units.ext
    rw [diagGL_one_neg_one_inv, Units.val_mul, Units.val_mul, ← hS, hμval, hμval,
      CFSG.Wreathed.CentralSL2.frobMatrix_mul_mulMatrix, Matrix.mul_assoc,
      CFSG.Wreathed.CentralSL2.frobMatrix_mul_self, Matrix.mul_one, Units.val_pow_eq_pow_val]
  · intro c
    exact ⟨_, (hscal c).symm⟩
  ·
    intro x hx A hA
    have hA' : (A : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix b (x : K) =
        Algebra.leftMulMatrix b (x : K) * A := by
      have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) hA
      simpa only [Units.val_mul, hμval] using this
    have heq := eq_add_smul_of_commute (hcoord x hx) hA'
    set α := (A : Matrix (Fin 2) (Fin 2) F) 0 0 - (A : Matrix (Fin 2) (Fin 2) F) 1 0 /
      (Algebra.leftMulMatrix b (x : K)) 1 0 * (Algebra.leftMulMatrix b (x : K)) 0 0
    set β := (A : Matrix (Fin 2) (Fin 2) F) 1 0 / (Algebra.leftMulMatrix b (x : K)) 1 0
    have hy : (A : Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b (algebraMap F K α + β • x) := by
      rw [heq, map_add, AlgHom.commutes, map_smul, Matrix.algebraMap_eq_diagonal,
        Matrix.smul_one_eq_diagonal]
      rfl
    have hy0 : algebraMap F K α + β • (x : K) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hy
      exact A.ne_zero hy
    refine ⟨Units.mk0 _ hy0, ?_⟩
    apply Units.ext
    rw [hμval]
    exact hy.symm
  ·
    intro x y N hN
    have hNval : (N : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix b (x : K) *
        ((N⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          Algebra.leftMulMatrix b (y : K) := by
      have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) hN
      simpa only [Units.val_mul, hμval] using this
    have htr : Matrix.trace (Algebra.leftMulMatrix b (y : K)) =
        Matrix.trace (Algebra.leftMulMatrix b (x : K)) := by
      rw [← hNval, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have hdet :
        (Algebra.leftMulMatrix b (y : K)).det = (Algebra.leftMulMatrix b (x : K)).det := by
      rw [← hNval, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
    have htrK : ∀ t : K, algebraMap F K (Matrix.trace (Algebra.leftMulMatrix b t)) =
        t + t ^ Nat.card F := by
      intro t
      rw [← Algebra.trace_eq_matrix_trace, FiniteField.algebraMap_trace_eq_sum_pow,
        CFSG.Wreathed.CentralSL2.finrank_eq_two F K b, Finset.sum_range_succ,
        Finset.sum_range_one, pow_zero, pow_one, pow_one]
    have hdetK : ∀ t : K, algebraMap F K (Algebra.leftMulMatrix b t).det =
        t * t ^ Nat.card F := CFSG.Wreathed.CentralSL2.algebraMap_det_mulMatrix F K b
    have h1 : (y : K) + (y : K) ^ Nat.card F = (x : K) + (x : K) ^ Nat.card F := by
      rw [← htrK, ← htrK, htr]
    have h2 : (y : K) * (y : K) ^ Nat.card F = (x : K) * (x : K) ^ Nat.card F := by
      rw [← hdetK, ← hdetK, hdet]
    have hprod : ((y : K) - x) * ((y : K) - (x : K) ^ Nat.card F) = 0 := by
      linear_combination (y : K) * h1 - h2
    rcases mul_eq_zero.mp hprod with h | h
    · left
      exact Units.ext (sub_eq_zero.mp h)
    · right
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact sub_eq_zero.mp h

end CFSG.BrauerLinearThree
