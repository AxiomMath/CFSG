module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Field
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

@[expose] def Mt (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

theorem Mt_quad (K : Type) [Field K] : Mt K * Mt K + Mt K + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mt, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem aeval_quad_Mt (K : Type) [Field K] :
    Polynomial.aeval (Mt K) (KA7.quad K) = 0 := by
  have hq : Polynomial.aeval (Mt K) (KA7.quad K) = Mt K * Mt K + Mt K + 1 := by
    simp [KA7.quad, sq]
  rw [hq, Mt_quad]

theorem aeval_mem_span (K : Type) [Field K] :
    ∀ a ∈ Ideal.span {KA7.quad K}, Polynomial.aeval (Mt K) a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, aeval_quad_Mt, mul_zero]

@[expose] noncomputable def phi (K : Type) [Field K] :
    AdjoinRoot (KA7.quad K) →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  Ideal.Quotient.liftₐ (Ideal.span {KA7.quad K}) (Polynomial.aeval (Mt K)) (aeval_mem_span K)

theorem phi_root (K : Type) [Field K] :
    phi K (AdjoinRoot.root (KA7.quad K)) = Mt K := by
  have h := Ideal.Quotient.liftₐ_apply (Ideal.span {KA7.quad K}) (Polynomial.aeval (Mt K))
    (aeval_mem_span K) (Polynomial.X : Polynomial K)
  have h' : (Polynomial.aeval (Mt K)) (Polynomial.X : Polynomial K) = Mt K :=
    Polynomial.aeval_X _
  exact h.trans h'

@[expose] def eps : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

@[expose] noncomputable def ThetaP {K : Type} [Field K]
    (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K :=
  Matrix.of fun p q => phi K (X p.1 q.1) p.2 q.2

@[expose] noncomputable def Theta {K : Type} [Field K]
    (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) :
    Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex eps eps (ThetaP X)

theorem ThetaP_mul {K : Type} [Field K]
    (X Y : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) :
    ThetaP (X * Y) = ThetaP X * ThetaP Y := by
  ext p q
  simp [ThetaP, Matrix.mul_apply, Fintype.sum_prod_type, map_sum, map_mul, Matrix.sum_apply]

theorem Theta_mul {K : Type} [Field K]
    (X Y : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) :
    Theta (X * Y) = Theta X * Theta Y := by
  have h : ∀ Z : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)),
      Theta Z = Matrix.reindexAlgEquiv K K eps (ThetaP Z) := fun Z => rfl
  rw [h, h, h, ← map_mul, ThetaP_mul]

theorem ThetaP_root (K : Type) [Field K] (p q : Fin 2 × Fin 2) :
    ThetaP (AdjoinRoot.root (KA7.quad K) • (1 : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))))
      p q = if p.1 = q.1 then Mt K p.2 q.2 else 0 := by
  simp only [ThetaP, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · simp [h, phi_root]
  · simp [h]

theorem Theta_root (K : Type) [Field K] :
    Theta (AdjoinRoot.root (KA7.quad K) • (1 : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))))
      = D4 K := by
  ext a b
  simp only [Theta, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [ThetaP_root]
  fin_cases a <;> fin_cases b <;> rfl

theorem phi_injective (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    Function.Injective (phi K) :=
  (phi K).toRingHom.injective

theorem Theta_injective (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    Function.Injective (Theta (K := K)) := by
  intro X Y h
  have h1 : ThetaP X = ThetaP Y := (Matrix.reindex eps eps).injective h
  ext i j
  apply phi_injective K
  ext k l
  have := congrFun (congrFun h1 (i, k)) (j, l)
  simpa [ThetaP] using this

theorem block_commute (K : Type) [Field K] (B : Matrix (Fin 2) (Fin 2) K)
    (hB : B * Mt K = Mt K * B) :
    B = (B 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) - (B 0 1) • Mt K := by
  have h00 := congrFun (congrFun hB 0) 0
  have h01 := congrFun (congrFun hB 0) 1
  have h11 := congrFun (congrFun hB 1) 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mt, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11 ⊢ <;>
    first
    | rfl
    | linear_combination h00
    | linear_combination -h00
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h11
    | linear_combination -h11

theorem phi_block (K : Type) [Field K] (B : Matrix (Fin 2) (Fin 2) K)
    (hB : B * Mt K = Mt K * B) :
    phi K ((B 0 0) • (1 : AdjoinRoot (KA7.quad K)) - (B 0 1) • AdjoinRoot.root (KA7.quad K)) = B := by
  rw [map_sub, map_smul, map_smul, map_one, phi_root]
  exact (block_commute K B hB).symm

theorem commutant_Theta (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (C : Matrix (Fin 4) (Fin 4) K) (hC : C * D4 K = D4 K * C) :
    ∃ Y : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)), Theta Y = C := by
  let re : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K ≃ₐ[K] Matrix (Fin 4) (Fin 4) K :=
    Matrix.reindexAlgEquiv K K eps
  obtain ⟨C', rfl⟩ : ∃ C' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K, C = re C' :=
    ⟨re.symm C, (re.apply_symm_apply C).symm⟩
  have hD : D4 K = re (ThetaP (AdjoinRoot.root (KA7.quad K) •
      (1 : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))))) := by
    rw [← Theta_root K]
    rfl
  rw [hD, ← map_mul, ← map_mul] at hC
  have hC2 := re.injective hC
  have hB : ∀ i j : Fin 2, (Matrix.of fun k l : Fin 2 => C' (i, k) (j, l)) * Mt K =
      Mt K * (Matrix.of fun k l : Fin 2 => C' (i, k) (j, l)) := by
    intro i j
    ext k l
    have h := congrFun (congrFun hC2 (i, k)) (j, l)
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, ThetaP_root, Mt] at h ⊢ <;>
      first
      | linear_combination h
      | linear_combination -h
      | ring
  let Y : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)) := Matrix.of fun i j =>
    (Matrix.of fun k l : Fin 2 => C' (i, k) (j, l)) 0 0 • (1 : AdjoinRoot (KA7.quad K)) -
      (Matrix.of fun k l : Fin 2 => C' (i, k) (j, l)) 0 1 • AdjoinRoot.root (KA7.quad K)
  have hY : ThetaP Y = C' := by
    ext p q
    have h := congrFun (congrFun (phi_block K _ (hB p.1 q.1)) p.2) q.2
    simp only [Matrix.of_apply] at h
    simp only [ThetaP, Matrix.of_apply, Y]
    exact h
  refine ⟨Y, ?_⟩
  show re (ThetaP Y) = re C'
  rw [hY]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
