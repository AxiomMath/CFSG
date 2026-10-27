module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix

public section

namespace CFSG.LinearAlgebra

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ComponentClassification.CatalogueBHermitian

noncomputable section

universe u v

section HermitianForm

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {sigma : K ≃+* K} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K)

theorem exists_orthogonal_basis [Finite K] [FiniteDimensional K V]
    (hsym : h.IsSymm) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V)
      (d : Fin (Module.finrank K V) → K),
      (∀ i, d i = 0 ∨ d i = 1) ∧
      ∀ i j, h (b i) (b j) = if i = j then d i else 0 := by
  classical
  suffices ∀ d : ℕ, Module.finrank K V = d →
      ∃ (b : Module.Basis (Fin d) K V) (c : Fin d → K),
        (∀ i, c i = 0 ∨ c i = 1) ∧
        ∀ i j, h (b i) (b j) = if i = j then c i else 0 by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero =>
      refine ⟨basisOfFinrankZero hd, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ d ih =>
      by_cases hzero : h = 0
      · refine ⟨Module.finBasisOfFinrankEq K V hd, fun _ => 0, ?_, ?_⟩
        · intro i
          exact Or.inl rfl
        · intro i j
          rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]
          simp
      · have hex : ∃ x : V, h x x ≠ 0 := by
          by_contra hall
          apply hzero
          ext x y
          exact polarization h hne ⊤ (fun z _ => by
            by_contra hz
            exact hall ⟨z, hz⟩) trivial trivial
        obtain ⟨x, hx⟩ := hex
        obtain ⟨c, hc⟩ := exists_smul_unit h hsym hsigma hne hx
        let e : V := c • x
        have he : h e e = 1 := hc
        let W : Submodule K V := LinearMap.ker (h e)
        let hW : W →ₛₗ[sigma.toRingHom] W →ₗ[K] K := h.domRestrict₁₂ W W
        have hdim : Module.finrank K W = d := by
          have hc := complement_finrank h he
          change Module.finrank K W + 1 = Module.finrank K V at hc
          omega
        obtain ⟨bW, cW, hcW, hbW⟩ :=
          ih hW (complement_isSymm h hsym e) hdim
        change ∀ i j, h (bW i : V) (bW j : V) = if i = j then cW i else 0 at hbW
        have hli : ∀ (c : K), ∀ x ∈ W, c • e + x = 0 → c = 0 :=
          coefficient_zero h he
        have hsp : ∀ x : V, ∃ c : K, x + c • e ∈ W := by
          intro x
          refine ⟨-h e x, ?_⟩
          simpa only [W, orthogonalProjection_apply, neg_smul, sub_eq_add_neg] using
            orthogonalProjection_mem_ker h he x
        let b : Module.Basis (Fin (d + 1)) K V :=
          Module.Basis.mkFinCons e bW hli hsp
        refine ⟨b, Fin.cons 1 cW, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · exact Or.inr (by simp)
          · exact hcW i
        · have hb : (b : Fin (d + 1) → V) =
              Fin.cons e (fun i => (bW i : V)) :=
            Module.Basis.coe_mkFinCons e bW hli hsp
          intro i j
          rw [hb]
          refine Fin.cases ?_ (fun i => ?_) i <;>
            refine Fin.cases ?_ (fun j => ?_) j
          · simp only [Fin.cons_zero]
            simpa using he
          · have hxj : h e (bW j : V) = 0 := (bW j).property
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hxj, if_neg (fun h => Fin.succ_ne_zero j h.symm)]
          · have hxi : h (bW i : V) e = 0 :=
              hsym.isRefl e (bW i) (bW i).property
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hxi, if_neg (Fin.succ_ne_zero i)]
          · simp only [Fin.cons_succ, Fin.succ_inj]
            exact hbW i j

end HermitianForm

section MatrixCongruence

variable {K : Type u} [Field K] (sigma : K ≃+* K) {n : ℕ}

theorem exists_diagonal_congr_of_hermitian [Finite K]
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (A : Matrix (Fin n) (Fin n) K) (hA : conjTr sigma A = A) :
    ∃ (P : GL (Fin n) K) (d : Fin n → K),
      (∀ i, d i = 0 ∨ d i = 1) ∧
      conjTr sigma P.val * A * P.val = Matrix.diagonal d := by
  classical
  have hmain := exists_orthogonal_basis (matrixForm sigma A)
    (matrixForm_isSymm sigma hsigma A hA) hsigma hne
  rw [Module.finrank_fin_fun K] at hmain
  obtain ⟨b, d, hd, hb⟩ := hmain
  let b0 := Pi.basisFun K (Fin n)
  let P : GL (Fin n) K :=
    { val := b0.toMatrix b
      inv := b.toMatrix b0
      val_inv := b0.toMatrix_mul_toMatrix_flip b
      inv_val := b.toMatrix_mul_toMatrix_flip b0 }
  have hcol (i : Fin n) : P.val *ᵥ Pi.single i 1 = b i := by
    ext j
    simp [P, b0, Module.Basis.toMatrix_apply]
  refine ⟨P, d, hd, ?_⟩
  ext i j
  have hij := hb i j
  rw [← hcol i, ← hcol j, matrixForm_mulVec, herm_single_left,
    map_one, one_mul, mulVec_single_one] at hij
  rwa [Matrix.diagonal_apply]

end MatrixCongruence

end

end CFSG.LinearAlgebra
