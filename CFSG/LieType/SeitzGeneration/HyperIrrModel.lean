module

public import CFSG.LieType.SeitzGeneration.HyperIrrIndep

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Module

variable {F : Type*} [Field F]

@[expose] def shiftMat (p : ℕ) (F : Type*) [Field F] : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i k => if (i : ℕ) = ((k : ℕ) + 1) % p then 1 else 0

@[expose] def charMat (p : ℕ) (ε : F) : Matrix (Fin p) (Fin p) F :=
  Matrix.diagonal fun i => ε ^ (i : ℕ)

@[expose] def compMat (p : ℕ) (c : F) : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i k =>
    if (i : ℕ) = ((k : ℕ) + 1) % p then (if (k : ℕ) + 1 = p then c else 1) else 0

@[expose] def shiftIdx {p : ℕ} (hp : 0 < p) (i : Fin p) : Fin p :=
  ⟨((i : ℕ) + 1) % p, Nat.mod_lt _ hp⟩

theorem mulVec_single_apply {m : ℕ} (X : Matrix (Fin m) (Fin m) F) (a k : Fin m) :
    X.mulVec (Pi.single k 1) a = X a k := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem mul_basisUnit_eq {m : ℕ} (b : Basis (Fin m) F (Fin m → F))
    {M N : Matrix (Fin m) (Fin m) F} (ι : Fin m → F) (φ : Fin m → Fin m)
    (hM : ∀ k, M.mulVec (b k) = ι k • b (φ k))
    (hN : ∀ a k, N a k = if a = φ k then ι k else 0) :
    M * (basisUnit b : Matrix (Fin m) (Fin m) F) =
      (basisUnit b : Matrix (Fin m) (Fin m) F) * N := by
  ext a k
  rw [← mulVec_single_apply (M * (basisUnit b : Matrix (Fin m) (Fin m) F)) a k,
    ← mulVec_single_apply ((basisUnit b : Matrix (Fin m) (Fin m) F) * N) a k,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisUnit_mulVec_single, one_smul, hM k]
  have hNv : N.mulVec (Pi.single k 1) = ι k • (Pi.single (φ k) 1 : Fin m → F) := by
    ext a'
    rw [mulVec_single_apply, hN a' k]
    by_cases ha : a' = φ k
    · simp [ha]
    · simp [ha]
  rw [hNv, Matrix.mulVec_smul, basisUnit_mulVec_single, one_smul]

theorem mul_basisUnit_eq_kr {p : ℕ} (b : Basis (Fin (p * p)) F (Fin (p * p) → F))
    {M : Matrix (Fin (p * p)) (Fin (p * p)) F} {N₁ N₂ : Matrix (Fin p) (Fin p) F}
    (ι : Fin p × Fin p → F) (φ : Fin p × Fin p → Fin p × Fin p)
    (hM : ∀ ij, M.mulVec (b (finProdFinEquiv ij)) = ι ij • b (finProdFinEquiv (φ ij)))
    (hN : ∀ i' j' i j, N₁ i' i * N₂ j' j = if (i', j') = φ (i, j) then ι (i, j) else 0) :
    M * (basisUnit b : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (basisUnit b : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr N₁ N₂ := by
  refine mul_basisUnit_eq b (fun k => ι (finProdFinEquiv.symm k))
    (fun k => finProdFinEquiv (φ (finProdFinEquiv.symm k))) ?_ ?_
  · intro k
    obtain ⟨ij, rfl⟩ := finProdFinEquiv.surjective k
    simpa using hM ij
  · intro a k
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [kr_apply, hN]
    simp

theorem exists_kron_model {p : ℕ} {ζ c : F} {A B C : Matrix (Fin (p * p)) (Fin (p * p)) F}
    {u₀ : Fin (p * p) → F} (h : KronData p ζ c A B C u₀) :
    ∃ P : GL (Fin (p * p)) F,
      A * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr (shiftMat p F) 1 ∧
      B * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr (charMat p ζ⁻¹) 1 ∧
      C * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr 1 (compMat p c) := by
  have hp := h.prime.pos
  let b0 : Basis (Fin p × Fin p) F (Fin (p * p) → F) :=
    Basis.mk h.linearIndependent_kvec (h.span_kvec hp)
  let bb : Basis (Fin (p * p)) F (Fin (p * p) → F) := b0.reindex finProdFinEquiv
  have hbb : ∀ ij, bb (finProdFinEquiv ij) = kvec A C u₀ ij := fun ij => by
    simp [bb, b0, Basis.reindex_apply]
  refine ⟨basisUnit bb, ?_, ?_, ?_⟩
  · refine mul_basisUnit_eq_kr bb (fun _ => 1) (fun ij => (shiftIdx hp ij.1, ij.2)) ?_ ?_
    · rintro ⟨i, j⟩
      rw [hbb, hbb, one_smul]
      exact h.kvec_A hp i j
    · intro i' j' i j
      simp only [shiftMat, Matrix.of_apply, Matrix.one_apply, shiftIdx, Prod.mk.injEq,
        Fin.ext_iff]
      by_cases h1 : (i' : ℕ) = ((i : ℕ) + 1) % p <;> by_cases h2 : (j' : ℕ) = (j : ℕ) <;>
        simp [h1, h2]
  · refine mul_basisUnit_eq_kr bb (fun ij => ζ⁻¹ ^ (ij.1 : ℕ)) (fun ij => ij) ?_ ?_
    · rintro ⟨i, j⟩
      rw [hbb]
      exact h.kvec_B (i, j)
    · intro i' j' i j
      simp only [charMat, Matrix.diagonal_apply, Matrix.one_apply, Prod.mk.injEq]
      by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> simp [h1, h2]
  · refine mul_basisUnit_eq_kr bb (fun ij => if (ij.2 : ℕ) + 1 = p then c else 1)
      (fun ij => (ij.1, shiftIdx hp ij.2)) ?_ ?_
    · rintro ⟨i, j⟩
      rw [hbb, hbb]
      exact h.kvec_C hp i j
    · intro i' j' i j
      simp only [compMat, Matrix.of_apply, Matrix.one_apply, shiftIdx, Prod.mk.injEq,
        Fin.ext_iff]
      by_cases h1 : (i' : ℕ) = (i : ℕ) <;> by_cases h2 : (j' : ℕ) = ((j : ℕ) + 1) % p <;>
        simp [h1, h2]

end CFSG.LieType.SeitzGeneration
