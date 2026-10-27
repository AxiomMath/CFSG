module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def IsRat (k : Subfield K) (v : Fin n → K) : Prop := ∀ i, v i ∈ k

theorem coe_inv_eq_conjTr (g : SUid σ n) :
    (((g⁻¹ : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 : conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := g.2.2
  have h2 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((g⁻¹ : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]
    have : ((g : GL (Fin n) K) * ((g⁻¹ : SUid σ n) : GL (Fin n) K)) = 1 := by
      have := congrArg Subtype.val (mul_inv_cancel g)
      exact this
    rw [this, Units.val_one]
  symm
  calc conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((g⁻¹ : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [h2, Matrix.mul_one]
    _ = (((g⁻¹ : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

@[expose] def ratSU (σ : K ≃+* K) (k : Subfield K) (hk : ∀ x ∈ k, σ x ∈ k) (n : ℕ) :
    Subgroup (SUid σ n) where
  carrier := {g | ∀ i j, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ k}
  mul_mem' {a b} ha hb i j := by
    show (((a : GL (Fin n) K) * (b : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      i j ∈ k
    rw [Units.val_mul, Matrix.mul_apply]
    exact k.sum_mem fun l _ => k.mul_mem (ha i l) (hb l j)
  one_mem' i j := by
    show (((1 : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ k
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact k.one_mem
    · exact k.zero_mem
  inv_mem' {g} hg i j := by
    show (((g⁻¹ : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ k
    rw [coe_inv_eq_conjTr]
    exact hk _ (hg j i)

theorem conjTr_conjTr (hσ : ∀ c, σ (σ c) = c) (M : Matrix (Fin n) (Fin n) K) :
    conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσ]

theorem coe_inv_eq_conjTr_of_unitary (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      conjTr σ (A : Matrix (Fin n) (Fin n) K) := by
  have h2 : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  symm
  calc conjTr σ (A : Matrix (Fin n) (Fin n) K)
      = conjTr σ (A : Matrix (Fin n) (Fin n) K) *
        ((A : Matrix (Fin n) (Fin n) K) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [h2, Matrix.mul_one]
    _ = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← Matrix.mul_assoc, hA, Matrix.one_mul]

theorem conj_mem_SUid (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (g : SUid σ n) : A * (g : GL (Fin n) K) * A⁻¹ ∈ SUid σ n := by
  have hAi := coe_inv_eq_conjTr_of_unitary A hA
  have hAA : (A : Matrix (Fin n) (Fin n) K) * conjTr σ (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mem_SUid, Units.val_mul, Units.val_mul, hAi]
  refine ⟨?_, ?_⟩
  · have hdet : (A : Matrix (Fin n) (Fin n) K).det *
        (conjTr σ (A : Matrix (Fin n) (Fin n) K)).det = 1 := by
      rw [← det_mul, hAA, det_one]
    rw [det_mul, det_mul, g.2.1, mul_one, hdet]
  · rw [conjTr_mul, conjTr_mul, conjTr_conjTr hσ]
    have hg := g.2.2
    have e1 : (A : Matrix (Fin n) (Fin n) K) *
        (conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          conjTr σ (A : Matrix (Fin n) (Fin n) K)) *
        ((A : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          conjTr σ (A : Matrix (Fin n) (Fin n) K)) =
        (A : Matrix (Fin n) (Fin n) K) *
          (conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          conjTr σ (A : Matrix (Fin n) (Fin n) K) := by
      simp only [Matrix.mul_assoc]
    rw [e1, hA, Matrix.mul_one, hg, Matrix.mul_one, hAA]

theorem herm_mulVec_unitary (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (x y : Fin n → K) :
    herm σ ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      herm σ x y := by
  rw [herm_mulVec, hA, one_mulVec]

@[expose] def suConj (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1) :
    SUid σ n →* SUid σ n where
  toFun g := ⟨A * (g : GL (Fin n) K) * A⁻¹, conj_mem_SUid hσ A hA g⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp [mul_assoc]

theorem coe_suConj (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (g : SUid σ n) :
    ((suConj hσ A hA g : SUid σ n) : GL (Fin n) K) = A * (g : GL (Fin n) K) * A⁻¹ :=
  rfl

theorem suConj_smul_of_tv (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    {t : SUid σ n} {a : Fin n → K} {c : K} (h : ∀ v, t • v = v + (c * herm σ a v) • a)
    (v : Fin n → K) :
    (suConj hσ A hA t) • v =
      v + (c * herm σ ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) v) •
        ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) := by
  have hAi := coe_inv_eq_conjTr_of_unitary A hA
  have hAA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hv : (A : Matrix (Fin n) (Fin n) K) *ᵥ
      (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
    rw [mulVec_mulVec, hAA, one_mulVec]
  have e1 : (suConj hσ A hA t) • v = (A : Matrix (Fin n) (Fin n) K) *ᵥ
      (t • (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) := by
    show ((A * (t : GL (Fin n) K) * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = _
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  rw [e1, h, mulVec_add, mulVec_smul, hv]
  congr 2
  rw [← herm_mulVec_unitary A hA a, hv]

end CFSG.LieType.SeitzGeneration.SUPair
