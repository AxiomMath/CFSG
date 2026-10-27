module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthD

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section LeviExt

variable (s : ℕ) (m : Type) [Fintype m] [DecidableEq m] (K : Type) [Field K]

@[expose] noncomputable def leviExtUnit (g : GL (Fin s) K) : GL (Fin s ⊕ Fin s ⊕ m) K where
  val := fromBlocks (g : Matrix (Fin s) (Fin s) K) 0 0
    (fromBlocks (((g⁻¹ : GL (Fin s) K) : Matrix (Fin s) (Fin s) K)ᵀ) 0 0 (1 : Matrix m m K))
  inv := fromBlocks ((g⁻¹ : GL (Fin s) K) : Matrix (Fin s) (Fin s) K) 0 0
    (fromBlocks ((g : Matrix (Fin s) (Fin s) K)ᵀ) 0 0 (1 : Matrix m m K))
  val_inv := by
    simp only [fromBlocks_multiply, ← transpose_mul, Units.inv_mul, Units.mul_inv, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, transpose_one, Matrix.mul_one, fromBlocks_one]
  inv_val := by
    simp only [fromBlocks_multiply, ← transpose_mul, Units.inv_mul, Units.mul_inv, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, transpose_one, Matrix.mul_one, fromBlocks_one]

@[expose] noncomputable def leviExt : GL (Fin s) K →* GL (Fin s ⊕ Fin s ⊕ m) K :=
  MonoidHom.mk' (leviExtUnit s m K) fun g h => Units.ext (by
    simp only [leviExtUnit, Units.val_mul, fromBlocks_multiply, _root_.mul_inv_rev, transpose_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one])

theorem leviExt_injective : Function.Injective (leviExt s m K) := by
  intro a b h
  have h2 := congrArg
    (fun u : GL (Fin s ⊕ Fin s ⊕ m) K => (u : Matrix (Fin s ⊕ Fin s ⊕ m) (Fin s ⊕ Fin s ⊕ m) K)) h
  simp only [leviExt, MonoidHom.mk'_apply, leviExtUnit] at h2
  exact Units.ext (fromBlocks_inj.1 h2).1

variable {s m K}

theorem leviExt_mulVec (g : GL (Fin s) K) (v : Fin s ⊕ Fin s ⊕ m → K) :
    (leviExt s m K g : Matrix (Fin s ⊕ Fin s ⊕ m) (Fin s ⊕ Fin s ⊕ m) K) *ᵥ v =
      Sum.elim ((g : Matrix (Fin s) (Fin s) K) *ᵥ fun i => v (Sum.inl i))
        (Sum.elim ((((g⁻¹ : GL (Fin s) K) : Matrix (Fin s) (Fin s) K)ᵀ) *ᵥ
          fun i => v (Sum.inr (Sum.inl i))) fun k => v (Sum.inr (Sum.inr k))) := by
  have hM : ((leviExt s m K g : GL (Fin s ⊕ Fin s ⊕ m) K) :
      Matrix (Fin s ⊕ Fin s ⊕ m) (Fin s ⊕ Fin s ⊕ m) K) =
      fromBlocks (g : Matrix (Fin s) (Fin s) K) 0 0
        (fromBlocks (((g⁻¹ : GL (Fin s) K) : Matrix (Fin s) (Fin s) K)ᵀ) 0 0
          (1 : Matrix m m K)) := rfl
  rw [hM, fromBlocks_mulVec]
  ext a
  rcases a with a | a | a
  · simp [Function.comp_def]
  · simp [fromBlocks_mulVec, Function.comp_def]
  · simp [fromBlocks_mulVec, Function.comp_def]

end LeviExt

section Forms

variable {s : ℕ} {K : Type} [Field K]

theorem quadOdd_leviExt (g : GL (Fin s) K) (v : Fin s ⊕ Fin s ⊕ Unit → K) :
    StatedQuadOdd s K ((leviExt s Unit K g : Matrix _ _ K) *ᵥ v) = StatedQuadOdd s K v := by
  rw [leviExt_mulVec]
  simp only [StatedQuadOdd, Sum.elim_inl, Sum.elim_inr]
  rw [show (∑ i, ((g : Matrix (Fin s) (Fin s) K) *ᵥ fun i => v (Sum.inl i)) i *
      ((((g⁻¹ : GL (Fin s) K) : Matrix (Fin s) (Fin s) K)ᵀ) *ᵥ
        fun i => v (Sum.inr (Sum.inl i))) i) =
      (((g : Matrix (Fin s) (Fin s) K) *ᵥ fun i => v (Sum.inl i)) ⬝ᵥ
        ((((g⁻¹ : GL (Fin s) K) : Matrix (Fin s) (Fin s) K)ᵀ) *ᵥ
          fun i => v (Sum.inr (Sum.inl i)))) from rfl,
    dot_mulVec_transpose_mulVec _ _ (Units.inv_mul g)]
  rfl

theorem quadOdd_smul (c : K) (w : Fin s ⊕ Fin s ⊕ Unit → K) :
    StatedQuadOdd s K (c • w) = c ^ 2 * StatedQuadOdd s K w := by
  simp only [StatedQuadOdd, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem quadOdd_exists_one : ∃ w : Fin s ⊕ Fin s ⊕ Unit → K, StatedQuadOdd s K w = 1 :=
  ⟨Pi.single (Sum.inr (Sum.inr ())) 1, by simp [StatedQuadOdd, Pi.single_apply]⟩

theorem quadMinus_leviExt (r : ℕ) (b c : K) (g : GL (Fin (r - 1)) K)
    (v : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus r K b c ((leviExt (r - 1) (Fin 2) K g : Matrix _ _ K) *ᵥ v) =
      StatedQuadMinus r K b c v := by
  rw [leviExt_mulVec]
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Sum.elim_inl, Sum.elim_inr]
  rw [show (∑ i, ((g : Matrix (Fin (r - 1)) (Fin (r - 1)) K) *ᵥ fun i => v (Sum.inl i)) i *
      ((((g⁻¹ : GL (Fin (r - 1)) K) : Matrix (Fin (r - 1)) (Fin (r - 1)) K)ᵀ) *ᵥ
        fun i => v (Sum.inr (Sum.inl i))) i) =
      (((g : Matrix (Fin (r - 1)) (Fin (r - 1)) K) *ᵥ fun i => v (Sum.inl i)) ⬝ᵥ
        ((((g⁻¹ : GL (Fin (r - 1)) K) : Matrix (Fin (r - 1)) (Fin (r - 1)) K)ᵀ) *ᵥ
          fun i => v (Sum.inr (Sum.inl i)))) from rfl,
    dot_mulVec_transpose_mulVec _ _ (Units.inv_mul g)]
  rfl

theorem quadMinus_smul (r : ℕ) (b c a : K) (w : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus r K b c (a • w) = a ^ 2 * StatedQuadMinus r K b c w := by
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.mul_sum]
  have : ∀ i : Fin (r - 1), a * w (Sum.inl i) * (a * w (Sum.inr (Sum.inl i))) =
      a ^ 2 * (w (Sum.inl i) * w (Sum.inr (Sum.inl i))) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => this i]
  ring

theorem quadMinus_exists_one (r : ℕ) (b c : K) :
    ∃ w : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K, StatedQuadMinus r K b c w = 1 :=
  ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, by
    simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]⟩

end Forms

end CFSG.LocalAnalysis.RankFourTheoremC
