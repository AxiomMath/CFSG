module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
import CFSG.Open.StatedZModTwo
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open
open scoped Kronecker

variable {K : Type} [Field K]

private theorem exists_perfect_le_centralizer_c₀_six_of_hom [Finite K] (hK : Nat.card K = 2)
    (v : Multiplicative (Fin 3 → ZMod 3))
    (φ : Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 6) (Fin 6) K) (hφ : Function.Injective φ)
    (hc : ∀ U, φ U * ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) v : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) v : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * φ U) :
    ∃ J : Subgroup (StatedSL 6 K), J ≤ Subgroup.centralizer
        ({c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) v} : Set (StatedSL 6 K)) ∧ ⁅J, J⁆ = J ∧
      7 ∣ Nat.card J := by
  let ψ : Matrix.SpecialLinearGroup (Fin 3) K →* StatedSL 6 K :=
    { toFun := fun U => ⟨Units.map φ (Matrix.SpecialLinearGroup.toGL U), by
        rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK]
        exact Subgroup.mem_top _⟩
      map_one' := by
        apply Subtype.ext
        exact Units.ext (by simp)
      map_mul' := fun U V => by
        apply Subtype.ext
        exact Units.ext (by simp) }
  have hψinj : Function.Injective ψ := by
    intro U V h
    have h1 : Units.map φ (Matrix.SpecialLinearGroup.toGL U) =
        Units.map φ (Matrix.SpecialLinearGroup.toGL V) := congrArg Subtype.val h
    exact Matrix.SpecialLinearGroup.toGL_injective (Units.map_injective hφ h1)
  have hcard : Nat.card ψ.range = 168 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top,
      ← CFSG.Open.StatedAPI.card_statedSL 3 K, CFSG.Open.StatedAPI.card_statedSL_three, hK]
    norm_num
  refine ⟨ψ.range, ?_, ?_, by rw [hcard]; norm_num⟩
  · rintro _ ⟨U, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.coe_map]
    exact hc U
  · have hJ : ψ.range = (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map ψ :=
      MonoidHom.range_eq_map ψ
    have hcomm : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)), ⊤⁆ = ⊤ :=
      CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (n := 3) (by norm_num)
    rw [hJ, ← Subgroup.map_commutator, hcomm, Subgroup.map_top]

private theorem weight_one_equiv :
    ∃ ρ : Fin 3 ⊕ Fin 3 ≃ Blk ⊕ Fin 0, ∀ x, ρ x =
      Sum.elim (fun i : Fin 3 => Sum.inl (![(0, 0), (1, 0), (0, 1)] i : Blk))
        (fun i : Fin 3 => Sum.inl (![(1, 1), (0, 2), (1, 2)] i : Blk)) x :=
  ⟨Equiv.ofBijective _ (by decide), fun _ => rfl⟩

private theorem weight_one_hom (ε : Fin 6 ≃ Fin 3 ⊕ Fin 3) :
    ∃ φ : Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 6) (Fin 6) K,
      Function.Injective φ ∧ ∀ U, Matrix.reindexRingEquiv K ε (φ U) = fromBlocks 1 0 0 U :=
  ⟨(Matrix.reindexRingEquiv K ε).symm.toMonoidHom.comp
    { toFun := fun U => fromBlocks 1 0 0 U
      map_one' := fromBlocks_one
      map_mul' := fun U V => by simp [fromBlocks_multiply] },
    fun U V h => (fromBlocks_inj.mp ((Matrix.reindexRingEquiv K ε).symm.injective
      (a₁ := fromBlocks 1 0 0 U) (a₂ := fromBlocks 1 0 0 V) h)).2.2.2,
    fun U => (Matrix.reindexRingEquiv K ε).apply_symm_apply (fromBlocks 1 0 0 U)⟩

theorem exists_perfect_le_centralizer_c₀_six_weight_one [Finite K] (hK : Nat.card K = 2) :
    ∃ J : Subgroup (StatedSL 6 K), J ≤ Subgroup.centralizer
        ({c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) (Multiplicative.ofAdd ![1, 0, 0])} :
          Set (StatedSL 6 K)) ∧ ⁅J, J⁆ = J ∧ 7 ∣ Nat.card J := by
  obtain ⟨ρ, hρ⟩ := weight_one_equiv
  set e := blkEquiv (Or.inl rfl : 6 = 6 ∨ 6 = 7) with he
  set ε : Fin 6 ≃ Fin 3 ⊕ Fin 3 := e.trans ρ.symm with hε
  set v : Multiplicative (Fin 3 → ZMod 3) := Multiplicative.ofAdd ![1, 0, 0] with hv
  set X : Matrix Blk Blk K := Matrix.blockDiagonal fun i =>
    ((blockPowGL K (Multiplicative.toAdd v i) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hX
  set N := Matrix.reindex ε ε ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) v : GL (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K) with hN
  have hM : ∀ x y, N x y = fromBlocks X 0 0 1 (ρ x) (ρ y) := by
    intro x y
    show fromBlocks X 0 0 1 (e (e.symm (ρ x))) (e (e.symm (ρ y))) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h12 : N.toBlocks₁₂ = 0 := by
    ext p k
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, hM, hρ, hρ, Matrix.zero_apply]
    fin_cases p <;> fin_cases k <;>
      simp [X, Matrix.blockDiagonal_apply, hv, blockPowGL_zero, Matrix.one_apply]
  have h21 : N.toBlocks₂₁ = 0 := by
    ext k p
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, hM, hρ, hρ, Matrix.zero_apply]
    fin_cases k <;> fin_cases p <;>
      simp [X, Matrix.blockDiagonal_apply, hv, blockPowGL_zero, Matrix.one_apply]
  have h22 : N.toBlocks₂₂ = 1 := by
    ext t t'
    rw [Matrix.toBlocks₂₂, Matrix.of_apply, hM, hρ, hρ]
    fin_cases t <;> fin_cases t' <;>
      simp [X, Matrix.blockDiagonal_apply, hv, blockPowGL_zero, Matrix.one_apply]
  have hNb : N = fromBlocks N.toBlocks₁₁ 0 0 1 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks N]
    rw [h12, h21, h22]
  obtain ⟨φ, hφ, hφU⟩ := weight_one_hom (K := K) ε
  apply exists_perfect_le_centralizer_c₀_six_of_hom hK v φ hφ
  intro U
  apply (Matrix.reindexRingEquiv K ε).injective
  rw [map_mul, map_mul, hφU]
  change fromBlocks 1 0 0 U * N = N * fromBlocks 1 0 0 U
  rw [hNb, fromBlocks_multiply, fromBlocks_multiply]
  simp

private theorem weight_three_matrix :
    (Matrix.blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd
      (Multiplicative.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) i) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = blockS K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext ⟨p, i⟩ ⟨q, j⟩
  fin_cases i <;> fin_cases j <;> simp [Matrix.blockDiagonal_apply, blockPowGL_one, blockSGL]

private theorem weight_three_hom :
    ∃ φ : Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 6) (Fin 6) K,
      Function.Injective φ ∧ ∀ U, φ U = embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7)
        ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ U) :=
  ⟨(embMonoidHom (Or.inl rfl : 6 = 6 ∨ 6 = 7)).comp
    { toFun := fun U => (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ U
      map_one' := one_kronecker_one
      map_mul' := fun U V => by rw [← mul_kronecker_mul, Matrix.mul_one] },
    fun U V h => by
      ext i j
      simpa using congrFun (congrFun (embMat_injective _ h) (0, i)) (0, j),
    fun U => rfl⟩

theorem exists_perfect_le_centralizer_c₀_six_weight_three [Finite K] (hK : Nat.card K = 2) :
    ∃ J : Subgroup (StatedSL 6 K), J ≤ Subgroup.centralizer
        ({c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) (Multiplicative.ofAdd ![1, 1, 1])} :
          Set (StatedSL 6 K)) ∧ ⁅J, J⁆ = J ∧ 7 ∣ Nat.card J := by
  set v : Multiplicative (Fin 3 → ZMod 3) := Multiplicative.ofAdd ![1, 1, 1] with hv
  obtain ⟨φ, hφ, hφU⟩ := weight_three_hom (K := K)
  apply exists_perfect_le_centralizer_c₀_six_of_hom hK v φ hφ
  intro U
  rw [show ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) v : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7) (blockS K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) from
    congrArg (embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7)) (weight_three_matrix (K := K))]
  rw [hφU U]
  change embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7) (1 ⊗ₖ U) *
      embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7) (blockS K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) =
    embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7) (blockS K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) *
      embMat (Or.inl rfl : 6 = 6 ∨ 6 = 7) (1 ⊗ₖ U)
  rw [← embMat_mul, ← embMat_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp

end CFSG.ClassicalGroups.SLnThreeLocal
