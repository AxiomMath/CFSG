module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open
open scoped Kronecker

variable {K : Type} [Field K]

private theorem seven_dvd_card_centralizer_of_hom [Finite K] (hK : Nat.card K = 2)
    (v : Multiplicative (Fin 3 → ZMod 3))
    (φ : Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 7) (Fin 7) K) (hφ : Function.Injective φ)
    (hc : ∀ U, φ U * ((c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v : GL (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K) = ((c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v : GL (Fin 7) K) :
        Matrix (Fin 7) (Fin 7) K) * φ U) :
    7 ∣ Nat.card (Subgroup.centralizer
      ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v} : Set (StatedSL 7 K))) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : 7 ∣ Nat.card (GL (Fin 3) K) := by
    have := Fintype.ofFinite K
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK]
    norm_num [Fin.prod_univ_three]
  obtain ⟨U, hU⟩ := exists_prime_orderOf_dvd_card' (G := GL (Fin 3) K) 7 hcard
  have hmem : Units.map φ U ∈ StatedSL 7 K := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK]
    exact Subgroup.mem_top _
  have hcent : (⟨Units.map φ U, hmem⟩ : StatedSL 7 K) ∈
      Subgroup.centralizer ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v} : Set (StatedSL 7 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.coe_map]
    exact hc U
  have hord : orderOf (⟨⟨Units.map φ U, hmem⟩, hcent⟩ : Subgroup.centralizer
      ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v} : Set (StatedSL 7 K))) = 7 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_injective _ (Units.map_injective hφ),
      hU]
  exact (dvd_of_eq hord.symm).trans (orderOf_dvd_natCard _)

private theorem seven_dvd_card_centralizer_c₀_of_two [Finite K] (hK : Nat.card K = 2)
    (v : Multiplicative (Fin 3 → ZMod 3)) (hv : Multiplicative.toAdd v 2 = 0) :
    7 ∣ Nat.card (Subgroup.centralizer
      ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v} : Set (StatedSL 7 K))) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin 2 × Fin 2) ⊕ Fin 3 ≃ Blk ⊕ Fin 1, ∀ x, ρ x =
      Sum.elim (fun y : Fin 2 × Fin 2 => Sum.inl (y.1, y.2.castSucc))
        ![Sum.inl ((0, 2) : Blk), Sum.inl ((1, 2) : Blk), Sum.inr 0] x :=
    ⟨Equiv.ofBijective _ (by decide), fun _ => rfl⟩
  set e := blkEquiv (Or.inr rfl : 7 = 6 ∨ 7 = 7) with he
  set ε : Fin 7 ≃ (Fin 2 × Fin 2) ⊕ Fin 3 := e.trans ρ.symm with hε
  set X : Matrix Blk Blk K := blockDiagonal fun i =>
    ((blockPowGL K (Multiplicative.toAdd v i) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hX
  set N := reindex ε ε ((c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) v : GL (Fin 7) K) :
    Matrix (Fin 7) (Fin 7) K) with hN
  have hM : ∀ x y, N x y = fromBlocks X 0 0 1 (ρ x) (ρ y) := by
    intro x y
    show fromBlocks X 0 0 1 (e (e.symm (ρ x))) (e (e.symm (ρ y))) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h12 : N.toBlocks₁₂ = 0 := by
    ext ⟨p, k⟩ t
    rw [toBlocks₁₂, of_apply, hM, hρ, hρ, Matrix.zero_apply]
    fin_cases p <;> fin_cases k <;> fin_cases t <;> simp [X, blockDiagonal_apply]
  have h21 : N.toBlocks₂₁ = 0 := by
    ext t ⟨p, k⟩
    rw [toBlocks₂₁, of_apply, hM, hρ, hρ, Matrix.zero_apply]
    fin_cases p <;> fin_cases k <;> fin_cases t <;> simp [X, blockDiagonal_apply]
  have h22 : N.toBlocks₂₂ = 1 := by
    ext t t'
    rw [toBlocks₂₂, of_apply, hM, hρ, hρ]
    fin_cases t <;> fin_cases t' <;>
      simp [X, blockDiagonal_apply, hv, blockPowGL_zero, one_apply]
  have hNb : N = fromBlocks N.toBlocks₁₁ 0 0 1 := by
    rw [← h12, ← h21, ← h22, fromBlocks_toBlocks]
  obtain ⟨φ, hφ, hφU⟩ : ∃ φ : Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 7) (Fin 7) K,
      Function.Injective φ ∧ ∀ U, Matrix.reindexRingEquiv K ε (φ U) = fromBlocks 1 0 0 U :=
    ⟨(Matrix.reindexRingEquiv K ε).symm.toMonoidHom.comp
      { toFun := fun U => fromBlocks 1 0 0 U
        map_one' := fromBlocks_one
        map_mul' := fun U V => by simp [fromBlocks_multiply] },
      fun U V h => (fromBlocks_inj.mp ((Matrix.reindexRingEquiv K ε).symm.injective
        (a₁ := fromBlocks 1 0 0 U) (a₂ := fromBlocks 1 0 0 V) h)).2.2.2,
      fun U => (Matrix.reindexRingEquiv K ε).apply_symm_apply (fromBlocks 1 0 0 U)⟩
  refine seven_dvd_card_centralizer_of_hom hK v φ hφ fun U => ?_
  apply (Matrix.reindexRingEquiv K ε).injective
  rw [map_mul, map_mul, hφU]
  change fromBlocks 1 0 0 U * N = N * fromBlocks 1 0 0 U
  rw [hNb, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem seven_dvd_card_centralizer_c₀_weight_one [Finite K] (hK : Nat.card K = 2) :
    7 ∣ Nat.card (Subgroup.centralizer
      ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) (Multiplicative.ofAdd ![1, 0, 0])} :
        Set (StatedSL 7 K))) :=
  seven_dvd_card_centralizer_c₀_of_two hK _ rfl

theorem seven_dvd_card_centralizer_c₀_weight_two [Finite K] (hK : Nat.card K = 2) :
    7 ∣ Nat.card (Subgroup.centralizer
      ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) (Multiplicative.ofAdd ![1, 1, 0])} :
        Set (StatedSL 7 K))) :=
  seven_dvd_card_centralizer_c₀_of_two hK _ rfl

theorem seven_dvd_card_centralizer_c₀_weight_three [Finite K] (hK : Nat.card K = 2) :
    7 ∣ Nat.card (Subgroup.centralizer
      ({c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) (Multiplicative.ofAdd ![1, 1, 1])} :
        Set (StatedSL 7 K))) := by
  have hX : (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd
      (Multiplicative.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) i) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = blockS K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext ⟨p, i⟩ ⟨q, j⟩
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal_apply, blockPowGL_one, blockSGL]
  refine seven_dvd_card_centralizer_of_hom hK _
    ((embMonoidHom (Or.inr rfl : 7 = 6 ∨ 7 = 7)).comp
      { toFun := fun U => (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ U
        map_one' := one_kronecker_one
        map_mul' := fun U V => by rw [← mul_kronecker_mul, Matrix.mul_one] }) ?_ ?_
  · intro U V h
    ext i j
    simpa using congrFun (congrFun (embMat_injective _ h) (0, i)) (0, j)
  · intro U
    rw [show ((c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7) (Multiplicative.ofAdd ![1, 1, 1]) :
        GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = embMat (Or.inr rfl : 7 = 6 ∨ 7 = 7)
          (blockS K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) from congrArg (embMat _) hX]
    change embMat _ (1 ⊗ₖ U) * _ = _ * embMat _ (1 ⊗ₖ U)
    rw [← embMat_mul, ← embMat_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp

end CFSG.ClassicalGroups.SLnThreeLocal
