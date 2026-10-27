module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Mono
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalBlock
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneLift

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryScalar

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem pow_three_eq_one_of_eigen_scalar (hq : ℓ ^ f = 2) {Z M : primeFormUnitary h (idGram K n)}
    (hZ : Z ^ 3 = 1)
    (hM : ∀ ν : K, ∃ c : K, ∀ v : Fin n → K,
      ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v →
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) :
    M ^ 3 = 1 := by
  classical
  have := h.finite
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hZgl : (Z : GL (Fin n) K) ^ 3 = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hZ
    simpa using this
  have hZs : (Z : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [hZgl, map_one]
  have H0 := primaryData_of_pow_eq_scalar Nat.prime_three hpℓ hZs
  obtain ⟨ω, hω⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h Nat.prime_three
    (show 3 ∣ ℓ ^ f + 1 by rw [hq])
  set A : Matrix (Fin n) (Fin n) K := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA
  have hAinj : ∀ v : Fin n → K, A *ᵥ v = 0 → v = 0 := by
    intro v hv
    have : (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (A *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hA, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← this, hv, Matrix.mulVec_zero]
  have hext : Matrix.toLin' (A ^ 3) = LinearMap.id := by
    refine ext_primaryComponent H0.squarefree fun a ha v hv => ?_
    obtain ⟨ν, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors (p := 3) (by norm_num) hω hZgl ha
    have hZv : ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v :=
      mem_primaryComponent_X_sub_C.1 hv
    obtain ⟨c, hc⟩ := hM ν
    have hMv := hc v hZv
    rw [Matrix.toLin'_apply, LinearMap.id_apply, pow_three, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [hMv, Matrix.mulVec_smul, smul_smul]
    by_cases hv0 : v = 0
    · rw [hv0, smul_zero]
    · have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hMv
        exact hv0 (hAinj v hMv)
      rw [show c * c * c = c ^ 3 by ring, pow_three_eq_one h hq hc0, one_smul]
  have hA3 : A ^ 3 = 1 := by
    apply Matrix.toLin'.injective
    rw [hext, Matrix.toLin'_one]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  exact hA3

end CFSG.HardMathSupport.Timmesfeld.CrossChar
