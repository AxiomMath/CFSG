module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLTools
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open scoped MatrixGroups
open Polynomial

section Cyclic

variable {F : Type} [Field F]

theorem coeffs_eq_zero_of_cube_noncube {a : F} (ha : ∀ b : F, b ^ 3 ≠ a)
    (x : Matrix (Fin 3) (Fin 3) F) (hx : x ^ 3 = Matrix.scalar (Fin 3) a) {v : Fin 3 → F}
    (hv : v ≠ 0) (g : Fin 3 → F)
    (hg : g 0 • v + g 1 • (x.mulVec v) + g 2 • (x.mulVec (x.mulVec v)) = 0) : g = 0 := by
  by_contra hg0
  have hirr : Irreducible (X ^ 3 - C a : F[X]) := X_pow_sub_C_irreducible_of_prime Nat.prime_three ha
  set p : F[X] := C (g 0) + C (g 1) * X + C (g 2) * X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    apply hg0
    have c0 : p.coeff 0 = g 0 := by simp [hp, coeff_C]
    have c1 : p.coeff 1 = g 1 := by simp [hp, coeff_C]
    have c2 : p.coeff 2 = g 2 := by simp [hp, coeff_X_pow]
    ext i
    fin_cases i
    · simp [← c0, h]
    · simp [← c1, h]
    · simp [← c2, h]
  have hdeg : p.natDegree ≤ 2 := by
    rw [hp]
    compute_degree
  have hnd : ¬ (X ^ 3 - C a : F[X]) ∣ p := by
    intro hd
    have := natDegree_le_of_dvd hd hp0
    rw [natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨u, w, huw⟩ := (hirr.coprime_iff_not_dvd.mpr hnd)
  have h1 := congrArg (Polynomial.aeval x) huw
  simp only [map_add, map_mul, map_one, map_sub, aeval_X_pow, aeval_C] at h1
  have hx' : x ^ 3 - (algebraMap F (Matrix (Fin 3) (Fin 3) F)) a = 0 := by
    rw [hx]
    exact sub_eq_zero.mpr rfl
  rw [hx', mul_zero, zero_add] at h1
  have hpv : (aeval x p).mulVec v = 0 := by
    rw [← hg]
    simp only [hp, map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      Matrix.add_mulVec, pow_two, smul_mul_assoc, one_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  apply hv
  calc v = (1 : Matrix (Fin 3) (Fin 3) F).mulVec v := by simp
    _ = ((aeval x w) * (aeval x p)).mulVec v := by rw [h1]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hpv, Matrix.mulVec_zero]

theorem eq_scalar_of_commute_of_eigen {a : F} (ha : ∀ b : F, b ^ 3 ≠ a)
    (x y : Matrix (Fin 3) (Fin 3) F) (hx : x ^ 3 = Matrix.scalar (Fin 3) a) (hxy : x * y = y * x)
    {v : Fin 3 → F} (hv : v ≠ 0) {ε : F} (hyv : y.mulVec v = ε • v) :
    y = Matrix.scalar (Fin 3) ε := by
  let w : Fin 3 → Fin 3 → F := ![v, x.mulVec v, x.mulVec (x.mulVec v)]
  let B : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => w j i
  have hcol : ∀ j, B.col j = w j := fun j => rfl
  have hind : LinearIndependent F B.col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := coeffs_eq_zero_of_cube_noncube ha x hx hv g (by
      simpa [Fin.sum_univ_three, hcol, w] using hg)
    intro i
    exact congrFun this i
  have hB : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.mp hind
  have hyx : ∀ u : Fin 3 → F, y.mulVec (x.mulVec u) = x.mulVec (y.mulVec u) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hxy]
  have hw : ∀ j, y.mulVec (w j) = ε • w j := by
    intro j
    fin_cases j
    · simpa [w] using hyv
    · show y.mulVec (x.mulVec v) = ε • x.mulVec v
      rw [hyx, hyv, Matrix.mulVec_smul]
    · show y.mulVec (x.mulVec (x.mulVec v)) = ε • x.mulVec (x.mulVec v)
      rw [hyx, hyx, hyv, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hyB : y * B = Matrix.scalar (Fin 3) ε * B := by
    ext i j
    have h2 : (Matrix.scalar (Fin 3) ε * B) i j = ε * B i j := by
      simp [Matrix.scalar_apply, Matrix.diagonal_mul]
    have h1 : (y * B) i j = (y.mulVec (w j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, B]
    rw [h1, h2, hw j]
    simp [B]
  exact (hB.mul_left_inj).mp hyB

theorem exists_eigenvector_of_pow_three [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    (y : GL (Fin 3) F) (hy : y ^ 3 = 1) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ ∃ ε : F, (y : Matrix (Fin 3) (Fin 3) F).mulVec v = ε • v := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_dvd (F := F) (m := 3) h3
  have hcomm : ∀ u ∈ Subgroup.zpowers y, ∀ u' ∈ Subgroup.zpowers y, u * u' = u' * u := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self y i j).eq
  have hexp : ∀ u ∈ Subgroup.zpowers y, u ^ 3 = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul]
    simp [hy]
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_conj_diagonal_of_pow_eq_one
    hζ (Subgroup.zpowers y) hcomm hexp
  have hD := hg y (Subgroup.mem_zpowers y)
  set D : Matrix (Fin 3) (Fin 3) F := ((g * y * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    with hDdef
  have hcomm' : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * D =
      (y : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hDdef, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  set e : Fin 3 → F := Pi.single 0 1 with he
  refine ⟨((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec e, ?_, D 0 0, ?_⟩
  · intro h0
    have h1 : e = 0 := by
      have := congrArg (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec) h0
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    have h2 := congrFun h1 0
    simp [he] at h2
  · have hDe : D.mulVec e = D 0 0 • e := by
      ext i
      fin_cases i
      · simp [he, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · simp [he, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hD 1 0 (by decide)]
      · simp [he, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hD 2 0 (by decide)]
    rw [Matrix.mulVec_mulVec, ← hcomm', ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_smul]

end Cyclic

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
