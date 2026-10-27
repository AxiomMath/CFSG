module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangianBlock
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLagrangianDot

public section

namespace CFSG.SeitzReduction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical
open FourGroupEvenCanonical (matrixIsometryGroup mem_matrixIsometryGroup)
open SymplecticTorusWeyl (leviSp coe_leviSp)

namespace SymplecticLagrangian

variable {r : ℕ} {K : Type} [Field K]

theorem exists_unit_mul_of_mul_self {X Y : Matrix (Fin r) (Fin r) K} (hX : X * X = 1)
    (hY : Y * Y = 1) :
    ∃ A : GL (Fin r) K, (A : Matrix (Fin r) (Fin r) K) = X * Y ∧
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Y * X :=
  ⟨⟨X * Y, Y * X, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, hY, Matrix.one_mul, hX],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc X, hX, Matrix.one_mul, hY]⟩, rfl, rfl⟩

theorem exists_unit_of_mul_self {X : Matrix (Fin r) (Fin r) K} (hX : X * X = 1) :
    ∃ A : GL (Fin r) K, (A : Matrix (Fin r) (Fin r) K) = X ∧
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = X :=
  ⟨⟨X, X, hX, hX⟩, rfl, rfl⟩

theorem pow_three_eq_one_of_coe {A : GL (Fin r) K}
    (h : (A : Matrix (Fin r) (Fin r) K) ^ 3 = 1) : A ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])

section Alternating

variable [CharP K 2] {S : Matrix (Fin r) (Fin r) K}

omit [CharP K 2] in
theorem transvectionMatrix_mulVec (S : Matrix (Fin r) (Fin r) K) (u x : Fin r → K) :
    (1 + vecMulVec u (S *ᵥ u)) *ᵥ x = x + ((S *ᵥ u) ⬝ᵥ x) • u := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem transvectionMatrix_mul_self_of_isAlt (halt : ∀ x : Fin r → K, x ⬝ᵥ (S *ᵥ x) = 0)
    (u : Fin r → K) : (1 + vecMulVec u (S *ᵥ u)) * (1 + vecMulVec u (S *ᵥ u)) = 1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul, map_one, ClassicalLagrangian.toLinAlgEquiv'_transvection]
  exact ClassicalLagrangian.transvection_mul_self (by rw [Matrix.toBilin'_apply']; exact halt u)

omit [CharP K 2] in
theorem dotProduct_mulVec_comm (hS : Sᵀ = S) (u v : Fin r → K) :
    u ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (S *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

theorem exists_levi_of_isAlt (hS : Sᵀ = S) (halt : ∀ x : Fin r → K, x ⬝ᵥ (S *ᵥ x) = 0)
    {u v : Fin r → K} (huv : u ⬝ᵥ (S *ᵥ v) = 1) :
    ∃ A : GL (Fin r) K,
      (A : Matrix (Fin r) (Fin r) K) * S * (A : Matrix (Fin r) (Fin r) K)ᵀ = S ∧ A ^ 3 = 1 ∧
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ =
        (1 + vecMulVec u (S *ᵥ u)) * (1 + vecMulVec v (S *ᵥ v)) ∧ A ≠ 1 := by
  set tu := 1 + vecMulVec u (S *ᵥ u) with htu
  set tv := 1 + vecMulVec v (S *ᵥ v) with htv
  have hu2 : tu * tu = 1 := transvectionMatrix_mul_self_of_isAlt halt u
  have hv2 : tv * tv = 1 := transvectionMatrix_mul_self_of_isAlt halt v
  have hX : tuᵀ * tuᵀ = 1 := by rw [← transpose_mul, hu2, transpose_one]
  have hY : tvᵀ * tvᵀ = 1 := by rw [← transpose_mul, hv2, transpose_one]
  obtain ⟨A, hA, hAi⟩ := exists_unit_mul_of_mul_self hX hY
  have hiso_u : tuᵀ * S * tu = S := ClassicalLagrangian.transvectionMatrix_isometry halt u
  have hiso_v : tvᵀ * S * tv = S := ClassicalLagrangian.transvectionMatrix_isometry halt v
  have hvu : v ⬝ᵥ (S *ᵥ u) = 1 := by rw [dotProduct_mulVec_comm hS, huv]
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rw [hA, transpose_mul, transpose_transpose, transpose_transpose]
    calc tuᵀ * tvᵀ * S * (tv * tu) = tuᵀ * (tvᵀ * S * tv) * tu := by
          simp only [Matrix.mul_assoc]
      _ = S := by rw [hiso_v, hiso_u]
  · apply pow_three_eq_one_of_coe
    have h3 := ClassicalLagrangian.transvectionMatrix_mul_pow_three halt hvu
    rw [hA, ← transpose_mul, ← transpose_pow, h3, transpose_one]
  · rw [hAi, transpose_mul, transpose_transpose, transpose_transpose]
  · intro h1
    have hA1 : tuᵀ * tvᵀ = 1 := by rw [← hA, h1, Units.val_one]
    have hvu1 : tv * tu = 1 := by
      rw [← transpose_transpose (tv * tu), transpose_mul, hA1, transpose_one]
    have e : (tv * tu) *ᵥ v = u := by
      have h1' : (S *ᵥ u) ⬝ᵥ v = 1 := by rw [dotProduct_comm, hvu]
      have h2' : (S *ᵥ v) ⬝ᵥ v = 0 := by rw [dotProduct_comm, halt]
      have h3' : (S *ᵥ v) ⬝ᵥ u = 1 := by rw [dotProduct_comm, huv]
      have hvv : v + v = 0 := by rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
      rw [← mulVec_mulVec, htu, htv, transvectionMatrix_mulVec S u v, h1', one_smul,
        transvectionMatrix_mulVec, dotProduct_add, h2', h3', zero_add, one_smul, add_comm v u,
        add_assoc, hvv, add_zero]
    rw [hvu1, one_mulVec] at e
    rw [← e, halt] at huv
    exact zero_ne_one huv

theorem involutionCriterion_upperUnipotentSp_of_isAlt [Finite K] (hr : 3 ≤ r) (hS : Sᵀ = S)
    (hSu : IsUnit S) (halt : ∀ x : Fin r → K, x ⬝ᵥ (S *ᵥ x) = 0) :
    InvolutionCriterion (spInner r K (upperUnipotentSp r K hS)) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨v₀, hv₀⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hSu (Pi.single 0 1)
  have huv₀ : (Pi.single 0 1 : Fin r → K) ⬝ᵥ (S *ᵥ v₀) = 1 := by
    rw [hv₀, single_dotProduct, Pi.single_eq_same, one_mul]
  obtain ⟨A₀, hA₀, hA₀3, -, hA₀1⟩ := exists_levi_of_isAlt hS halt huv₀
  refine involutionCriterion_upperUnipotentSp hr hS hSu hA₀ hA₀3 hA₀1 fun G h21 _ hD => ?_
  refine ClassicalLagrangian.exists_eq_smul_one_of_commute_matrix_mul hSu halt
    (by rw [Fintype.card_fin]; omega) fun u v huv => ?_
  obtain ⟨A, hA, hA3, hAi, -⟩ := exists_levi_of_isAlt hS halt huv
  have h := hD _ (leviSp_mem_closure_odd hS hA hA3)
  simp only [spMat, coe_leviSp] at h
  have h2 := (commute_toBlocks_of_commute_fromBlocks_diag h21 h).2
  rw [hAi] at h2
  exact h2

end Alternating

section Dot

variable [CharP K 2]

omit [CharP K 2] in
theorem transvectionMatrix_one_mulVec (u x : Fin r → K) :
    (1 + vecMulVec u u) *ᵥ x = x + (u ⬝ᵥ x) • u := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem exists_levi_one {u v : Fin r → K} (hu : u ⬝ᵥ u = 0) (hv : v ⬝ᵥ v = 0)
    (huv : u ⬝ᵥ v = 1) :
    ∃ A : GL (Fin r) K,
      (A : Matrix (Fin r) (Fin r) K) = (1 + vecMulVec u u) * (1 + vecMulVec v v) ∧
      (A : Matrix (Fin r) (Fin r) K) * 1 * (A : Matrix (Fin r) (Fin r) K)ᵀ = 1 ∧ A ^ 3 = 1 ∧
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ =
        (1 + vecMulVec u u) * (1 + vecMulVec v v) ∧
      A ≠ 1 ∧ A ∈ matrixIsometryGroup (1 : Matrix (Fin r) (Fin r) K) := by
  have hu2 := ClassicalLagrangian.transvectionMatrix_one_mul_self hu
  have hv2 := ClassicalLagrangian.transvectionMatrix_one_mul_self hv
  have hut := ClassicalLagrangian.transvectionMatrix_one_transpose u
  have hvt := ClassicalLagrangian.transvectionMatrix_one_transpose v
  obtain ⟨A, hA, hAi⟩ := exists_unit_mul_of_mul_self hu2 hv2
  have hAAt : (A : Matrix (Fin r) (Fin r) K)ᵀ * (A : Matrix (Fin r) (Fin r) K) = 1 := by
    rw [hA, transpose_mul, hut, hvt]
    calc (1 + vecMulVec v v) * (1 + vecMulVec u u) * ((1 + vecMulVec u u) * (1 + vecMulVec v v))
        = (1 + vecMulVec v v) * ((1 + vecMulVec u u) * (1 + vecMulVec u u)) *
            (1 + vecMulVec v v) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu2, Matrix.mul_one, hv2]
  refine ⟨A, hA, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_one]
    exact mul_eq_one_comm.mp hAAt
  · apply pow_three_eq_one_of_coe
    rw [hA]
    exact ClassicalLagrangian.transvectionMatrix_one_mul_pow_three hu hv huv
  · rw [hAi, transpose_mul, hut, hvt]
  · intro h1
    have e : (A : Matrix (Fin r) (Fin r) K) *ᵥ v = v + u := by
      rw [hA, ← mulVec_mulVec, transvectionMatrix_one_mulVec v v, hv, zero_smul, add_zero,
        transvectionMatrix_one_mulVec, huv, one_smul]
    rw [h1, Units.val_one, one_mulVec, left_eq_add] at e
    rw [e, zero_dotProduct] at huv
    exact zero_ne_one huv
  · rw [mem_matrixIsometryGroup, Matrix.mul_one]
    exact hAAt

theorem upperUnipotentSp_shear_mem_closure_odd {u v e : Fin r → K} (hu : u ⬝ᵥ u = 0)
    (hv : v ⬝ᵥ v = 0) (huv : u ⬝ᵥ v = 1) (hue : u ⬝ᵥ e = 0) (hve : v ⬝ᵥ e = 0) :
    upperUnipotentSp r K (show (vecMulVec u e + vecMulVec e u)ᵀ = vecMulVec u e + vecMulVec e u by
        rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]) ∈
      closure {c : StatedSp r K | c ∈ centralizer {upperUnipotentSp r K transpose_one} ∧
        Odd (orderOf c)} := by
  obtain ⟨A, hA, hA1, hA3, -, -, -⟩ := exists_levi_one hu hv huv
  have hT' : (vecMulVec v e + vecMulVec e v)ᵀ = vecMulVec v e + vecMulVec e v := by
    rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
  have h := upperUnipotentSp_sub_mem_closure_odd transpose_one hA1 hA3 hT'
  convert h using 2
  have hAe : (A : Matrix (Fin r) (Fin r) K) *ᵥ e = e := by
    rw [hA, ← mulVec_mulVec, transvectionMatrix_one_mulVec v e, hve, zero_smul, add_zero,
      transvectionMatrix_one_mulVec, hue, zero_smul, add_zero]
  have hAv : (A : Matrix (Fin r) (Fin r) K) *ᵥ v = v + u := by
    rw [hA, ← mulVec_mulVec, transvectionMatrix_one_mulVec v v, hv, zero_smul, add_zero,
      transvectionMatrix_one_mulVec, huv, one_smul]
  rw [Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
    mul_vecMulVec, vecMulVec_mul, vecMul_transpose, hAe, hAv, add_vecMulVec, vecMulVec_add]
  abel

omit [CharP K 2] in
theorem single_add_single_dotProduct {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Pi.single i 1 + Pi.single j 1 : Fin r → K) ⬝ᵥ (Pi.single j 1 + Pi.single k 1 : Fin r → K) =
      1 := by
  simp [hij.symm, hik.symm, hjk.symm]

theorem onesVec_dotProduct_single_add_single {i j : Fin r} :
    (onesVec : Fin r → K) ⬝ᵥ (Pi.single i 1 + Pi.single j 1) = 0 := by
  simp only [dotProduct_add, dotProduct_single, onesVec_apply, mul_one]
  exact CharTwo.add_self_eq_zero 1

omit [CharP K 2] in
theorem single_add_single_ne_zero {i j : Fin r} (hij : i ≠ j) :
    (Pi.single i (1 : K) + Pi.single j 1 : Fin r → K) ≠ 0 := fun h => by
  have := congrFun h i
  simp [hij] at this

theorem involutionCriterion_upperUnipotentSp_one_of_odd [Finite K] (hr : 3 ≤ r) (hodd : Odd r) :
    InvolutionCriterion (spInner r K (upperUnipotentSp r K
      (transpose_one : (1 : Matrix (Fin r) (Fin r) K)ᵀ = 1))) := by
  set i0 : Fin r := ⟨0, by omega⟩
  set i1 : Fin r := ⟨1, by omega⟩
  set i2 : Fin r := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  set u₀ : Fin r → K := Pi.single i0 1 + Pi.single i1 1
  set v₀ : Fin r → K := Pi.single i1 1 + Pi.single i2 1
  have hsq : ∀ x : Fin r → K, onesVec ⬝ᵥ x = 0 → x ⬝ᵥ x = 0 := fun x hx => by
    rw [dotProduct_self_eq_sq, hx, zero_pow two_ne_zero]
  have hu₀d : onesVec ⬝ᵥ u₀ = 0 := onesVec_dotProduct_single_add_single
  have hv₀d : onesVec ⬝ᵥ v₀ = 0 := onesVec_dotProduct_single_add_single
  have huv₀ : u₀ ⬝ᵥ v₀ = 1 := single_add_single_dotProduct h01 h02 h12
  obtain ⟨A₀, -, hA₀, hA₀3, -, hA₀1, -⟩ := exists_levi_one (hsq u₀ hu₀d) (hsq v₀ hv₀d) huv₀
  refine involutionCriterion_upperUnipotentSp hr transpose_one isUnit_one hA₀ hA₀3 hA₀1
    fun G h21 h11 hD => ?_
  rw [Matrix.mul_one, Matrix.one_mul] at h11
  refine ClassicalLagrangian.exists_eq_smul_one_of_commute_odd_mul hodd
    (fun u v hu hv huv => ?_) hu₀d (single_add_single_ne_zero h01) ?_
  · obtain ⟨A, -, hA, hA3, hAi, -, -⟩ := exists_levi_one (hsq u hu) (hsq v hv) huv
    have h := hD _ (leviSp_mem_closure_odd transpose_one hA hA3)
    simp only [spMat, coe_leviSp] at h
    have h2 := (commute_toBlocks_of_commute_fromBlocks_diag h21 h).2
    rw [hAi] at h2
    exact h2
  · have h := hD _ (upperUnipotentSp_shear_mem_closure_odd (e := onesVec) (hsq u₀ hu₀d)
      (hsq v₀ hv₀d) huv₀ (by rw [dotProduct_comm, hu₀d]) (by rw [dotProduct_comm, hv₀d]))
    simp only [spMat, coe_upperUnipotentSp] at h
    have h2 := toBlocks_mul_eq_of_commute_fromBlocks_one h21 h
    rw [h11] at h2
    exact h2

theorem involutionCriterion_upperUnipotentSp_one_of_even [Finite K] (hr : 3 ≤ r)
    (heven : Even r) :
    InvolutionCriterion (spInner r K (upperUnipotentSp r K
      (transpose_one : (1 : Matrix (Fin r) (Fin r) K)ᵀ = 1))) := by
  have hr4 : 4 ≤ r := by
    obtain ⟨m, hm⟩ := heven
    omega
  set i : Fin r := ⟨0, by omega⟩
  set i1 : Fin r := ⟨1, by omega⟩
  set i2 : Fin r := ⟨2, by omega⟩
  have h01 : i ≠ i1 := by simp [i, i1, Fin.ext_iff]
  have h02 : i ≠ i2 := by simp [i, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  set u₀ : Fin r → K := Pi.single i1 1 + Pi.single i2 1
  have hu₀ : u₀ ∈ radicalW i := mem_radicalW.mpr ⟨onesVec_dotProduct_single_add_single, by
    simp [u₀, h01, h02]⟩
  have hu₀0 : u₀ ≠ 0 := single_add_single_ne_zero h12
  obtain ⟨v₀, hv₀, huv₀⟩ :=
    ClassicalLagrangian.exists_dotProduct_eq_one_of_mem_radicalW heven hu₀ hu₀0
  have hsqW : ∀ x ∈ radicalW (K := K) i, x ⬝ᵥ x = 0 := fun x hx => by
    rw [dotProduct_self_eq_sq, (mem_radicalW.mp hx).1, zero_pow two_ne_zero]
  have hvv : ∀ x : Fin r → K, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  obtain ⟨A₀, -, hA₀, hA₀3, -, hA₀1, -⟩ := exists_levi_one (hsqW u₀ hu₀) (hsqW v₀ hv₀) huv₀
  refine involutionCriterion_upperUnipotentSp hr transpose_one isUnit_one hA₀ hA₀3 hA₀1
    fun G h21 h11 hD => ?_
  rw [Matrix.mul_one, Matrix.one_mul] at h11
  refine ClassicalLagrangian.exists_eq_smul_one_of_commute_even_mul heven (i := i)
    (fun u hu v hv huv => ?_) (fun v hv => ?_) hu₀ hu₀0 ?_
  · obtain ⟨A, -, hA, hA3, hAi, -, -⟩ := exists_levi_one (hsqW u hu) (hsqW v hv) huv
    have h := hD _ (leviSp_mem_closure_odd transpose_one hA hA3)
    simp only [spMat, coe_leviSp] at h
    have h2 := (commute_toBlocks_of_commute_fromBlocks_diag h21 h).2
    rw [hAi] at h2
    exact h2
  · by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, radicalMatrix_zero]; exact Commute.one_right _⟩
    obtain ⟨v', hv', hvv'⟩ :=
      ClassicalLagrangian.exists_dotProduct_eq_one_of_mem_radicalW heven hv hv0
    obtain ⟨y, hy, hy1, hy3, -, -, hyO⟩ := exists_levi_one (hsqW v hv) (hsqW v' hv') hvv'
    have hv'd : onesVec ⬝ᵥ v' = 0 := (mem_radicalW.mp hv').1
    obtain ⟨ρ, hρ, hρi⟩ := exists_unit_of_mul_self (radicalMatrix_mul_self heven hv'd (0 : K))
    have hρ1 : (ρ : Matrix (Fin r) (Fin r) K) * 1 * (ρ : Matrix (Fin r) (Fin r) K)ᵀ = 1 := by
      rw [hρ, Matrix.mul_one, radicalMatrix_transpose, radicalMatrix_mul_self heven hv'd]
    have hmem := mul_conj_inv_mem_closure_odd (leviSp_mem_centralizer transpose_one hy1)
      (odd_orderOf_leviSp hy3) (leviSp_mem_centralizer transpose_one hρ1)
    have e : leviSp y * (leviSp ρ * (leviSp y)⁻¹ * (leviSp ρ)⁻¹) =
        leviSp (y * (ρ * y⁻¹ * ρ⁻¹)) := by
      simp only [map_mul, map_inv]
    rw [e] at hmem
    have h := hD _ hmem
    simp only [spMat, coe_leviSp] at h
    have h2 := (commute_toBlocks_of_commute_fromBlocks_diag h21 h).1
    have hyv' : (y : Matrix (Fin r) (Fin r) K) *ᵥ v' + v' = v := by
      rw [hy, ← mulVec_mulVec, transvectionMatrix_one_mulVec v' v', hsqW v' hv', zero_smul,
        add_zero, transvectionMatrix_one_mulVec, hvv', one_smul, add_comm v' v, add_assoc, hvv,
        add_zero]
    have hZ : ((y * (ρ * y⁻¹ * ρ⁻¹) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        radicalMatrix v ((y : Matrix (Fin r) (Fin r) K) *ᵥ v' ⬝ᵥ v') := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hρ, hρi, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ClassicalLagrangian.conj_radicalMatrix_mul_radicalMatrix heven hyO hv'd,
        hyv']
    rw [hZ, h11] at h2
    exact ⟨_, h2⟩
  · have hu₀e : u₀ ⬝ᵥ Pi.single i 1 = 0 := by
      rw [dotProduct_single, mul_one]
      exact (mem_radicalW.mp hu₀).2
    have hv₀e : v₀ ⬝ᵥ Pi.single i 1 = 0 := by
      rw [dotProduct_single, mul_one]
      exact (mem_radicalW.mp hv₀).2
    have h := hD _ (upperUnipotentSp_shear_mem_closure_odd (e := Pi.single i 1) (hsqW u₀ hu₀)
      (hsqW v₀ hv₀) huv₀ hu₀e hv₀e)
    simp only [spMat, coe_upperUnipotentSp] at h
    have h2 := toBlocks_mul_eq_of_commute_fromBlocks_one h21 h
    rw [h11] at h2
    exact h2

end Dot

end SymplecticLagrangian

end CFSG.SeitzReduction
