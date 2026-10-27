module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN5D8

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig

variable {p f : ℕ} {K : Type} [Field K]

theorem ar_unitary (h : UnitaryFieldData p f K) :
    ((ar : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * ar = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ar, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply]

theorem br_unitary (h : UnitaryFieldData p f K) :
    ((br : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * br = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [br, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply]

theorem two_ne_zero_of_prime_ne_two (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro h0
  have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  have := (CharP.cast_eq_zero_iff K p 2).1 h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)

theorem exists_D8_comm_su4 (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {t : GL (Fin 4) K}
    (ht : t ∈ unitarySU p f K 4) (htt : t * t = 1) :
    ∃ a b : GL (Fin 4) K, a ∈ unitarySU p f K 4 ∧ b ∈ unitarySU p f K 4 ∧ a * t = t * a ∧
      b * t = t * b ∧ a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_prime_ne_two h hp2
  have hpodd : Odd (p ^ f) := (h.prime.eq_two_or_odd'.resolve_left hp2).pow
  have hpq : 2 ∣ p ^ f + 1 := hpodd.add_one.two_dvd
  let tU : primeFormUnitary h (idGram K 4) := ⟨t, unitarySU_le_primeFormUnitary h ht⟩
  have htU : tU * tU = 1 := Subtype.ext htt
  let G : Subgroup (primeFormUnitary h (idGram K 4)) := Subgroup.zpowers tU
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl tU).zpow_zpow m n).eq
  have hpow : ∀ x ∈ G, x ^ 2 = 1 := fun x hx => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [pow_two, ← _root_.zpow_add, ← two_mul, _root_.zpow_mul, zpow_two, htU, _root_.one_zpow]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_two hpq G hcomm hpow
  have hdiag := hP tU (Subgroup.mem_zpowers tU)
  set Pg : GL (Fin 4) K := (P : GL (Fin 4) K) with hPg
  have hPmem : Pg ∈ primeFormUnitary h (idGram K 4) := P.2
  set Pm : Matrix (Fin 4) (Fin 4) K := (Pg : Matrix (Fin 4) (Fin 4) K) with hPm
  set Pi : Matrix (Fin 4) (Fin 4) K := ((Pg⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hPi
  have hPmPi : Pm * Pi = 1 := Pg.mul_inv
  have hPiPm : Pi * Pm = 1 := Pg.inv_mul
  have hunit : (Pm.map h.bar)ᵀ * Pm = 1 := by
    have := hPmem
    simpa [mem_primeFormUnitary, idGram] using this
  set T : Matrix (Fin 4) (Fin 4) K := (t : Matrix (Fin 4) (Fin 4) K) with hT
  have hTT : T * T = 1 := by rw [hT, ← Units.val_mul, htt, Units.val_one]
  have hD : (Pi * T * Pm).IsDiag := by
    have h1 : ((P⁻¹ * tU * P : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) = Pg⁻¹ * t * Pg := rfl
    rw [h1, Units.val_mul, Units.val_mul] at hdiag
    exact hdiag
  set μ : Fin 4 → K := fun j => (Pi * T * Pm) j j with hμdef
  have hDeq : Pi * T * Pm = diagonal μ := hD.diagonal_diag.symm
  have hTP : T * Pm = Pm * diagonal μ := by
    rw [← hDeq]
    calc T * Pm = (Pm * Pi) * T * Pm := by rw [hPmPi, Matrix.one_mul]
      _ = Pm * (Pi * T * Pm) := by simp only [Matrix.mul_assoc]
  have hDD : diagonal μ * diagonal μ = 1 := by
    rw [← hDeq]
    calc Pi * T * Pm * (Pi * T * Pm) = Pi * (T * (Pm * Pi) * T) * Pm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPmPi, Matrix.mul_one, hTT, Matrix.mul_one, hPiPm]
  have hμ : ∀ j, μ j = 1 ∨ μ j = -1 := fun j => by
    have := congrFun (congrFun hDD j) j
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact mul_self_eq_one_iff.1 this
  obtain ⟨σ, hσ⟩ := exists_perm_eq hμ
  obtain ⟨h1, h2', h3⟩ := submatrix_perm_facts σ hPmPi hPiPm hTP
  rw [diagonal_perm_pair hσ] at h3
  have hunit' : ((Pm.submatrix id σ).map h.bar)ᵀ * Pm.submatrix id σ = 1 := by
    rw [← Matrix.submatrix_map, Matrix.transpose_submatrix,
      ← Matrix.submatrix_mul _ _ σ id σ Function.bijective_id, hunit, Matrix.submatrix_one_equiv]
  let Pc : GL (Fin 4) K := ⟨Pm.submatrix id σ, Pi.submatrix σ id, h1, h2'⟩
  have hPc : Pc ∈ primeFormUnitary h (idGram K 4) := by
    simpa [mem_primeFormUnitary, idGram] using hunit'
  set m := μ (σ 0)
  set n := μ (σ 2)
  set k := μ (σ 3)
  let ga : GL (Fin 4) K := Matrix.SpecialLinearGroup.toGL arSL
  let gb : GL (Fin 4) K := Matrix.SpecialLinearGroup.toGL brSL
  have hga : ga ∈ unitarySU p f K 4 := (mem_unitarySU_iff h).2 ⟨ar_det, ar_unitary h⟩
  have hgb : gb ∈ unitarySU p f K 4 := (mem_unitarySU_iff h).2 ⟨br_det, br_unitary h⟩
  refine ⟨Pc * ga * Pc⁻¹, Pc * gb * Pc⁻¹, conj_mem_unitarySU h hPc hga, conj_mem_unitarySU h hPc hgb,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact conj_comm (D := diagonal ![m, m, n, k]) h1 h2' h3 (ar_diag m n k)
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact conj_comm (D := diagonal ![m, m, n, k]) h1 h2' h3 (br_diag m n k)
  · have : Pc * ga * Pc⁻¹ = MulAut.conj Pc ga := rfl
    rw [this, ← map_pow]
    have h4 : ga ^ 4 = 1 := by rw [← map_pow, arSL_pow, map_one]
    rw [h4, map_one]
  · intro h5
    have : Pc * ga * Pc⁻¹ = MulAut.conj Pc ga := rfl
    rw [this, ← map_pow] at h5
    have h6 : ga ^ 2 = 1 := (MulAut.conj Pc).injective (by rw [h5, map_one])
    apply arSL_sq_ne h2
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, map_one]
    exact h6
  · have : Pc * gb * Pc⁻¹ = MulAut.conj Pc gb := rfl
    rw [this, ← map_mul]
    have h4 : gb * gb = 1 := by rw [← map_mul, brSL_sq, map_one]
    rw [h4, map_one]
  · have e1 : Pc * ga * Pc⁻¹ = MulAut.conj Pc ga := rfl
    have e2 : Pc * gb * Pc⁻¹ = MulAut.conj Pc gb := rfl
    rw [e1, e2, ← map_inv, ← map_mul, ← map_mul]
    have h4 : gb * ga * gb⁻¹ = ga⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, brSL_arSL, map_inv]
    rw [h4, map_inv]

end CFSG.GH74.Generic.BProg.B3.S45EvenN5D8
