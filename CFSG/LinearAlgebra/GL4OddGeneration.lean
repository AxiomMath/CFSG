module

public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LinearAlgebra

open Matrix

theorem exists_odd_orderOf_map_eq {Γ Γ' : Type*} [Group Γ] [Finite Γ] [Group Γ']
    (ρ : Γ →* Γ') {γ : Γ} (hodd : Odd (orderOf (ρ γ))) :
    ∃ γ' ∈ Subgroup.zpowers γ, Odd (orderOf γ') ∧ ρ γ' = ρ γ := by
  classical
  let n := orderOf γ
  let k := n.factorization 2
  let m := n / 2 ^ k
  let o := orderOf (ρ γ)
  have hn0 : n ≠ 0 := (orderOf_pos γ).ne'
  have hdvd : 2 ^ k ∣ n := Nat.ordProj_dvd n 2
  have hpow : orderOf (γ ^ 2 ^ k) = m := by
    have h := orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) hdvd
    simpa [n, k, m] using h
  have hm_odd : Odd m := by
    have hcompl : m = ordCompl[2] n := rfl
    rw [hcompl]
    exact (Nat.coprime_ordCompl Nat.prime_two hn0).odd_of_left
  have ho_dvd : o ∣ n := orderOf_map_dvd ρ γ
  have ho_pos : 0 < o := Nat.pos_of_dvd_of_pos ho_dvd (orderOf_pos γ)
  have hcop : Nat.Coprime o (2 ^ k) := hodd.coprime_two_right.pow_right k
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt ho_pos) with hogt | ho1
  · obtain ⟨s, -, hs⟩ :=
      Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hogt
    let e := 2 ^ k * s
    have he : e % o = 1 := by
      simpa [e] using hs
    have hmap : ρ (γ ^ e) = ρ γ := by
      rw [map_pow]
      have hpoweq : (ρ γ) ^ e = (ρ γ) ^ 1 := by
        rw [pow_inj_mod]
        change e % o = 1 % o
        rw [he, Nat.mod_eq_of_lt hogt]
      simpa using hpoweq
    have hγe_eq : γ ^ e = (γ ^ 2 ^ k) ^ s := by
      simp only [e, pow_mul]
    have hγe_odd : Odd (orderOf (γ ^ e)) := by
      apply hm_odd.of_dvd_nat
      rw [hγe_eq]
      calc orderOf ((γ ^ 2 ^ k) ^ s) ∣ orderOf (γ ^ 2 ^ k) := orderOf_pow_dvd s
        _ = m := hpow
    exact ⟨γ ^ e, Subgroup.npow_mem_zpowers γ e, hγe_odd, hmap⟩
  · have ho1' : o = 1 := ho1.symm
    have hρ1 : ρ γ = 1 := orderOf_eq_one_iff.mp ho1'
    refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
    · simpa using odd_one
    · rw [map_one, hρ1]

private lemma pow_eq_one_of_matrix_pow {M : GL (Fin 4) (ZMod 2)} {k : ℕ}
    (h : ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ k) = 1) : M ^ k = 1 := by
  apply Units.ext
  rwa [Units.val_pow_eq_pow_val, Units.val_one]

private lemma odd_of_pow_eq_one {M : GL (Fin 4) (ZMod 2)} {k : ℕ} (hk : Odd k)
    (h : M ^ k = 1) : Odd (orderOf M) :=
  hk.of_dvd_nat (orderOf_dvd_of_pow_eq_one h)

private abbrev X (i j : Fin 4) (hij : i ≠ j) : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.transvection i j hij 1

private abbrev matA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0,0,1,0; 0,0,1,1; 1,0,0,1; 0,1,0,0]

private abbrev A : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matA (by decide)

private abbrev matB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0,1,0,0; 0,1,1,0; 0,0,1,1; 1,0,0,1]

private abbrev B : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matB (by decide)

private abbrev matC : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0,0,0,1; 1,0,0,1; 0,1,0,0; 0,0,1,0]

private abbrev C : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matC (by decide)

private abbrev matD : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0,0,0,1; 0,0,1,0; 0,1,0,1; 1,1,0,0]

private abbrev D : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matD (by decide)

private abbrev matE : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0,0,0,1; 0,0,1,0; 0,1,0,1; 1,0,1,1]

private abbrev E : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matE (by decide)

private lemma A_pow : A ^ 15 = 1 := by
  apply pow_eq_one_of_matrix_pow
  change (matA ^ 15) = 1
  decide

private lemma B_pow : B ^ 5 = 1 := by
  apply pow_eq_one_of_matrix_pow
  change (matB ^ 5) = 1
  decide

private lemma C_pow : C ^ 15 = 1 := by
  apply pow_eq_one_of_matrix_pow
  change (matC ^ 15) = 1
  decide

private lemma D_pow : D ^ 15 = 1 := by
  apply pow_eq_one_of_matrix_pow
  change (matD ^ 15) = 1
  decide

private lemma E_pow : E ^ 5 = 1 := by
  apply pow_eq_one_of_matrix_pow
  change (matE ^ 5) = 1
  decide

private lemma X01_A_pow : (X 0 1 (by decide) * A) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 0 1 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matA) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X02_C_pow : (X 0 2 (by decide) * C) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 0 2 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matC) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X03_D_pow : (X 0 3 (by decide) * D) ^ 15 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 0 3 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matD) ^ 15 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X10_E_pow : (X 1 0 (by decide) * E) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 1 0 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matE) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X12_A_pow : (X 1 2 (by decide) * A) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 1 2 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matA) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X13_C_pow : (X 1 3 (by decide) * C) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 1 3 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matC) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X20_C_pow : (X 2 0 (by decide) * C) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 2 0 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matC) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X21_B_pow : (X 2 1 (by decide) * B) ^ 15 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 2 1 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matB) ^ 15 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X23_A_pow : (X 2 3 (by decide) * A) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 2 3 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matA) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X30_A_pow : (X 3 0 (by decide) * A) ^ 7 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 3 0 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matA) ^ 7 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X31_C_pow : (X 3 1 (by decide) * C) ^ 5 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 3 1 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matC) ^ 5 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma X32_B_pow : (X 3 2 (by decide) * B) ^ 15 = 1 := by
  apply pow_eq_one_of_matrix_pow
  rw [Units.val_mul]
  change ((X 3 2 (by decide) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * matB) ^ 15 = 1
  simp only [X, Matrix.GeneralLinearGroup.val_transvection]
  decide

private lemma A_odd : Odd (orderOf A) :=
  odd_of_pow_eq_one ⟨7, by norm_num⟩ A_pow

private lemma B_odd : Odd (orderOf B) :=
  odd_of_pow_eq_one ⟨2, by norm_num⟩ B_pow

private lemma C_odd : Odd (orderOf C) :=
  odd_of_pow_eq_one ⟨7, by norm_num⟩ C_pow

private lemma D_odd : Odd (orderOf D) :=
  odd_of_pow_eq_one ⟨7, by norm_num⟩ D_pow

private lemma E_odd : Odd (orderOf E) :=
  odd_of_pow_eq_one ⟨2, by norm_num⟩ E_pow

private lemma X01_A_odd : Odd (orderOf (X 0 1 (by decide) * A)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X01_A_pow

private lemma X02_C_odd : Odd (orderOf (X 0 2 (by decide) * C)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X02_C_pow

private lemma X03_D_odd : Odd (orderOf (X 0 3 (by decide) * D)) :=
  odd_of_pow_eq_one ⟨7, by norm_num⟩ X03_D_pow

private lemma X10_E_odd : Odd (orderOf (X 1 0 (by decide) * E)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X10_E_pow

private lemma X12_A_odd : Odd (orderOf (X 1 2 (by decide) * A)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X12_A_pow

private lemma X13_C_odd : Odd (orderOf (X 1 3 (by decide) * C)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X13_C_pow

private lemma X20_C_odd : Odd (orderOf (X 2 0 (by decide) * C)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X20_C_pow

private lemma X21_B_odd : Odd (orderOf (X 2 1 (by decide) * B)) :=
  odd_of_pow_eq_one ⟨7, by norm_num⟩ X21_B_pow

private lemma X23_A_odd : Odd (orderOf (X 2 3 (by decide) * A)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X23_A_pow

private lemma X30_A_odd : Odd (orderOf (X 3 0 (by decide) * A)) :=
  odd_of_pow_eq_one ⟨3, by norm_num⟩ X30_A_pow

private lemma X31_C_odd : Odd (orderOf (X 3 1 (by decide) * C)) :=
  odd_of_pow_eq_one ⟨2, by norm_num⟩ X31_C_pow

private lemma X32_B_odd : Odd (orderOf (X 3 2 (by decide) * B)) :=
  odd_of_pow_eq_one ⟨7, by norm_num⟩ X32_B_pow

private abbrev K : Subgroup (GL (Fin 4) (ZMod 2)) :=
  Subgroup.closure {x : GL (Fin 4) (ZMod 2) | Odd (orderOf x)}

private lemma mem_K_of_mul_mem {i j : Fin 4} (hij : i ≠ j) {M : GL (Fin 4) (ZMod 2)}
    (hXM : X i j hij * M ∈ K) (hM : M ∈ K) : X i j hij ∈ K := by
  have h := K.mul_mem hXM (K.inv_mem hM)
  simpa using h

private lemma X01_mem (hij : (0 : Fin 4) ≠ 1) : X 0 1 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X01_A_odd)
    (Subgroup.subset_closure A_odd)

private lemma X02_mem (hij : (0 : Fin 4) ≠ 2) : X 0 2 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X02_C_odd)
    (Subgroup.subset_closure C_odd)

private lemma X03_mem (hij : (0 : Fin 4) ≠ 3) : X 0 3 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X03_D_odd)
    (Subgroup.subset_closure D_odd)

private lemma X10_mem (hij : (1 : Fin 4) ≠ 0) : X 1 0 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X10_E_odd)
    (Subgroup.subset_closure E_odd)

private lemma X12_mem (hij : (1 : Fin 4) ≠ 2) : X 1 2 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X12_A_odd)
    (Subgroup.subset_closure A_odd)

private lemma X13_mem (hij : (1 : Fin 4) ≠ 3) : X 1 3 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X13_C_odd)
    (Subgroup.subset_closure C_odd)

private lemma X20_mem (hij : (2 : Fin 4) ≠ 0) : X 2 0 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X20_C_odd)
    (Subgroup.subset_closure C_odd)

private lemma X21_mem (hij : (2 : Fin 4) ≠ 1) : X 2 1 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X21_B_odd)
    (Subgroup.subset_closure B_odd)

private lemma X23_mem (hij : (2 : Fin 4) ≠ 3) : X 2 3 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X23_A_odd)
    (Subgroup.subset_closure A_odd)

private lemma X30_mem (hij : (3 : Fin 4) ≠ 0) : X 3 0 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X30_A_odd)
    (Subgroup.subset_closure A_odd)

private lemma X31_mem (hij : (3 : Fin 4) ≠ 1) : X 3 1 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X31_C_odd)
    (Subgroup.subset_closure C_odd)

private lemma X32_mem (hij : (3 : Fin 4) ≠ 2) : X 3 2 hij ∈ K :=
  mem_K_of_mul_mem hij (Subgroup.subset_closure X32_B_odd)
    (Subgroup.subset_closure B_odd)

private lemma transvection_mem_closure_odd {i j : Fin 4} (hij : i ≠ j) : X i j hij ∈ K := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact X01_mem (by simpa using hij)
  · exact X02_mem (by simpa using hij)
  · exact X03_mem (by simpa using hij)
  · exact X10_mem (by simpa using hij)
  · exact (hij rfl).elim
  · exact X12_mem (by simpa using hij)
  · exact X13_mem (by simpa using hij)
  · exact X20_mem (by simpa using hij)
  · exact X21_mem (by simpa using hij)
  · exact (hij rfl).elim
  · exact X23_mem (by simpa using hij)
  · exact X30_mem (by simpa using hij)
  · exact X31_mem (by simpa using hij)
  · exact X32_mem (by simpa using hij)
  · exact (hij rfl).elim

private lemma diagonal_eq_one_of_det_ne_zero {D : Fin 4 → ZMod 2}
    (hD : (Matrix.diagonal D).det ≠ 0) : D = 1 := by
  funext i
  have hprod : (Finset.univ.prod D : ZMod 2) ≠ 0 := by
    simpa [Matrix.det_diagonal] using hD
  have hDnz : D i ≠ 0 :=
    (Finset.prod_ne_zero_iff (s := Finset.univ) (f := D)).mp
      (by simpa using hprod) i (Finset.mem_univ i)
  exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) (D i) hDnz

private lemma exists_unit_mem_K_of_matrix {M : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hM : M.det ≠ 0) : ∃ u ∈ K, (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M := by
  classical
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (P := fun N => ∃ u ∈ K, (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = N) M hM ?_ ?_ ?_
  · intro D hD
    have hD1 : D = 1 := diagonal_eq_one_of_det_ne_zero hD
    refine ⟨1, Subgroup.one_mem K, ?_⟩
    rw [hD1]
    simp
  · intro t
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t.c with hc | hc
    · refine ⟨1, Subgroup.one_mem K, ?_⟩
      change (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Matrix.transvection t.i t.j t.c
      rw [hc, Matrix.transvection_zero]
    · refine ⟨X t.i t.j t.hij, transvection_mem_closure_odd t.hij, ?_⟩
      change (Matrix.transvection t.i t.j 1) = Matrix.transvection t.i t.j t.c
      rw [hc]
  · intro B C _ _ hB hC
    obtain ⟨u, huK, huB⟩ := hB
    obtain ⟨v, hvK, hvC⟩ := hC
    refine ⟨u * v, K.mul_mem huK hvK, ?_⟩
    rw [Units.val_mul, huB, hvC]

theorem GL4_mem_closure_odd (g : GL (Fin 4) (ZMod 2)) :
    g ∈ Subgroup.closure {x : GL (Fin 4) (ZMod 2) | Odd (orderOf x)} := by
  obtain ⟨u, huK, hu⟩ := exists_unit_mem_K_of_matrix
    (Matrix.GeneralLinearGroup.det_ne_zero g)
  have hug : u = g := Units.ext hu
  simpa [K, hug] using huK

theorem exists_mem_closure_odd_map_eq {Γ : Type*} [Group Γ] [Finite Γ]
    (ρ : Γ →* GL (Fin 4) (ZMod 2)) (hρ : Function.Surjective ρ)
    (g : GL (Fin 4) (ZMod 2)) :
    ∃ γ ∈ Subgroup.closure {γ : Γ | Odd (orderOf γ)}, ρ γ = g := by
  classical
  let K : Subgroup Γ := Subgroup.closure {γ : Γ | Odd (orderOf γ)}
  have key : ∀ x ∈ Subgroup.closure {x : GL (Fin 4) (ZMod 2) | Odd (orderOf x)},
      ∃ γ ∈ K, ρ γ = x := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ γ ∈ K, ρ γ = x) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨γ, hγ⟩ := hρ y
      have hodd : Odd (orderOf (ρ γ)) := by rw [hγ]; exact hy
      obtain ⟨γ', -, hγ'odd, hγ'ρ⟩ := exists_odd_orderOf_map_eq ρ hodd
      refine ⟨γ', Subgroup.subset_closure hγ'odd, ?_⟩
      rw [hγ'ρ, hγ]
    · exact ⟨1, Subgroup.one_mem K, map_one ρ⟩
    · intro a b _ _ iha ihb
      obtain ⟨γ, hγK, hγa⟩ := iha
      obtain ⟨δ, hδK, hδb⟩ := ihb
      refine ⟨γ * δ, K.mul_mem hγK hδK, ?_⟩
      rw [map_mul, hγa, hδb]
    · intro a _ iha
      obtain ⟨γ, hγK, hγa⟩ := iha
      refine ⟨γ⁻¹, K.inv_mem hγK, ?_⟩
      rw [map_inv, hγa]
  exact key g (GL4_mem_closure_odd g)

end CFSG.LinearAlgebra
