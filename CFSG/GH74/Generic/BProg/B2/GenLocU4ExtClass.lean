module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtCore
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel

namespace GenLocU4ExtClass

variable {K : Type} [Field K]

theorem sum_zero_aux (h2 : (2 : K) ≠ 0) (ε : Fin 4 → K) (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (hall : ¬ ∀ j, ε j = ε 0) (hiso : ∀ k, ¬ ∀ j, j ≠ k → ε j ≠ ε k) :
    ε 0 + ε 1 + ε 2 + ε 3 = 0 := by
  have hne : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)
  have hne' : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rcases hε 3 with h3 | h3 <;>
  first
    | (rw [h0, h1, h2', h3]; ring1)
    | (refine absurd ?_ hall; intro j; fin_cases j <;> simp_all; done)
    | (refine absurd ?_ (hiso 0); intro j hj; fin_cases j <;> simp_all; done)
    | (refine absurd ?_ (hiso 1); intro j hj; fin_cases j <;> simp_all; done)
    | (refine absurd ?_ (hiso 2); intro j hj; fin_cases j <;> simp_all; done)
    | (refine absurd ?_ (hiso 3); intro j hj; fin_cases j <;> simp_all)

theorem isolated_false {q : ℕ} (ε : Fin 4 → K)
    (i' : Matrix (Fin 4) (Fin 4) K) (c : K) (hU : (i'.map (· ^ q))ᵀ * i' = 1)
    (hsq : i' * i' = c • (1 : Matrix (Fin 4) (Fin 4) K))
    (hD : i' * Matrix.diagonal ε = Matrix.diagonal ε * i')
    (hc : ∀ μ : K, μ ^ (q + 1) = 1 → μ * μ ≠ c) (k : Fin 4) (hk : ∀ j, j ≠ k → ε j ≠ ε k) : False := by
  have hz : ∀ j, j ≠ k → i' j k = 0 ∧ i' k j = 0 := by
    intro j hj
    have hne : ε j - ε k ≠ 0 := sub_ne_zero.2 (hk j hj)
    have e1 := congrFun (congrFun hD j) k
    have e2 := congrFun (congrFun hD k) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e1 e2
    constructor
    · have : (ε j - ε k) * i' j k = 0 := by linear_combination -e1
      exact (mul_eq_zero.1 this).resolve_left hne
    · have : (ε j - ε k) * i' k j = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left hne
  have hsq' : i' k k * i' k k = c := by
    have := congrFun (congrFun hsq k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k] at this
    · simpa using this
    · intro j _ hj
      rw [(hz j hj).2, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hU' : (i' k k) ^ q * i' k k = 1 := by
    have := congrFun (congrFun hU k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k] at this
    · simpa using this
    · intro j _ hj
      rw [Matrix.transpose_apply, Matrix.map_apply, (hz j hj).1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  exact hc (i' k k) (by rw [pow_succ]; exact hU') hsq'

theorem conj_comm {P x y : GL (Fin 4) K} {D : Matrix (Fin 4) (Fin 4) K}
    (hxP : (x : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) * D)
    (hxy : x * y = y * x) :
    ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * D =
      D * ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have hPi : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.inv_mul P
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.mul_inv P
  have hD : D = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
      (P : Matrix (Fin 4) (Fin 4) K) := by
    rw [Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, hPi, Matrix.one_mul]
  have hxy' : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      (y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) := by
    simpa [Units.val_mul] using congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hxy
  simp only [Units.val_mul]
  calc ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) *
        (P : Matrix (Fin 4) (Fin 4) K) * D
      = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) *
          (x : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) := by
        rw [Matrix.mul_assoc _ (P : Matrix (Fin 4) (Fin 4) K), ← hxP]
        simp only [Matrix.mul_assoc]
    _ = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
          (y : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) := by rw [hxy']
    _ = D * (((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K)) := by
        rw [hD]
        calc ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
              (y : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K)
            = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
                ((P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
                  (y : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) := by
              rw [hPP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_sq_scalar (P y : GL (Fin 4) K) (c : K)
    (hy : (y : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) = c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      c • (1 : Matrix (Fin 4) (Fin 4) K) := by
  have e : ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      = ((P⁻¹ * (y * y) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← Units.val_mul]; congr 1; group
  rw [e]
  simp only [Units.val_mul]
  rw [hy, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

theorem trace_x_zero {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (x i : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (hxn : ∀ l : K, (x : Matrix (Fin 4) (Fin 4) K) ≠ l • (1 : Matrix (Fin 4) (Fin 4) K))
    (hiU : ((i : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (i : Matrix (Fin 4) (Fin 4) K) = 1)
    (c : K) (hi2 : (i : Matrix (Fin 4) (Fin 4) K) * (i : Matrix (Fin 4) (Fin 4) K) = c • (1 : Matrix (Fin 4) (Fin 4) K))
    (hc : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ c) (hxi : x * i = i * x) :
    (x : Matrix (Fin 4) (Fin 4) K).trace = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  obtain ⟨P, ε, hPU, hε, hxP⟩ := GenLocU4ExtFrame.exists_frame_diag hp hp2 hK x hxU hx2
  have hPm := GenLocU4ExtCore.mem_primeFormUnitary_of h hPU
  have him := GenLocU4ExtCore.mem_primeFormUnitary_of h hiU
  have hiU' := GenLocU4ExtCore.unitary_of_mem h (mul_mem (mul_mem (inv_mem hPm) him) hPm)
  have hi2' := conj_sq_scalar P i c hi2
  have hD' := conj_comm hxP hxi
  have hPi : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.inv_mul P
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.mul_inv P
  have hx' : (x : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ε * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hxP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hs : ε 0 + ε 1 + ε 2 + ε 3 = 0 := by
    refine sum_zero_aux h2 ε hε ?_ ?_
    · intro hall
      have hDε : Matrix.diagonal ε = (ε 0) • (1 : Matrix (Fin 4) (Fin 4) K) := by
        ext a b
        by_cases hab : a = b
        · subst hab; simp [hall a]
        · simp [hab]
      refine hxn (ε 0) ?_
      rw [hx', hDε, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    · intro k hk
      exact isolated_false ε _ c hiU' hi2' hD' (by simpa using hc) k hk
  have h1 : (x : Matrix (Fin 4) (Fin 4) K).trace = (Matrix.diagonal ε).trace := by
    rw [hx', Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  rw [h1, Matrix.trace_diagonal, Fin.sum_univ_four]
  exact hs

theorem conj_back (P g : GL (Fin 4) K) :
    (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ * g * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : Matrix (Fin 4) (Fin 4) K) := by
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem conj_mul' (P : GL (Fin 4) K) (M N : Matrix (Fin 4) (Fin 4) K) :
    (P : Matrix (Fin 4) (Fin 4) K) * (M * N) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((P : Matrix (Fin 4) (Fin 4) K) * M * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
        ((P : Matrix (Fin 4) (Fin 4) K) * N * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  have hPi : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.inv_mul P
  calc (P : Matrix (Fin 4) (Fin 4) K) * (M * N) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      = (P : Matrix (Fin 4) (Fin 4) K) * M * (((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K)) * N * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        rw [hPi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem smul_unitary_eq {q : ℕ} (d : K) (B : Matrix (Fin 2) (Fin 2) K) :
    ((d • B).map (· ^ q))ᵀ * (d • B) = (d ^ q * d) • ((B.map (· ^ q))ᵀ * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    mul_pow, Fin.sum_univ_two]
  ring

theorem four_class_U {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (x i g : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (htr : (x : Matrix (Fin 4) (Fin 4) K).trace = 0)
    (hiU : ((i : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (i : Matrix (Fin 4) (Fin 4) K) = 1)
    (c : K) (hi2 : (i : Matrix (Fin 4) (Fin 4) K) * (i : Matrix (Fin 4) (Fin 4) K) = c • (1 : Matrix (Fin 4) (Fin 4) K))
    (hgU : ((g : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (g : Matrix (Fin 4) (Fin 4) K) = 1)
    (l : K) (hg2 : (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) = l • (1 : Matrix (Fin 4) (Fin 4) K))
    (hxi : x * i = i * x) (hxg : x * g = g * x) (hig : i * g = g * i)
    (ω : K) (hω : ω ^ (p ^ f) * ω = 1) (hωc : ω * ω * c = -1) :
    ∃ μ : K, μ ≠ 0 ∧ ((g : Matrix (Fin 4) (Fin 4) K) = μ • (1 : Matrix (Fin 4) (Fin 4) K) ∨
      (g : Matrix (Fin 4) (Fin 4) K) = μ • (x : Matrix (Fin 4) (Fin 4) K) ∨
      (g : Matrix (Fin 4) (Fin 4) K) = μ • (i : Matrix (Fin 4) (Fin 4) K) ∨
      (g : Matrix (Fin 4) (Fin 4) K) = μ • ((i * x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hq0 : p ^ f ≠ 0 := by omega
  obtain ⟨P, hPU, hxP⟩ := GenLocU4ExtFrame.exists_frame hp hp2 hK x hxU hx2 htr
  have hPm := GenLocU4ExtCore.mem_primeFormUnitary_of h hPU
  have him := GenLocU4ExtCore.mem_primeFormUnitary_of h hiU
  have hgm := GenLocU4ExtCore.mem_primeFormUnitary_of h hgU
  have hiU' := GenLocU4ExtCore.unitary_of_mem h (mul_mem (mul_mem (inv_mem hPm) him) hPm)
  have hgU' := GenLocU4ExtCore.unitary_of_mem h (mul_mem (mul_mem (inv_mem hPm) hgm) hPm)
  have hi2' := conj_sq_scalar P i c hi2
  have hg2' := conj_sq_scalar P g l hg2
  have hDi := conj_comm hxP hxi
  have hDg := conj_comm hxP hxg
  obtain ⟨I1, I2, hbi⟩ := GenLocU4ExtBd.exists_bd_of_comm h2 _ hDi
  obtain ⟨C, C', hbg⟩ := GenLocU4ExtBd.exists_bd_of_comm h2 _ hDg
  have hω0 : ω ≠ 0 := fun h0 => by rw [h0] at hω; simp at hω
  have e1 := hi2'
  rw [hbi, ← GenLocU4ExtBd.bd_one, GenLocU4ExtBd.bd_mul, GenLocU4ExtBd.bd_smul] at e1
  obtain ⟨hI1, hI2⟩ := GenLocU4ExtBd.bd_inj e1
  have e2 := hg2'
  rw [hbg, ← GenLocU4ExtBd.bd_one, GenLocU4ExtBd.bd_mul, GenLocU4ExtBd.bd_smul] at e2
  obtain ⟨hC, hC'⟩ := GenLocU4ExtBd.bd_inj e2
  have e3 := hiU'
  rw [hbi, GenLocU4ExtBd.bd_unitary hq0, ← GenLocU4ExtBd.bd_one] at e3
  obtain ⟨hI1U, hI2U⟩ := GenLocU4ExtBd.bd_inj e3
  have e4 := hgU'
  rw [hbg, GenLocU4ExtBd.bd_unitary hq0, ← GenLocU4ExtBd.bd_one] at e4
  obtain ⟨hCU, hC'U⟩ := GenLocU4ExtBd.bd_inj e4
  have hcomm : ((P⁻¹ * g * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((P⁻¹ * i * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((P⁻¹ * i * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((P⁻¹ * g * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc P⁻¹ * g * P * (P⁻¹ * i * P) = P⁻¹ * (g * i) * P := by group
      _ = P⁻¹ * (i * g) * P := by rw [hig.symm]
      _ = P⁻¹ * i * P * (P⁻¹ * g * P) := by group
  rw [hbg, hbi, GenLocU4ExtBd.bd_mul, GenLocU4ExtBd.bd_mul] at hcomm
  obtain ⟨hCI1, hC'I2⟩ := GenLocU4ExtBd.bd_inj hcomm
  have hB : (ω • I1) * (ω • I1) = -1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI1, smul_smul, hωc, neg_smul, one_smul]
  have hB' : (ω • I2) * (ω • I2) = -1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI2, smul_smul, hωc, neg_smul, one_smul]
  have hBU : ((ω • I1).map (· ^ (p ^ f)))ᵀ * (ω • I1) = 1 := by
    rw [smul_unitary_eq, hI1U, hω, one_smul]
  have hB'U : ((ω • I2).map (· ^ (p ^ f)))ᵀ * (ω • I2) = 1 := by
    rw [smul_unitary_eq, hI2U, hω, one_smul]
  have hCB : C * (ω • I1) = (ω • I1) * C := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hCI1]
  have hC'B' : C' * (ω • I2) = (ω • I2) * C' := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hC'I2]
  obtain ⟨μ, hμ, hcases⟩ := GenLocU4ExtBd.block_class hq h2 (ω • I1) (ω • I2) C C' l hB hBU hB' hB'U hC hCU
    hC' hC'U hCB hC'B'
  have hgback := GenLocU4ExtClass.conj_back P g
  rw [hbg] at hgback
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.mul_inv P
  have hxback : (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![-1, -1, 1, 1] *
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (x : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hxP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hiback := GenLocU4ExtClass.conj_back P i
  rw [hbi] at hiback
  have hsm : ∀ (a : K) (M : Matrix (Fin 4) (Fin 4) K), (P : Matrix (Fin 4) (Fin 4) K) * (a • M) *
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      a • ((P : Matrix (Fin 4) (Fin 4) K) * M * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
    intro a M
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hxi' : (x : Matrix (Fin 4) (Fin 4) K) * (i : Matrix (Fin 4) (Fin 4) K) =
      ((i * x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hxi, Units.val_mul]
  rcases hcases with ⟨hC1, hC1'⟩ | ⟨hC1, hC1'⟩ | ⟨hC1, hC1'⟩ | ⟨hC1, hC1'⟩
  · refine ⟨μ, hμ, Or.inl ?_⟩
    rw [← hgback, hC1, hC1', ← GenLocU4ExtBd.bd_smul, GenLocU4ExtBd.bd_one, hsm, Matrix.mul_one, hPP]
  · refine ⟨-μ, neg_ne_zero.2 hμ, Or.inr (Or.inl ?_)⟩
    have hb : GenLocU4ExtBd.bd (μ • (1 : Matrix (Fin 2) (Fin 2) K)) (-(μ • (1 : Matrix (Fin 2) (Fin 2) K))) =
        (-μ) • Matrix.diagonal ![-1, -1, 1, 1] := by
      rw [GenLocU4ExtBd.diag_eq_bd, GenLocU4ExtBd.bd_smul, smul_neg, neg_smul, neg_neg]
    rw [← hgback, hC1, hC1', hb, hsm, hxback]
  · refine ⟨μ * ω, mul_ne_zero hμ hω0, Or.inr (Or.inr (Or.inl ?_))⟩
    have hb : GenLocU4ExtBd.bd (μ • (ω • I1)) (μ • (ω • I2)) = (μ * ω) • GenLocU4ExtBd.bd I1 I2 := by
      rw [GenLocU4ExtBd.bd_smul, smul_smul, smul_smul]
    rw [← hgback, hC1, hC1', hb, hsm, hiback]
  · refine ⟨-(μ * ω), neg_ne_zero.2 (mul_ne_zero hμ hω0), Or.inr (Or.inr (Or.inr ?_))⟩
    have hb : GenLocU4ExtBd.bd (μ • (ω • I1)) (-(μ • (ω • I2))) =
        (-(μ * ω)) • (Matrix.diagonal ![-1, -1, 1, 1] * GenLocU4ExtBd.bd I1 I2) := by
      rw [GenLocU4ExtBd.diag_eq_bd, GenLocU4ExtBd.bd_mul, GenLocU4ExtBd.bd_smul, neg_mul, one_mul, one_mul,
        smul_neg, neg_smul, neg_neg, smul_smul, smul_smul, neg_smul]
    rw [← hgback, hC1, hC1', hb, hsm, GenLocU4ExtClass.conj_mul', hxback, hiback, hxi']

end GenLocU4ExtClass

end CFSG.GH74.Generic.BProg.B2
