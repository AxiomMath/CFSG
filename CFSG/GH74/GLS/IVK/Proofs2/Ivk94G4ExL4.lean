module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4E16b
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4E16

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Matrix Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Pauli

variable {F : Type} [Field F]

@[expose] def pA : Matrix (Fin 4) (Fin 4) F := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
@[expose] def pB : Matrix (Fin 4) (Fin 4) F := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
@[expose] def pC : Matrix (Fin 4) (Fin 4) F := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]
@[expose] def pD : Matrix (Fin 4) (Fin 4) F := !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1]

@[expose] def pauli : Fin 4 → Matrix (Fin 4) (Fin 4) F := ![pA, pB, pC, pD]

theorem pauli_sq (i : Fin 4) : (pauli i : Matrix (Fin 4) (Fin 4) F) * pauli i = 1 := by
  fin_cases i <;>
    (ext k l; fin_cases k <;> fin_cases l <;>
      simp [pauli, pA, pB, pC, pD, Matrix.mul_apply, Fin.sum_univ_succ])

@[expose] def wPauli : Fin 4 → Fin 4 → ℕ := ![![0,1,0,0], ![1,0,0,0], ![0,0,0,1], ![0,0,1,0]]

theorem comm01 : (pA : Matrix (Fin 4) (Fin 4) F) * pB = -(pB * pA) := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pA, pB, Matrix.mul_apply, Fin.sum_univ_succ]

theorem comm02 : (pA : Matrix (Fin 4) (Fin 4) F) * pC = pC * pA := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pA, pC, Matrix.mul_apply, Fin.sum_univ_succ]

theorem comm03 : (pA : Matrix (Fin 4) (Fin 4) F) * pD = pD * pA := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pA, pD, Matrix.mul_apply, Fin.sum_univ_succ]

theorem comm12 : (pB : Matrix (Fin 4) (Fin 4) F) * pC = pC * pB := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pB, pC, Matrix.mul_apply, Fin.sum_univ_succ]

theorem comm13 : (pB : Matrix (Fin 4) (Fin 4) F) * pD = pD * pB := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pB, pD, Matrix.mul_apply, Fin.sum_univ_succ]

theorem comm23 : (pC : Matrix (Fin 4) (Fin 4) F) * pD = -(pD * pC) := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pC, pD, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sign_zero_of_comm {A B : Matrix (Fin 4) (Fin 4) F} (h : A * B = B * A) :
    A * B = (-1 : F) ^ 0 • (B * A) := by
  rw [pow_zero, one_smul]
  exact h

theorem sign_one_of_anticomm {A B : Matrix (Fin 4) (Fin 4) F} (h : A * B = -(B * A)) :
    A * B = (-1 : F) ^ 1 • (B * A) := by
  rw [pow_one, neg_smul, one_smul]
  exact h

theorem comm10 : (pB : Matrix (Fin 4) (Fin 4) F) * pA = -(pA * pB) := by
  rw [comm01, neg_neg]

theorem comm32 : (pD : Matrix (Fin 4) (Fin 4) F) * pC = -(pC * pD) := by
  rw [comm23, neg_neg]

theorem pauli_comm (i j : Fin 4) :
    (pauli i : Matrix (Fin 4) (Fin 4) F) * pauli j =
      (-1 : F) ^ wPauli i j • ((pauli j : Matrix (Fin 4) (Fin 4) F) * pauli i) := by
  fin_cases i <;> fin_cases j
  · exact sign_zero_of_comm rfl
  · exact sign_one_of_anticomm comm01
  · exact sign_zero_of_comm comm02
  · exact sign_zero_of_comm comm03
  · exact sign_one_of_anticomm comm10
  · exact sign_zero_of_comm rfl
  · exact sign_zero_of_comm comm12
  · exact sign_zero_of_comm comm13
  · exact sign_zero_of_comm comm02.symm
  · exact sign_zero_of_comm comm12.symm
  · exact sign_zero_of_comm rfl
  · exact sign_one_of_anticomm comm23
  · exact sign_zero_of_comm comm03.symm
  · exact sign_zero_of_comm comm13.symm
  · exact sign_one_of_anticomm comm32
  · exact sign_zero_of_comm rfl

theorem pauli_nondeg : ∀ a : Fin 4 → Fin 2, a ≠ 0 → ∃ j, ¬ 2 ∣ ∑ i, wPauli j i * (a i : ℕ) := by
  decide

theorem det_pA : (pA : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [pA, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_pB : (pB : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [pB, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_pC : (pC : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [pC, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_pD : (pD : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [pD, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_pauli (i : Fin 4) : (pauli i : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  fin_cases i
  · exact det_pA
  · exact det_pB
  · exact det_pC
  · exact det_pD

theorem pA_map_pow {q : ℕ} (hq : Odd q) : (pA : Matrix (Fin 4) (Fin 4) F).map (· ^ q) = pA := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  ext k l; fin_cases k <;> fin_cases l <;> simp [pA, hq0]

theorem pB_map_pow {q : ℕ} (hq : Odd q) : (pB : Matrix (Fin 4) (Fin 4) F).map (· ^ q) = pB := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  ext k l; fin_cases k <;> fin_cases l <;> simp [pB, hq0, hq.neg_one_pow]

theorem pC_map_pow {q : ℕ} (hq : Odd q) : (pC : Matrix (Fin 4) (Fin 4) F).map (· ^ q) = pC := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  ext k l; fin_cases k <;> fin_cases l <;> simp [pC, hq0]

theorem pD_map_pow {q : ℕ} (hq : Odd q) : (pD : Matrix (Fin 4) (Fin 4) F).map (· ^ q) = pD := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  ext k l; fin_cases k <;> fin_cases l <;> simp [pD, hq0, hq.neg_one_pow]

theorem pA_transpose : (pA : Matrix (Fin 4) (Fin 4) F)ᵀ = pA := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pA]

theorem pB_transpose : (pB : Matrix (Fin 4) (Fin 4) F)ᵀ = pB := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pB]

theorem pC_transpose : (pC : Matrix (Fin 4) (Fin 4) F)ᵀ = pC := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pC]

theorem pD_transpose : (pD : Matrix (Fin 4) (Fin 4) F)ᵀ = pD := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [pD]

theorem pauli_map_pow {q : ℕ} (hq : Odd q) (i : Fin 4) :
    (pauli i : Matrix (Fin 4) (Fin 4) F).map (· ^ q) = pauli i := by
  fin_cases i
  · exact pA_map_pow hq
  · exact pB_map_pow hq
  · exact pC_map_pow hq
  · exact pD_map_pow hq

theorem pauli_transpose (i : Fin 4) : (pauli i : Matrix (Fin 4) (Fin 4) F)ᵀ = pauli i := by
  fin_cases i
  · exact pA_transpose
  · exact pB_transpose
  · exact pC_transpose
  · exact pD_transpose

theorem pauli_unitary {q : ℕ} (hq : Odd q) (i : Fin 4) :
    ((pauli i : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ * pauli i = 1 := by
  rw [pauli_map_pow hq, pauli_transpose, pauli_sq]

@[expose] def pauliGL (F : Type) [Field F] (i : Fin 4) : GL (Fin 4) F :=
  involGL (pauli i) (pauli_sq i)

theorem exists_E16_pauli (hne : (-1 : F) ≠ 1) {H : Subgroup (GL (Fin 4) F)}
    (hH : ∀ i, pauliGL F i ∈ H) :
    ∃ E : Subgroup (StatedProj H), (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  refine exists_E16_statedProj (pauliGL F) hH ?_ ?_ ?_
  · intro i
    exact ⟨1, by rw [one_smul]; exact pauli_sq i⟩
  · intro i j
    exact ⟨(-1) ^ wPauli i j, pauli_comm i j⟩
  · exact not_scalar_of_comm_signs hne (pauliGL F) wPauli (fun i j => pauli_comm i j)
      pauli_nondeg

end Pauli

theorem k94_psl4 :
    K94Excl fun K _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel K .PSL 4 p f := by
  refine k94Excl_of_E16 ?_
  rintro K _ _ ⟨p, f, hp, hp2, -, -, hL⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  refine exists_E16_of_equiv e
    (exists_E16_pauli (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure (det_pauli i)

theorem k94_psu4 :
    K94Excl fun K _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel K .PSU 4 p f := by
  refine k94Excl_of_E16 ?_
  rintro K _ _ ⟨p, f, hp, hp2, -, -, hL⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hq.pow
  refine exists_E16_of_equiv e
    (exists_E16_pauli (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure ⟨det_pauli i, pauli_unitary hq i⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
