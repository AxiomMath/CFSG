module

public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel Matrix

namespace GenLocU4ExtFrame

variable {K : Type} [Field K]

theorem map_bar_eq {p f : ℕ} (h : UnitaryFieldData p f K) {m n : Type} (M : Matrix m n K) :
    M.map h.bar = M.map (· ^ (p ^ f)) := by
  ext i j
  simp [Matrix.map_apply, UnitaryFieldData.bar_apply]

theorem two_ne_zero_of_card {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) : (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  exact Ring.two_ne_zero (by rwa [ringChar.eq K p])

theorem submatrix_unitary {q : ℕ} (P : Matrix (Fin 4) (Fin 4) K) (hP : (P.map (· ^ q))ᵀ * P = 1)
    (τ : Fin 4 → Fin 4) (hτ : Function.Injective τ) :
    ((P.submatrix id τ).map (· ^ q))ᵀ * P.submatrix id τ = 1 := by
  ext k l
  have := congrFun (congrFun hP (τ k)) (τ l)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
    Matrix.one_apply, hτ.eq_iff, id] at this ⊢
  exact this

theorem exists_sort (h2 : (2 : K) ≠ 0) (ε : Fin 4 → K) (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (hs : ε 0 + ε 1 + ε 2 + ε 3 = 0) :
    ∃ τ : Fin 4 → Fin 4, Function.Injective τ ∧ ∀ k, ε (τ k) = ![-1, -1, 1, 1] k := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rcases hε 3 with h3 | h3 <;> rw [h0, h1, h2', h3] at hs
  · exact absurd (by linear_combination hs) h4
  · exact absurd (by linear_combination hs) h2
  · exact absurd (by linear_combination hs) h2
  · exact ⟨![2, 3, 0, 1], by decide, fun k => by fin_cases k <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination hs) h2
  · exact ⟨![1, 3, 0, 2], by decide, fun k => by fin_cases k <;> simp [h0, h1, h2', h3]⟩
  · exact ⟨![1, 2, 0, 3], by decide, fun k => by fin_cases k <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination -hs) h2
  · exact absurd (by linear_combination hs) h2
  · exact ⟨![0, 3, 1, 2], by decide, fun k => by fin_cases k <;> simp [h0, h1, h2', h3]⟩
  · exact ⟨![0, 2, 1, 3], by decide, fun k => by fin_cases k <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination -hs) h2
  · exact ⟨![0, 1, 2, 3], by decide, fun k => by fin_cases k <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination -hs) h2
  · exact absurd (by linear_combination -hs) h2
  · exact absurd (by linear_combination -hs) h4

theorem exists_frame_diag {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (x : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) :
    ∃ (P : GL (Fin 4) K) (ε : Fin 4 → K),
      ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (∀ k, ε k = 1 ∨ ε k = -1) ∧
      (x : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
        (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ε := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hpq : 2 ∣ p ^ f + 1 := even_iff_two_dvd.1 ((h.prime.odd_of_ne_two hp2).pow).add_one
  have hxmem : x ∈ primeFormUnitary h (idGram K 4) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [map_bar_eq h]; exact hxU
  let X : primeFormUnitary h (idGram K 4) := ⟨x, hxmem⟩
  have hX2 : X ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext hx2
  obtain ⟨P, hP⟩ := KFU.exists_unitary_conj_diag h Nat.prime_two hpq (Subgroup.zpowers X)
    (fun a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self X m n).eq)
    (fun a ha => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hX2, _root_.one_zpow])
  have hD := hP X (Subgroup.mem_zpowers X)
  set D : Matrix (Fin 4) (Fin 4) K :=
    (((P⁻¹ * X * P : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hDdef
  have hDD : D * D = 1 := by
    have e : (P⁻¹ * X * P) * (P⁻¹ * X * P) = (1 : primeFormUnitary h (idGram K 4)) := by
      calc (P⁻¹ * X * P) * (P⁻¹ * X * P) = P⁻¹ * (X * X) * P := by group
        _ = 1 := by rw [← pow_two, hX2]; group
    have := congrArg (fun u : primeFormUnitary h (idGram K 4) => ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) e
    simpa [hDdef] using this
  have hDeq : D = Matrix.diagonal (fun k => D k k) := hD.diagonal_diag.symm
  refine ⟨(P : GL (Fin 4) K), fun k => D k k, ?_, fun k => ?_, ?_⟩
  · have hP1 := (mem_primeFormUnitary (h := h)).1 P.2
    simp only [idGram, Units.val_one, Matrix.mul_one] at hP1
    rw [map_bar_eq h] at hP1
    exact hP1
  · have := congrFun (congrFun hDD k) k
    rw [hDeq] at this
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact mul_self_eq_one_iff.1 this
  · rw [← hDeq]
    have : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * D = (x : Matrix (Fin 4) (Fin 4) K) * ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      have e : ((P : GL (Fin 4) K)) * (((P⁻¹ * X * P : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K)) = x * (P : GL (Fin 4) K) := by
        change (P : GL (Fin 4) K) * ((P : GL (Fin 4) K)⁻¹ * x * (P : GL (Fin 4) K)) = x * (P : GL (Fin 4) K)
        group
      simpa [hDdef] using congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) e
    exact this.symm


theorem exists_frame {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (x : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (htr : (x : Matrix (Fin 4) (Fin 4) K).trace = 0) :
    ∃ P : GL (Fin 4) K,
      ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (x : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
        (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![-1, -1, 1, 1] := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  obtain ⟨P, ε, hPU, hε, hxP⟩ := exists_frame_diag hp hp2 hK x hxU hx2
  have hx' : (x : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ε * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hxP, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hs : ε 0 + ε 1 + ε 2 + ε 3 = 0 := by
    have h1 : (x : Matrix (Fin 4) (Fin 4) K).trace = (Matrix.diagonal ε).trace := by
      rw [hx', Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [htr, Matrix.trace_diagonal, Fin.sum_univ_four] at h1
    exact h1.symm
  obtain ⟨τ, hτ, hετ⟩ := exists_sort h2 ε hε hs
  set Pm : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K).submatrix id τ with hPm
  have hU' : (Pm.map (· ^ (p ^ f)))ᵀ * Pm = 1 := submatrix_unitary _ hPU τ hτ
  have hU'' : Pm * (Pm.map (· ^ (p ^ f)))ᵀ = 1 := mul_eq_one_comm.mp hU'
  refine ⟨⟨Pm, (Pm.map (· ^ (p ^ f)))ᵀ, hU'', hU'⟩, hU', ?_⟩
  show (x : Matrix (Fin 4) (Fin 4) K) * Pm = Pm * Matrix.diagonal ![-1, -1, 1, 1]
  ext r k
  have e1 := congrFun (congrFun hxP r) (τ k)
  rw [Matrix.mul_diagonal] at e1
  rw [Matrix.mul_diagonal, ← hετ k]
  simpa [hPm, Matrix.mul_apply, Matrix.submatrix_apply] using e1

end GenLocU4ExtFrame
end CFSG.GH74.Generic.BProg.B2
