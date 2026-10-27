module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenInv
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenExtStd
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrSplit

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace GenLocU4Out

open GenLocU4Basic

section Transport

variable {K : Type} [Field K] {p f : ℕ}

theorem map_mul_pow (h : UnitaryFieldData p f K) (M N : Matrix (Fin 4) (Fin 4) K) :
    (M * N).map (· ^ (p ^ f)) = M.map (· ^ (p ^ f)) * N.map (· ^ (p ^ f)) := by
  have := Matrix.map_mul (f := (h.bar : K →+* K)) (L := M) (M := N)
  simpa [GenLocU4Basic.bar_eq_pow h] using this

theorem map_map_pow (h : UnitaryFieldData p f K) (M : Matrix (Fin 4) (Fin 4) K) :
    (M.map (· ^ (p ^ f))).map (· ^ (p ^ f)) = M := by
  ext i j
  simp [Matrix.map_apply, pow_pow_card h]

theorem map_one_pow (hq0 : p ^ f ≠ 0) : (1 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.map_apply, hij, zero_pow hq0]

theorem unitary_facts (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hq0 : p ^ f ≠ 0) :
    U * (U.map (· ^ (p ^ f)))ᵀ = 1 ∧ Uᵀ * U.map (· ^ (p ^ f)) = 1 ∧ U.map (· ^ (p ^ f)) * Uᵀ = 1 := by
  have h1 : (U.map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  have h3 : Uᵀ * U.map (· ^ (p ^ f)) = 1 := by
    have e : ((U.map (· ^ (p ^ f)))ᵀ * U).map (· ^ (p ^ f)) = Uᵀ * U.map (· ^ (p ^ f)) := by
      rw [map_mul_pow h, ← Matrix.transpose_map, map_map_pow h]
    rw [← e, h1, map_one_pow hq0]
  exact ⟨mul_eq_one_comm.1 h1, h3, mul_eq_one_comm.1 h3⟩

@[expose] noncomputable def cUaut (h : UnitaryFieldData p f K) (U : Matrix (Fin 4) (Fin 4) K)
    (hU : IsUnitaryU (p ^ f) U) : MulAut ↥(StatedSU 4 (p ^ f) K) :=
  GenLocDiagU.conjSUHom h 4
    ⟨⟨U, (U.map (· ^ (p ^ f)))ᵀ, mul_eq_one_comm.1 hU, hU⟩, by
      rw [mem_primeFormUnitary]
      simp only [idGram, Units.val_one, Matrix.mul_one]
      exact hU⟩

theorem cUaut_coe (h : UnitaryFieldData p f K) (U : Matrix (Fin 4) (Fin 4) K) (hU : IsUnitaryU (p ^ f) U)
    (g : ↥(StatedSU 4 (p ^ f) K)) :
    (((cUaut h U hU g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (U.map (· ^ (p ^ f)))ᵀ := by
  unfold cUaut
  rw [GenLocDiagU.coe_conjSUHom]
  simp only [Units.val_mul]
  rfl

theorem fixOut_conj (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hq0 : p ^ f ≠ 0) {M1 : Matrix (Fin 4) (Fin 4) K} (g : ↥(StatedSU 4 (p ^ f) K))
    (hg : FixOut (p ^ f) M1 g) : FixOut (p ^ f) (U * M1 * Uᵀ) (cUaut h U hU g) := by
  obtain ⟨hUUs, hUtUb, hUbUt⟩ := unitary_facts h hU hq0
  have hUs : (U.map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  have k1 : ∀ X : Matrix (Fin 4) (Fin 4) K, Uᵀ * (U.map (· ^ (p ^ f)) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUtUb, Matrix.one_mul]
  have k2 : ∀ X : Matrix (Fin 4) (Fin 4) K, (U.map (· ^ (p ^ f)))ᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUs, Matrix.one_mul]
  unfold FixOut at hg ⊢
  rw [cUaut_coe, map_mul_pow h, map_mul_pow h, Matrix.transpose_map, map_map_pow h]
  simp only [Matrix.mul_assoc, k1, k2]
  rw [← Matrix.mul_assoc M1, hg, Matrix.mul_assoc]

theorem fixIn_conj (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hq0 : p ^ f ≠ 0) {ξ : Matrix (Fin 4) (Fin 4) K} (g : ↥(StatedSU 4 (p ^ f) K))
    (hg : FixIn ((U.map (· ^ (p ^ f)))ᵀ * ξ * U) g) : FixIn ξ (cUaut h U hU g) := by
  obtain ⟨hUUs, hUtUb, hUbUt⟩ := unitary_facts h hU hq0
  have hUs : (U.map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  have k2 : ∀ X : Matrix (Fin 4) (Fin 4) K, (U.map (· ^ (p ^ f)))ᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUs, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin 4) (Fin 4) K, U * ((U.map (· ^ (p ^ f)))ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUUs, Matrix.one_mul]
  unfold FixIn at hg ⊢
  rw [cUaut_coe]
  set G : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hG
  set Us : Matrix (Fin 4) (Fin 4) K := (U.map (· ^ (p ^ f)))ᵀ with hUsdef
  simp only [Matrix.mul_assoc] at hg ⊢
  have e1 := congrArg (fun X => U * X) hg
  simp only [k3] at e1
  calc ξ * (U * (G * Us)) = (ξ * (U * G)) * Us := by simp only [Matrix.mul_assoc]
    _ = U * (G * (Us * (ξ * U))) * Us := by rw [e1]
    _ = U * (G * (Us * ξ)) := by simp only [Matrix.mul_assoc, hUUs, Matrix.mul_one]

theorem xi_sq : (xi : Matrix (Fin 4) (Fin 4) K) * xi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xi, Matrix.mul_apply, Fin.sum_univ_four]

theorem xi_map_pow (hq : Odd (p ^ f)) : (xi : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = xi := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xi, zero_pow hq0, Odd.neg_pow hq]

theorem xi_transpose' : (xi : Matrix (Fin 4) (Fin 4) K)ᵀ = -xi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xi]

theorem xi'_facts (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {U : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) :
    IsUnitaryU (p ^ f) ((U.map (· ^ (p ^ f)))ᵀ * xi * U) ∧
      ((U.map (· ^ (p ^ f)))ᵀ * xi * U) * ((U.map (· ^ (p ^ f)))ᵀ * xi * U) = -1 ∧
      ((U.map (· ^ (p ^ f)))ᵀ * xi * U).map (· ^ (p ^ f)) = Uᵀ * xi * U.map (· ^ (p ^ f)) := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  obtain ⟨hUUs, hUtUb, hUbUt⟩ := unitary_facts h hU hq0
  have hUs : (U.map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  have k2 : ∀ X : Matrix (Fin 4) (Fin 4) K, (U.map (· ^ (p ^ f)))ᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUs, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin 4) (Fin 4) K, U * ((U.map (· ^ (p ^ f)))ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUUs, Matrix.one_mul]
  have hmap : ((U.map (· ^ (p ^ f)))ᵀ * xi * U).map (· ^ (p ^ f)) = Uᵀ * xi * U.map (· ^ (p ^ f)) := by
    rw [map_mul_pow h, map_mul_pow h, Matrix.transpose_map, map_map_pow h, xi_map_pow hq]
  have hsq : ((U.map (· ^ (p ^ f)))ᵀ * xi * U) * ((U.map (· ^ (p ^ f)))ᵀ * xi * U) = -1 := by
    simp only [Matrix.mul_assoc, k3]
    rw [← Matrix.mul_assoc xi xi, xi_sq, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, hUs]
  refine ⟨?_, hsq, hmap⟩
  unfold IsUnitaryU
  rw [hmap, Matrix.transpose_mul, Matrix.transpose_mul, xi_transpose', Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, k3]
  rw [← Matrix.mul_assoc xi xi, xi_sq, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, hUs, neg_neg]

theorem xi'_comm (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {U x : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) (hξx : (xi : Matrix (Fin 4) (Fin 4) K) * x = x * xi) {ε : K} (hε : ε ≠ 0)
    (hxU : x * U = U * (ε • (tT : Matrix (Fin 4) (Fin 4) K))) :
    ((U.map (· ^ (p ^ f)))ᵀ * xi * U) * Matrix.diagonal ![-1, -1, 1, 1] =
      Matrix.diagonal ![-1, -1, 1, 1] * ((U.map (· ^ (p ^ f)))ᵀ * xi * U) := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  obtain ⟨hUUs, hUtUb, hUbUt⟩ := unitary_facts h hU hq0
  have hUs : (U.map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  have k2 : ∀ X : Matrix (Fin 4) (Fin 4) K, (U.map (· ^ (p ^ f)))ᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUs, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin 4) (Fin 4) K, U * ((U.map (· ^ (p ^ f)))ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUUs, Matrix.one_mul]
  have hx' : (U.map (· ^ (p ^ f)))ᵀ * x * U = ε • (tT : Matrix (Fin 4) (Fin 4) K) := by
    rw [Matrix.mul_assoc, hxU, k2]
  have hc1 : ((U.map (· ^ (p ^ f)))ᵀ * xi * U) * ((U.map (· ^ (p ^ f)))ᵀ * x * U) =
      ((U.map (· ^ (p ^ f)))ᵀ * x * U) * ((U.map (· ^ (p ^ f)))ᵀ * xi * U) := by
    simp only [Matrix.mul_assoc, k3]
    rw [← Matrix.mul_assoc xi x, hξx, Matrix.mul_assoc]
  rw [hx', Matrix.mul_smul, Matrix.smul_mul] at hc1
  have hc2 : ((U.map (· ^ (p ^ f)))ᵀ * xi * U) * (tT : Matrix (Fin 4) (Fin 4) K) =
      (tT : Matrix (Fin 4) (Fin 4) K) * ((U.map (· ^ (p ^ f)))ᵀ * xi * U) :=
    smul_right_injective _ hε hc1
  rw [← GenLocU4OutFrDa.neg_tT_eq, Matrix.mul_neg, Matrix.neg_mul, hc2]

theorem xi'_rel (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {U B : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) (hξB : (xi : Matrix (Fin 4) (Fin 4) K) * B = -(B * xi)) {ε : K} (hε : ε ≠ 0)
    (hBU : B * U.map (· ^ (p ^ f)) = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K))) :
    ((U.map (· ^ (p ^ f)))ᵀ * xi * U) * (mD : Matrix (Fin 4) (Fin 4) K) =
      -((mD : Matrix (Fin 4) (Fin 4) K) * ((U.map (· ^ (p ^ f)))ᵀ * xi * U).map (· ^ (p ^ f))) := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  obtain ⟨hUUs, hUtUb, hUbUt⟩ := unitary_facts h hU hq0
  have hUs : (U.map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  obtain ⟨-, -, hmap⟩ := xi'_facts h hq hU
  have hB : B = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K)) * Uᵀ := by
    calc B = B * (U.map (· ^ (p ^ f)) * Uᵀ) := by rw [hUbUt, Matrix.mul_one]
      _ = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K)) * Uᵀ := by rw [← Matrix.mul_assoc, hBU]
  have e := congrArg (fun X => (U.map (· ^ (p ^ f)))ᵀ * X * U.map (· ^ (p ^ f))) hξB
  simp only [hB, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, hUtUb, Matrix.mul_one] at e
  have k2 : ∀ X : Matrix (Fin 4) (Fin 4) K, (U.map (· ^ (p ^ f)))ᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUs, Matrix.one_mul]
  simp only [k2, Matrix.mul_smul, Matrix.smul_mul] at e
  have e3 : ε • ((U.map (· ^ (p ^ f)))ᵀ * (xi * (U * (mD : Matrix (Fin 4) (Fin 4) K)))) =
      ε • (-((mD : Matrix (Fin 4) (Fin 4) K) * (Uᵀ * (xi * U.map (· ^ (p ^ f)))))) := by
    rw [smul_neg]
    exact e
  have e4 := smul_right_injective _ hε e3
  rw [hmap]
  simpa only [Matrix.mul_assoc] using e4

theorem fixOut_smul {q : ℕ} {M : Matrix (Fin 4) (Fin 4) K} {ε : K} (hε : ε ≠ 0) (g : ↥(StatedSU 4 q K)) :
    FixOut q (ε • M) g ↔ FixOut q M g := by
  unfold FixOut
  rw [Matrix.smul_mul, Matrix.mul_smul]
  exact ⟨fun h => smul_right_injective _ hε h, fun h => by rw [h]⟩

theorem B_frame_forms (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {U B : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) {ε : K}
    (hBU : B * U.map (· ^ (p ^ f)) = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K))) :
    B = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K)) * Uᵀ ∧
      B * xi = U * (ε • ((mD : Matrix (Fin 4) (Fin 4) K) *
        ((U.map (· ^ (p ^ f)))ᵀ * xi * U).map (· ^ (p ^ f)))) * Uᵀ := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  obtain ⟨hUUs, hUtUb, hUbUt⟩ := unitary_facts h hU hq0
  obtain ⟨-, -, hmap⟩ := xi'_facts h hq hU
  have hB : B = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K)) * Uᵀ := by
    calc B = B * (U.map (· ^ (p ^ f)) * Uᵀ) := by rw [hUbUt, Matrix.mul_one]
      _ = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K)) * Uᵀ := by rw [← Matrix.mul_assoc, hBU]
  refine ⟨hB, ?_⟩
  rw [hmap]
  conv_lhs => rw [hB]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hUbUt, Matrix.mul_one]

end Transport

theorem outExtGen
    (K : Type) [Field K] [Finite K] (p f : ℕ) : OutExtGen K p f := by
  intro hp hp2 hK hq4 B hBU hBmin hξB Γ hu ht hut
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨x, hxU, hx2, hxtr, hξx, hxB⟩ := exists_split_involution hp hp2 hK hq4 hBU hBmin.1 hξB
  obtain ⟨U, hUU, hxUe, hBUe⟩ :=
    GenLocU4OutFrSplit.exists_split_frame hp hp2 hK hq4 hxU hx2 hxtr hBU hBmin hxB
  obtain ⟨hξ'u, hξ'2, -⟩ := xi'_facts h hq hUU
  obtain ⟨ε2, hε2, hxU2⟩ : ∃ ε2 : K, ε2 ≠ 0 ∧
      x * U = U * (ε2 • (tT : Matrix (Fin 4) (Fin 4) K)) := by
    rcases hxUe with e | e
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact e⟩
    · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by rw [neg_one_smul]; exact e⟩
  obtain ⟨ε, hε, hBU2⟩ : ∃ ε : K, ε ≠ 0 ∧
      B * U.map (· ^ (p ^ f)) = U * (ε • (mD : Matrix (Fin 4) (Fin 4) K)) := by
    rcases hBUe with e | e
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact e⟩
    · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by rw [neg_one_smul]; exact e⟩
  have hcomm := xi'_comm h hq hUU hξx hε2 hxU2
  have hrel := xi'_rel h hq hUU hξB hε hBU2
  obtain ⟨hB, hBxi⟩ := B_frame_forms h hq hUU hBU2
  let Γ' : Subgroup ↥(StatedSU 4 (p ^ f) K) := Γ.comap (cUaut h U hUU).toMonoidHom
  have hmem : ∀ g, g ∈ Γ' ↔ cUaut h U hUU g ∈ Γ := fun g => Iff.rfl
  have h1 : ∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ' := fun g hg => by
    rw [hmem]
    apply hu
    rw [hB]
    exact fixOut_conj h hUU hq0 g ((fixOut_smul hε g).2 hg)
  have h2 : ∀ g, FixIn ((U.map (· ^ (p ^ f)))ᵀ * xi * U) g → g ∈ Γ' := fun g hg => by
    rw [hmem]
    exact ht _ (fixIn_conj h hUU hq0 g hg)
  have h3 : ∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) *
      ((U.map (· ^ (p ^ f)))ᵀ * xi * U).map (· ^ (p ^ f))) g → g ∈ Γ' := fun g hg => by
    rw [hmem]
    apply hut
    rw [hBxi]
    exact fixOut_conj h hUU hq0 g ((fixOut_smul hε g).2 hg)
  have hΓ' := ext_class_std hp hp2 hK hq4 Γ' _ hξ'u hξ'2 hcomm hrel h1 h2 h3
  refine eq_top_iff.2 fun g _ => ?_
  have hg : (cUaut h U hUU).symm g ∈ Γ' := by
    rw [hΓ']
    trivial
  rw [hmem] at hg
  simpa using hg

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
