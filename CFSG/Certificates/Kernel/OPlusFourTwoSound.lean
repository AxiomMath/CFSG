module

public import Certificates.Data.Kernel.OPlusFourTwoK

public section

namespace CFSG.KS.OPlusFourTwo

open CFSG.OPlusFourTwo CFSG.KC.OPlusFourTwo Matrix

theorem mulE_eq (M N : Mat) : mulE M N = M * N := by
  ext i j
  simp [mulE, Matrix.mul_apply, Fin.sum_univ_four]

theorem mulVecE_eq (M : Mat) (v : Fin 4 → ZMod 2) : mulVecE M v = M *ᵥ v := by
  funext i
  simp [mulVecE, mulVec, dotProduct, Fin.sum_univ_four]

theorem cubeE_eq (M : Mat) : cubeE M = M ^ 3 := by
  rw [cubeE, mulE_eq, mulE_eq, pow_three']

theorem pow12E_eq (M : Mat) : pow12E M = M ^ 12 := by
  simp only [pow12E, mulE_eq, cubeE_eq, ← pow_add]

theorem eqE_iff {M N : Mat} : eqE M N = true ↔ M = N := by
  constructor
  · intro h
    simp only [eqE, decide_eq_true_eq] at h
    obtain ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33⟩ := h
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  · rintro rfl
    simp [eqE]

theorem preserves_of_soundB (hv : ∀ v : Fin 4 → ZMod 2, v ∈ vecs) {L : List Mat}
    (h : soundB L = true) : ∀ M ∈ L, PreservesQ0 M := fun M hM v => by
  simp only [soundB, List.all_eq_true, decide_eq_true_eq] at h
  rw [← mulVecE_eq]
  exact h M hM v (hv v)

theorem nodup_of_distinctP {L : List Mat} (h : DistinctP L) : L.Nodup :=
  h.imp fun {M N} hMN hEq => by
    rw [eqE_iff.mpr hEq] at hMN
    exact Bool.false_ne_true hMN.symm

theorem pow_twelve_of_pow12B {L : List Mat} (h : pow12B L = true) : ∀ M ∈ L, M ^ 12 = 1 :=
  fun M hM => by
    rw [← pow12E_eq]
    exact eqE_iff.mp (List.all_eq_true.mp h M hM)

theorem eq_true_of_imp {p : Prop} [Decidable p] {b : Bool} (h : (!(decide p) || b) = true)
    (hp : p) : b = true := by
  simpa [hp] using h

theorem filter_cube_eq (L : List Mat) :
    (L.filter fun M => M ^ 3 = 1) = L.filter fun M => eqE (cubeE M) 1 := by
  apply List.filter_congr
  intro M _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eqE_iff, cubeE_eq]

theorem q0_eq_of {M : Mat} (h : PreservesQ0 M) (v w : Fin 4 → ZMod 2) (hw : M *ᵥ v = w) :
    q0 w = q0 v := hw ▸ h v

theorem mem_of_treeB (hv : ∀ v : Fin 4 → ZMod 2, v ∈ vecs) {L : List Mat} (hT : treeB L = true)
    (M : Mat) (h : PreservesQ0 M) : M ∈ L := by
  have e : ∀ (v w : Fin 4 → ZMod 2) (c : ZMod 2), (∀ i, (M *ᵥ v) i = w i) → q0 v = c →
      q0 w = c := fun v w c hw hc => (q0_eq_of h v w (funext hw)).trans hc
  have c0 := e ![1, 0, 0, 0] (fun i => M i 0) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c1 := e ![0, 1, 0, 0] (fun i => M i 1) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c2 := e ![0, 0, 1, 0] (fun i => M i 2) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c3 := e ![0, 0, 0, 1] (fun i => M i 3) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c01 := e ![1, 1, 0, 0] ((fun i => M i 0) + fun i => M i 1) 1 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c02 := e ![1, 0, 1, 0] ((fun i => M i 0) + fun i => M i 2) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c12 := e ![0, 1, 1, 0] ((fun i => M i 1) + fun i => M i 2) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c03 := e ![1, 0, 0, 1] ((fun i => M i 0) + fun i => M i 3) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c13 := e ![0, 1, 0, 1] ((fun i => M i 1) + fun i => M i 3) 0 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have c23 := e ![0, 0, 1, 1] ((fun i => M i 2) + fun i => M i 3) 1 (fun i => by
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]) (by decide)
  have h0 := eq_true_of_imp (List.all_eq_true.mp hT _ (hv _)) c0
  have h1 := eq_true_of_imp (List.all_eq_true.mp h0 _ (hv _)) ⟨c1, c01⟩
  have h2 := eq_true_of_imp (List.all_eq_true.mp h1 _ (hv _)) ⟨c2, c02, c12⟩
  have h3 := eq_true_of_imp (List.all_eq_true.mp h2 _ (hv _)) ⟨c3, c03, c13, c23⟩
  obtain ⟨N, hN, hEq⟩ := List.any_eq_true.mp h3
  have hM : ofCols (fun i => M i 0) (fun i => M i 1) (fun i => M i 2) (fun i => M i 3) = M := by
    ext i j
    fin_cases j <;> rfl
  rw [← hM, eqE_iff.mp hEq]
  exact hN

end CFSG.KS.OPlusFourTwo
