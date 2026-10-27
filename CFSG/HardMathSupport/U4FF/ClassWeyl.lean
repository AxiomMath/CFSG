module

public import Mathlib.GroupTheory.Coxeter.Length

public section

namespace CFSG.HardMathSupport.U4FF

abbrev WB : Type := (CoxeterMatrix.B 2).Group

noncomputable abbrev csB : CoxeterSystem (CoxeterMatrix.B 2) WB :=
  (CoxeterMatrix.B 2).toCoxeterSystem

noncomputable abbrev s0 : WB := csB.simple 0

noncomputable abbrev s1 : WB := csB.simple 1

theorem s0_mul_s0 : s0 * s0 = 1 := csB.simple_mul_simple_self 0

theorem s1_mul_s1 : s1 * s1 = 1 := csB.simple_mul_simple_self 1

theorem s0_mul_s0_mul (w : WB) : s0 * (s0 * w) = w := by
  rw [← mul_assoc, s0_mul_s0, one_mul]

theorem s1_mul_s1_mul (w : WB) : s1 * (s1 * w) = w := by
  rw [← mul_assoc, s1_mul_s1, one_mul]

theorem braid_B2 : s0 * s1 * s0 * s1 = s1 * s0 * s1 * s0 := by
  have hM : (CoxeterMatrix.B 2) 0 1 = 4 := by decide
  have h4 : (s0 * s1) ^ 4 = 1 := by
    have h := csB.simple_mul_simple_pow 0 1
    rwa [hM] at h
  have hxx : s0 * s1 * s0 * s1 * (s0 * s1 * s0 * s1) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hxy : s0 * s1 * s0 * s1 * (s1 * s0 * s1 * s0) = 1 := by
    simp only [mul_assoc, s0_mul_s0_mul, s1_mul_s1_mul, s0_mul_s0]
  exact (mul_left_cancel (hxy.trans hxx.symm)).symm

theorem braid_B2' : s0 * (s1 * (s0 * s1)) = s1 * (s0 * (s1 * s0)) := by
  simpa only [mul_assoc] using braid_B2

theorem braid_B2_tail (X : WB) :
    s0 * (s1 * (s0 * (s1 * X))) = s1 * (s0 * (s1 * (s0 * X))) := by
  have h := congrArg (· * X) braid_B2
  simpa only [mul_assoc] using h

@[expose] def pA : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def pB : Equiv.Perm (Fin 4) := Equiv.swap 1 2

theorem isLiftable_AB : (CoxeterMatrix.B 2).IsLiftable ![pA, pB] := by
  unfold CoxeterMatrix.IsLiftable
  decide

@[expose] noncomputable def permOf : WB →* Equiv.Perm (Fin 4) :=
  csB.lift ⟨![pA, pB], isLiftable_AB⟩

theorem permOf_s0 : permOf s0 = pA := csB.lift_apply_simple isLiftable_AB 0

theorem permOf_s1 : permOf s1 = pB := csB.lift_apply_simple isLiftable_AB 1

@[expose] noncomputable def wTab : Fin 8 → WB :=
  ![1, s0, s1, s0 * s1, s1 * s0, s0 * s1 * s0, s1 * s0 * s1, s0 * s1 * s0 * s1]

@[expose] def lmulTab : Fin 2 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![2, 4, 0, 6, 1, 7, 3, 5]]

@[expose] def permTab : Fin 8 → Equiv.Perm (Fin 4) :=
  ![1, pA, pB, pA * pB, pB * pA, pA * pB * pA, pB * pA * pB, pA * pB * pA * pB]

@[expose] def lenTab : Fin 8 → ℕ := ![0, 1, 1, 2, 2, 3, 3, 4]

@[expose] def wordTab : Fin 8 → List (Fin 2) :=
  ![[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1]]

theorem permTab_injective : Function.Injective permTab := by
  decide

theorem permOf_wTab (i : Fin 8) : permOf (wTab i) = permTab i := by
  fin_cases i <;>
    simp [-CoxeterMatrix.toCoxeterSystem_simple, wTab, permTab, map_mul, permOf_s0, permOf_s1]

theorem wTab_injective : Function.Injective wTab := by
  intro i j h
  apply permTab_injective
  rw [← permOf_wTab, ← permOf_wTab, h]

theorem simple_mul_wTab (s : Fin 2) (i : Fin 8) :
    csB.simple s * wTab i = wTab (lmulTab s i) := by
  fin_cases s <;> fin_cases i <;>
    simp [-CoxeterMatrix.toCoxeterSystem_simple, wTab, lmulTab, mul_assoc, braid_B2',
      braid_B2_tail, s0_mul_s0, s1_mul_s1, s0_mul_s0_mul, s1_mul_s1_mul]

theorem exists_wTab (w : WB) : ∃ i, w = wTab i := by
  refine csB.simple_induction_left (p := fun x : WB => ∃ i, x = wTab i) w ⟨0, ?_⟩ ?_
  · simp [wTab]
  · rintro x i ⟨j, rfl⟩
    exact ⟨lmulTab i j, simple_mul_wTab i j⟩

instance instFiniteWB : Finite WB :=
  Finite.of_surjective wTab fun w => by
    obtain ⟨i, hi⟩ := exists_wTab w
    exact ⟨i, hi.symm⟩

theorem wordProd_wordTab (i : Fin 8) : csB.wordProd (wordTab i) = wTab i := by
  fin_cases i <;>
    simp [-CoxeterMatrix.toCoxeterSystem_simple, wordTab, wTab, CoxeterSystem.wordProd_cons,
      mul_assoc]

theorem wordTab_length : ∀ i : Fin 8, (wordTab i).length = lenTab i := by
  decide

theorem length_wTab_le (i : Fin 8) : csB.length (wTab i) ≤ lenTab i := by
  rw [← wordProd_wordTab i, ← wordTab_length i]
  exact csB.length_wordProd_le _

theorem lmul_lenTab : ∀ (s : Fin 2) (j : Fin 8), lenTab (lmulTab s j) ≤ lenTab j + 1 := by
  decide

theorem wordProd_mem (ω : List (Fin 2)) :
    ∃ j, csB.wordProd ω = wTab j ∧ lenTab j ≤ ω.length := by
  induction ω with
  | nil => exact ⟨0, by simp [wTab], by decide⟩
  | cons s ω ih =>
    obtain ⟨j, hj, hl⟩ := ih
    refine ⟨lmulTab s j, ?_, ?_⟩
    · rw [CoxeterSystem.wordProd_cons, hj]
      exact simple_mul_wTab s j
    · have := lmul_lenTab s j
      simp only [List.length_cons]
      omega

theorem lenTab_le_length (i : Fin 8) : lenTab i ≤ csB.length (wTab i) := by
  obtain ⟨ω, hred, hw⟩ := csB.exists_isReduced (wTab i)
  obtain ⟨j, hj, hl⟩ := wordProd_mem ω
  have hij : i = j := wTab_injective (hw.trans hj)
  calc lenTab i = lenTab j := by rw [hij]
    _ ≤ ω.length := hl
    _ = csB.length (wTab i) := by rw [hw, hred.eq]

theorem length_wTab (i : Fin 8) : csB.length (wTab i) = lenTab i :=
  le_antisymm (length_wTab_le i) (lenTab_le_length i)

abbrev permInvLt (s : Fin 2) (π : Equiv.Perm (Fin 4)) : Prop :=
  (s = 0 → π⁻¹ 0 < π⁻¹ 1 ∧ π⁻¹ 2 < π⁻¹ 3) ∧ (s = 1 → π⁻¹ 1 < π⁻¹ 2)

theorem lmul_length_iff_table : ∀ (s : Fin 2) (i : Fin 8),
    lenTab (lmulTab s i) = lenTab i + 1 ↔ permInvLt s (permTab i) := by
  decide

theorem length_simple_mul_iff (s : Fin 2) (w : WB) :
    csB.length (csB.simple s * w) = csB.length w + 1 ↔ permInvLt s (permOf w) := by
  obtain ⟨i, rfl⟩ := exists_wTab w
  rw [simple_mul_wTab, length_wTab, length_wTab, permOf_wTab]
  exact lmul_length_iff_table s i

noncomputable abbrev w0 : WB := wTab 7

theorem permOf_w0 : permOf w0 = Fin.revPerm := by
  show permOf (wTab 7) = Fin.revPerm
  rw [permOf_wTab]
  decide

end CFSG.HardMathSupport.U4FF
