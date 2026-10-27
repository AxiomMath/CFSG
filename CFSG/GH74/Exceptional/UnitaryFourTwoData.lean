module

public import CFSG.Fischer.Classification.PartIII.Beta.Data
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.GH74.Exceptional

open Matrix CFSG.Fischer CFSG.Fischer.Classification.Beta

abbrev SpMat3 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)

@[expose] def sp43Mat : Fin 45 → SpMat3 :=
  ![
    fromBlocks !![0, 0; 0, 0] !![0, 1; 2, 0] !![0, 2; 1, 0] !![0, 0; 0, 0],
    fromBlocks !![0, 0; 1, 0] !![0, 1; 2, 0] !![0, 2; 1, 0] !![0, 1; 0, 0],
    fromBlocks !![0, 0; 2, 0] !![0, 1; 2, 0] !![0, 2; 1, 0] !![0, 2; 0, 0],
    fromBlocks !![1, 0; 0, 2] !![0, 0; 0, 0] !![0, 1; 2, 0] !![1, 0; 0, 2],
    fromBlocks !![1, 0; 2, 2] !![0, 0; 0, 0] !![0, 1; 2, 0] !![1, 2; 0, 2],
    fromBlocks !![1, 0; 1, 2] !![0, 0; 0, 0] !![0, 1; 2, 0] !![1, 1; 0, 2],
    fromBlocks !![1, 0; 0, 2] !![0, 1; 2, 0] !![0, 0; 0, 0] !![1, 0; 0, 2],
    fromBlocks !![1, 0; 2, 2] !![0, 1; 2, 0] !![0, 0; 0, 0] !![1, 2; 0, 2],
    fromBlocks !![1, 0; 1, 2] !![0, 1; 2, 0] !![0, 0; 0, 0] !![1, 1; 0, 2],
    fromBlocks !![1, 0; 0, 2] !![0, 0; 0, 0] !![0, 2; 1, 0] !![1, 0; 0, 2],
    fromBlocks !![1, 0; 1, 2] !![0, 0; 0, 0] !![0, 2; 1, 0] !![1, 1; 0, 2],
    fromBlocks !![1, 0; 2, 2] !![0, 0; 0, 0] !![0, 2; 1, 0] !![1, 2; 0, 2],
    fromBlocks !![1, 0; 0, 2] !![0, 2; 1, 0] !![0, 0; 0, 0] !![1, 0; 0, 2],
    fromBlocks !![1, 0; 1, 2] !![0, 2; 1, 0] !![0, 0; 0, 0] !![1, 1; 0, 2],
    fromBlocks !![1, 0; 2, 2] !![0, 2; 1, 0] !![0, 0; 0, 0] !![1, 2; 0, 2],
    fromBlocks !![1, 0; 0, 2] !![0, 0; 0, 0] !![0, 0; 0, 0] !![1, 0; 0, 2],
    fromBlocks !![0, 1; 1, 0] !![0, 0; 0, 0] !![0, 0; 0, 0] !![0, 1; 1, 0],
    fromBlocks !![0, 1; 1, 0] !![0, 2; 1, 0] !![0, 0; 0, 0] !![0, 1; 1, 0],
    fromBlocks !![0, 1; 1, 0] !![0, 1; 2, 0] !![0, 0; 0, 0] !![0, 1; 1, 0],
    fromBlocks !![0, 1; 1, 0] !![0, 0; 0, 0] !![0, 2; 1, 0] !![0, 1; 1, 0],
    fromBlocks !![0, 1; 2, 0] !![0, 2; 1, 0] !![0, 2; 1, 0] !![0, 2; 1, 0],
    fromBlocks !![0, 1; 0, 0] !![0, 1; 2, 0] !![0, 2; 1, 0] !![0, 0; 1, 0],
    fromBlocks !![0, 1; 1, 0] !![0, 0; 0, 0] !![0, 1; 2, 0] !![0, 1; 1, 0],
    fromBlocks !![0, 1; 0, 0] !![0, 2; 1, 0] !![0, 1; 2, 0] !![0, 0; 1, 0],
    fromBlocks !![0, 1; 2, 0] !![0, 1; 2, 0] !![0, 1; 2, 0] !![0, 2; 1, 0],
    fromBlocks !![1, 0; 2, 2] !![0, 0; 0, 0] !![0, 0; 0, 0] !![1, 2; 0, 2],
    fromBlocks !![1, 2; 2, 2] !![0, 1; 2, 0] !![0, 1; 2, 0] !![1, 2; 2, 2],
    fromBlocks !![1, 2; 1, 2] !![0, 2; 1, 0] !![0, 1; 2, 0] !![1, 1; 2, 2],
    fromBlocks !![1, 2; 0, 2] !![0, 0; 0, 0] !![0, 1; 2, 0] !![1, 0; 2, 2],
    fromBlocks !![1, 2; 1, 2] !![0, 1; 2, 0] !![0, 2; 1, 0] !![1, 1; 2, 2],
    fromBlocks !![1, 2; 2, 2] !![0, 2; 1, 0] !![0, 2; 1, 0] !![1, 2; 2, 2],
    fromBlocks !![1, 2; 0, 2] !![0, 0; 0, 0] !![0, 2; 1, 0] !![1, 0; 2, 2],
    fromBlocks !![1, 2; 0, 2] !![0, 1; 2, 0] !![0, 0; 0, 0] !![1, 0; 2, 2],
    fromBlocks !![1, 2; 0, 2] !![0, 2; 1, 0] !![0, 0; 0, 0] !![1, 0; 2, 2],
    fromBlocks !![1, 2; 0, 2] !![0, 0; 0, 0] !![0, 0; 0, 0] !![1, 0; 2, 2],
    fromBlocks !![1, 0; 1, 2] !![0, 0; 0, 0] !![0, 0; 0, 0] !![1, 1; 0, 2],
    fromBlocks !![1, 1; 1, 2] !![0, 1; 2, 0] !![0, 1; 2, 0] !![1, 1; 1, 2],
    fromBlocks !![1, 1; 0, 2] !![0, 0; 0, 0] !![0, 1; 2, 0] !![1, 0; 1, 2],
    fromBlocks !![1, 1; 2, 2] !![0, 2; 1, 0] !![0, 1; 2, 0] !![1, 2; 1, 2],
    fromBlocks !![1, 1; 0, 2] !![0, 1; 2, 0] !![0, 0; 0, 0] !![1, 0; 1, 2],
    fromBlocks !![1, 1; 0, 2] !![0, 0; 0, 0] !![0, 0; 0, 0] !![1, 0; 1, 2],
    fromBlocks !![1, 1; 0, 2] !![0, 2; 1, 0] !![0, 0; 0, 0] !![1, 0; 1, 2],
    fromBlocks !![1, 1; 2, 2] !![0, 1; 2, 0] !![0, 2; 1, 0] !![1, 2; 1, 2],
    fromBlocks !![1, 1; 0, 2] !![0, 0; 0, 0] !![0, 2; 1, 0] !![1, 0; 1, 2],
    fromBlocks !![1, 1; 1, 2] !![0, 2; 1, 0] !![0, 2; 1, 0] !![1, 1; 1, 2]]

@[expose] def spMul (A B : SpMat3) : SpMat3 :=
  Matrix.of fun a b => A a (.inl 0) * B (.inl 0) b + A a (.inl 1) * B (.inl 1) b +
    A a (.inr 0) * B (.inr 0) b + A a (.inr 1) * B (.inr 1) b

theorem spMul_eq (A B : SpMat3) : spMul A B = A * B := by
  ext a b
  simp [spMul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, add_assoc]

@[expose] def spBEq (A B : SpMat3) : Bool :=
  A (.inl 0) (.inl 0) == B (.inl 0) (.inl 0) &&
    A (.inl 0) (.inl 1) == B (.inl 0) (.inl 1) &&
    A (.inl 0) (.inr 0) == B (.inl 0) (.inr 0) &&
    A (.inl 0) (.inr 1) == B (.inl 0) (.inr 1) &&
    A (.inl 1) (.inl 0) == B (.inl 1) (.inl 0) &&
    A (.inl 1) (.inl 1) == B (.inl 1) (.inl 1) &&
    A (.inl 1) (.inr 0) == B (.inl 1) (.inr 0) &&
    A (.inl 1) (.inr 1) == B (.inl 1) (.inr 1) &&
    A (.inr 0) (.inl 0) == B (.inr 0) (.inl 0) &&
    A (.inr 0) (.inl 1) == B (.inr 0) (.inl 1) &&
    A (.inr 0) (.inr 0) == B (.inr 0) (.inr 0) &&
    A (.inr 0) (.inr 1) == B (.inr 0) (.inr 1) &&
    A (.inr 1) (.inl 0) == B (.inr 1) (.inl 0) &&
    A (.inr 1) (.inl 1) == B (.inr 1) (.inl 1) &&
    A (.inr 1) (.inr 0) == B (.inr 1) (.inr 0) &&
    A (.inr 1) (.inr 1) == B (.inr 1) (.inr 1)

theorem spBEq_iff {A B : SpMat3} : spBEq A B = true ↔ A = B := by
  constructor
  · intro h
    simp only [spBEq, Bool.and_eq_true, beq_iff_eq] at h
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp_all
  · rintro rfl
    simp [spBEq]

@[expose] def sympCheck : Bool :=
  (List.finRange 45).all fun i =>
    spBEq (spMul (spMul (sp43Mat i)ᵀ (fromBlocks 0 1 (-1) 0)) (sp43Mat i)) (fromBlocks 0 1 (-1) 0)

@[expose] def sqCheck : Bool :=
  (List.finRange 45).all fun i => spBEq (spMul (sp43Mat i) (sp43Mat i)) 1

@[expose] def injCheck : Bool :=
  (List.finRange 45).all fun i => (List.finRange 45).all fun j =>
    !(spBEq (sp43Mat i) (sp43Mat j) || spBEq (sp43Mat i) (-sp43Mat j)) || i == j

@[expose] def tauRow (i : Fin 45) : Bool :=
  (List.finRange 45).all fun j =>
    spBEq (spMul (spMul (sp43Mat i) (sp43Mat j)) (sp43Mat i)) (sp43Mat (uIdx (tU (uPt i) (uPt j)))) ||
      spBEq (spMul (spMul (sp43Mat i) (sp43Mat j)) (sp43Mat i))
        (-sp43Mat (uIdx (tU (uPt i) (uPt j))))

@[expose] def tauRows (a n : ℕ) : Bool :=
  (List.range' a n).all fun k => if h : k < 45 then tauRow ⟨k, h⟩ else true

theorem sympCheck_eq : sympCheck = true := by decide +kernel

theorem sqCheck_eq : sqCheck = true := by decide +kernel

theorem injCheck_eq : injCheck = true := by decide +kernel

theorem tauRows_zero : tauRows 0 9 = true := by decide +kernel

theorem tauRows_nine : tauRows 9 9 = true := by decide +kernel

theorem tauRows_eighteen : tauRows 18 9 = true := by decide +kernel

theorem tauRows_twentySeven : tauRows 27 9 = true := by decide +kernel

theorem tauRows_thirtySix : tauRows 36 9 = true := by decide +kernel

theorem sp43Mat_symp (i : Fin 45) :
    (sp43Mat i)ᵀ * fromBlocks 0 1 (-1) 0 * sp43Mat i = fromBlocks 0 1 (-1) 0 := by
  have h := List.all_eq_true.mp sympCheck_eq i (List.mem_finRange i)
  rwa [spBEq_iff, spMul_eq, spMul_eq] at h

theorem sp43Mat_sq (i : Fin 45) : sp43Mat i * sp43Mat i = 1 := by
  have h := List.all_eq_true.mp sqCheck_eq i (List.mem_finRange i)
  rwa [spBEq_iff, spMul_eq] at h

theorem sp43Mat_inj {i j : Fin 45} (h : sp43Mat i = sp43Mat j ∨ sp43Mat i = -sp43Mat j) :
    i = j := by
  have h' := List.all_eq_true.mp (List.all_eq_true.mp injCheck_eq i (List.mem_finRange i)) j
    (List.mem_finRange j)
  rcases h with h | h
  · simpa [(spBEq_iff).mpr h] using h'
  · simpa [(spBEq_iff).mpr h] using h'

theorem tauRow_eq (i : Fin 45) : tauRow i = true := by
  have key : ∀ a, tauRows a 9 = true → a ≤ i.val → i.val < a + 9 → tauRow i = true := by
    intro a h h1 h2
    have := List.all_eq_true.mp h i.val (List.mem_range'_1.mpr ⟨h1, h2⟩)
    simpa [i.isLt] using this
  have hi := i.isLt
  rcases (by omega : i.val < 9 ∨ (9 ≤ i.val ∧ i.val < 18) ∨ (18 ≤ i.val ∧ i.val < 27) ∨
      (27 ≤ i.val ∧ i.val < 36) ∨ 36 ≤ i.val) with h | h | h | h | h
  · exact key 0 tauRows_zero (Nat.zero_le _) h
  · exact key 9 tauRows_nine h.1 h.2
  · exact key 18 tauRows_eighteen h.1 h.2
  · exact key 27 tauRows_twentySeven h.1 h.2
  · exact key 36 tauRows_thirtySix h (by omega)

theorem sp43Mat_tau (i j : Fin 45) :
    sp43Mat i * sp43Mat j * sp43Mat i = sp43Mat (uIdx (tU (uPt i) (uPt j))) ∨
      sp43Mat i * sp43Mat j * sp43Mat i = -sp43Mat (uIdx (tU (uPt i) (uPt j))) := by
  have h := List.all_eq_true.mp (tauRow_eq i) j (List.mem_finRange j)
  simp only [Bool.or_eq_true, spBEq_iff, spMul_eq] at h
  exact h

end CFSG.GH74.Exceptional
