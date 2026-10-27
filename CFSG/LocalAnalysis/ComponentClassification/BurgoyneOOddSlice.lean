module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEigen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFamily
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceAct
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceDef
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG

variable {K : Type} [Field K] {d : ℕ}

theorem card_jSet (hd : 2 ≤ d) : (jSet : Finset (Fin d)).card = 2 := by
  rw [show (jSet : Finset (Fin d)) = {⟨0, by omega⟩, ⟨1, by omega⟩} from by
    ext i
    simp only [mem_jSet, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega]
  exact Finset.card_pair (by simp [Fin.ext_iff])

theorem eq_one_of_forall_mulVec {M : Matrix (Fin d) (Fin d) K} (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one, Matrix.col_apply] at e
  rw [e, Pi.single_apply, one_apply]

theorem eigM_neg (A : Matrix (Fin d) (Fin d) K) : eigM (-A) = eigP A := by
  ext v
  rw [mem_eigM, mem_eigP, neg_mulVec, neg_inj]

theorem eigP_neg (A : Matrix (Fin d) (Fin d) K) : eigP (-A) = eigM A := by
  ext v
  rw [mem_eigM, mem_eigP, neg_mulVec, neg_eq_iff_eq_neg]

theorem sliceW_of_nf {b : ℕ} (hab : 2 + b = d) (hb : 5 ≤ b) {R : Matrix (Fin d) (Fin d) K}
    {c : Fin 2 ⊕ Fin b → Fin d → K} {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (h0 : c (.inl 0) ⬝ᵥ R *ᵥ c (.inl 0) = α) (h1 : c (.inl 1) ⬝ᵥ R *ᵥ c (.inl 1) = β)
    (h2 : c (.inr ⟨0, by omega⟩) ⬝ᵥ R *ᵥ c (.inr ⟨0, by omega⟩) = -α)
    (h3 : c (.inr ⟨1, by omega⟩) ⬝ᵥ R *ᵥ c (.inr ⟨1, by omega⟩) = -β)
    (hr : ∀ j : Fin b, 2 ≤ (j : ℕ) → c (.inr j) ⬝ᵥ R *ᵥ c (.inr j) = -α) :
    OSliceW (by omega : 4 ≤ d) (famW R hab c) α (β / α) ∧ BlockOK K (famW R hab c) jSetᶜ := by
  have hval : ∀ l : Fin d, famW R hab c l = if (l : ℕ) = 0 then α else if (l : ℕ) = 1 then β
      else if (l : ℕ) = 3 then -β else -α := by
    intro l
    obtain ⟨x, rfl⟩ := (sumFin hab).surjective l
    rw [famW_sumFin]
    rcases x with i | j
    · rw [sumFin_inl]
      fin_cases i
      · simpa using h0
      · simpa using h1
    · rw [sumFin_inr]
      simp only
      by_cases hj0 : (j : ℕ) = 0
      · have : j = ⟨0, by omega⟩ := Fin.ext hj0
        rw [this, h2]
        simp
      · by_cases hj1 : (j : ℕ) = 1
        · have : j = ⟨1, by omega⟩ := Fin.ext hj1
          rw [this, h3]
          simp
        · rw [hr j (by omega)]
          have e1 : 2 + (j : ℕ) ≠ 0 := by omega
          have e2 : 2 + (j : ℕ) ≠ 1 := by omega
          have e3 : 2 + (j : ℕ) ≠ 3 := by omega
          simp only [e1, e2, e3, ↓reduceIte]
  refine ⟨⟨hα, div_ne_zero hβ hα, fun i => ?_⟩, ?_⟩
  · rw [hval]
    fin_cases i <;> simp [qW] <;> field_simp
  · have hcard : (jSet : Finset (Fin d))ᶜ.card = b := by
      rw [Finset.card_compl, Fintype.card_fin, card_jSet (by omega)]
      omega
    have hmemc : ∀ l : Fin d, l ∈ (jSet : Finset (Fin d))ᶜ ↔ 2 ≤ (l : ℕ) := by
      intro l
      rw [Finset.mem_compl, mem_jSet]
      omega
    refine ⟨by omega, fun h => by omega, (jSet : Finset (Fin d))ᶜ.filter fun l => (l : ℕ) ≠ 3,
      Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · have hsub : ({⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩} : Finset (Fin d)) ⊆
          (jSet : Finset (Fin d))ᶜ.filter fun l => (l : ℕ) ≠ 3 := by
        intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rw [Finset.mem_filter, hmemc]
        rcases hl with rfl | rfl | rfl <;> simp
      refine le_trans ?_ (Finset.card_le_card hsub)
      rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
        Finset.card_pair (by simp [Fin.ext_iff])]
    · intro i hi j hj
      rw [Finset.mem_filter, hmemc] at hi hj
      rw [hval, hval]
      have e1 : (i : ℕ) ≠ 0 := by omega
      have e2 : (i : ℕ) ≠ 1 := by omega
      have e3 : (j : ℕ) ≠ 0 := by omega
      have e4 : (j : ℕ) ≠ 1 := by omega
      simp only [e1, e2, e3, e4, hi.2, hj.2, ↓reduceIte]
    · intro x hx y hy hx' hy'
      rw [Finset.mem_filter, not_and, not_not] at hx' hy'
      exact Fin.ext ((hx' hx).trans (hy' hy).symm)

end CFSG.ComponentClassification.Burgoyne.O
