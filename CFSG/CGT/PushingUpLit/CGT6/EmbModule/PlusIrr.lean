module

public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix

section Plus

variable {K : Type*} [Field K]

@[expose] def rowMat (r : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := Matrix.of ![r, 0]

@[expose] def rowMat' (r : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := Matrix.of ![0, r]

theorem rowMat_mul_transpose (r : Fin 2 → K) (h : Matrix (Fin 2) (Fin 2) K) :
    rowMat r * h.transpose = rowMat (h.mulVec r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem rowMat_add (r s : Fin 2 → K) : rowMat (r + s) = rowMat r + rowMat s := by
  ext i j
  fin_cases i <;> simp [rowMat]

theorem rowMat_sub (r s : Fin 2 → K) : rowMat (r - s) = rowMat r - rowMat s := by
  ext i j
  fin_cases i <;> simp [rowMat]

theorem eq_rowMat_add (M : Matrix (Fin 2) (Fin 2) K) : M = rowMat (M 0) + rowMat' (M 1) := by
  ext i j
  fin_cases i <;> simp [rowMat, rowMat']

theorem natPlus_irreducible_of_field (W : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K)))
    (hW : ∀ g h : SpecialLinearGroup (Fin 2) K, ∀ m ∈ W,
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd m *
        (h : Matrix (Fin 2) (Fin 2) K).transpose) ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  let P : Matrix (Fin 2) (Fin 2) K → Prop := fun M => Multiplicative.ofAdd M ∈ W
  have hPadd : ∀ A B, P A → P B → P (A + B) := fun A B hA hB => by
    show Multiplicative.ofAdd (A + B) ∈ W
    rw [ofAdd_add]
    exact W.mul_mem hA hB
  have hPsub : ∀ A B, P A → P B → P (A - B) := fun A B hA hB => by
    show Multiplicative.ofAdd (A - B) ∈ W
    rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg]
    exact W.mul_mem hA (W.inv_mem hB)
  have hact : ∀ (g h : SpecialLinearGroup (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K), P M →
      P ((g : Matrix (Fin 2) (Fin 2) K) * M * (h : Matrix (Fin 2) (Fin 2) K).transpose) :=
    fun g h M hM => hW g h _ hM
  let uSL : K → SpecialLinearGroup (Fin 2) K := fun x =>
    ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩
  let lSL : K → SpecialLinearGroup (Fin 2) K := fun x =>
    ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩
  let wSL : SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let S : (Fin 2 → K) → Prop := fun r => P (rowMat r)
  have hSadd : ∀ r s, S r → S s → S (r + s) := fun r s hr hs => by
    show P (rowMat (r + s))
    rw [rowMat_add]
    exact hPadd _ _ hr hs
  have hSsub : ∀ r s, S r → S s → S (r - s) := fun r s hr hs => by
    show P (rowMat (r - s))
    rw [rowMat_sub]
    exact hPsub _ _ hr hs
  have hactR : ∀ (h : SpecialLinearGroup (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K), P M →
      P (M * (h : Matrix (Fin 2) (Fin 2) K).transpose) := fun h M hM => by
    simpa using hact 1 h M hM
  have hactL : ∀ (g : SpecialLinearGroup (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K), P M →
      P ((g : Matrix (Fin 2) (Fin 2) K) * M) := fun g M hM => by
    simpa using hact g 1 M hM
  have hSact : ∀ (h : SpecialLinearGroup (Fin 2) K) r, S r →
      S ((h : Matrix (Fin 2) (Fin 2) K).mulVec r) := fun h r hr => by
    have := hactR h _ hr
    rw [rowMat_mul_transpose] at this
    exact this
  have hu : ∀ (x : K) (r : Fin 2 → K), ((uSL x : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec r - r = ![x * r 1, 0] := by
    intro x r
    funext j
    fin_cases j <;> simp [uSL, dotProduct, Fin.sum_univ_two]
  have hl : ∀ (x : K) (r : Fin 2 → K), ((lSL x : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec r - r = ![0, x * r 0] := by
    intro x r
    funext j
    fin_cases j <;> simp [lSL, dotProduct, Fin.sum_univ_two]
  have hSu : ∀ r, S r → ∀ x : K, S ![x * r 1, 0] := fun r hr x => by
    rw [← hu x r]
    exact hSsub _ _ (hSact _ r hr) hr
  have hSl : ∀ r, S r → ∀ x : K, S ![0, x * r 0] := fun r hr x => by
    rw [← hl x r]
    exact hSsub _ _ (hSact _ r hr) hr
  have hcase : ∀ r, S r → r 1 ≠ 0 → ∀ s, S s := by
    intro r hr h1 s
    have hA : ∀ t : K, S ![t, 0] := fun t => by
      have := hSu r hr (t / r 1)
      rwa [div_mul_cancel₀ _ h1] at this
    have hB : ∀ y : K, S ![0, y] := fun y => by
      have := hSl ![1, 0] (hA 1) y
      simpa using this
    have : s = ![s 0, 0] + ![0, s 1] := by
      funext j
      fin_cases j <;> simp
    rw [this]
    exact hSadd _ _ (hA _) (hB _)
  have hrow : ∀ r, S r → r ≠ 0 → ∀ s, S s := by
    intro r hr hr0 s
    by_cases h1 : r 1 = 0
    · have h0 : r 0 ≠ 0 := fun h => hr0 (by funext j; fin_cases j <;> simp [h, h1])
      have h01 : S ![0, 1] := by
        have := hSl r hr (1 / r 0)
        rwa [div_mul_cancel₀ _ h0] at this
      exact hcase _ h01 (by simp) s
    · exact hcase r hr h1 s
  obtain ⟨m, hm, hm1⟩ : ∃ m ∈ W, m ≠ 1 := by
    by_contra h
    push Not at h
    exact hbot ((Subgroup.eq_bot_iff_forall W).2 h)
  have hM : P (Multiplicative.toAdd m) := by
    show Multiplicative.ofAdd (Multiplicative.toAdd m) ∈ W
    rwa [ofAdd_toAdd]
  have hM0 : Multiplicative.toAdd m ≠ 0 := fun h => hm1 (by
    rw [← ofAdd_toAdd m, h]
    rfl)
  set M := Multiplicative.toAdd m with hMdef
  have hD : P (rowMat (M 1)) := by
    have h1 := hactL (uSL 1) M hM
    have h2 := hPsub _ _ h1 hM
    have e : ((uSL 1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M - M =
        rowMat (M 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uSL, rowMat, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two]
    rwa [e] at h2
  have hSall : ∀ s, S s := by
    by_cases h1 : M 1 = 0
    · have hMr : M = rowMat (M 0) := by
        rw [eq_rowMat_add M, h1]
        ext i j
        fin_cases i <;> simp [rowMat, rowMat']
      have h0 : M 0 ≠ 0 := fun h => hM0 (by
        rw [hMr, h]
        ext i j
        fin_cases i <;> simp [rowMat])
      have : S (M 0) := by
        show P (rowMat (M 0))
        rw [← hMr]
        exact hM
      exact hrow _ this h0
    · exact hrow _ hD h1
  refine (Subgroup.eq_top_iff' W).2 fun m' => ?_
  have h2 : P (rowMat' (Multiplicative.toAdd m' 1)) := by
    have h3 := hactL wSL _ (hSall (-(Multiplicative.toAdd m' 1)))
    have e : ((wSL : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        rowMat (-(Multiplicative.toAdd m' 1)) = rowMat' (Multiplicative.toAdd m' 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [wSL, rowMat, rowMat', Matrix.mul_apply,
        Fin.sum_univ_two]
    rwa [e] at h3
  have h4 : P (Multiplicative.toAdd m') := by
    have := hPadd _ _ (hSall (Multiplicative.toAdd m' 0)) h2
    rwa [← eq_rowMat_add] at this
  have h5 : Multiplicative.ofAdd (Multiplicative.toAdd m') ∈ W := h4
  rwa [ofAdd_toAdd] at h5

end Plus

theorem natPlus_irreducible (n : ℕ)
    (W : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))))
    (hW : ∀ g, ∀ m ∈ W, omegaPlusAct n g m ∈ W) : W = ⊥ ∨ W = ⊤ :=
  natPlus_irreducible_of_field W fun g h m hm => hW (g, h) m hm

end CFSG.CGT.PushingUpLit.CGT6
