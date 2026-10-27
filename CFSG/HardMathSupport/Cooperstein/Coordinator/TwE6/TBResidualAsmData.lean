module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualWord
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualData

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

@[expose] def ptCoef {K : Type} [Field K] (ω : K) (b : Bool) : K := if b then ω ^ 2 else ω

theorem ptCoef_false {K : Type} [Field K] (ω : K) : ptCoef ω false = ω := rfl

theorem ptCoef_true {K : Type} [Field K] (ω : K) : ptCoef ω true = ω ^ 2 := rfl

theorem ptCoef_value_eq_zero_iff {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (A B C D : Prop) [Decidable A] [Decidable B] [Decidable C] [Decidable D]
    (hAB : ¬ (A ∧ B)) (hCD : ¬ (C ∧ D)) (hAC : ¬ (A ∧ C)) (hBD : ¬ (B ∧ D)) (hCB : ¬ (C ∧ B))
    (β β' : Bool) :
    (((if A then 1 else 0) + ptCoef ω β' * (if B then 1 else 0) +
        (ptCoef ω β) ^ 2 * ((if C then 1 else 0) + ptCoef ω β' * (if D then 1 else 0)) : K) = 0) ↔
      ¬ ((if (if A ∨ C then 1 else 0) + (if B ∨ D then 1 else 0) = 1 then true
          else if A ∧ D then (β != β') else false) = true) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω
    norm_num at hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have : (3 : K) = 0 := by linear_combination hω
    have h1 : (1 : K) = 0 := by linear_combination this - h2
    exact one_ne_zero h1
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω0
    linear_combination hω - h - h2
  have hc0 : ∀ b, ptCoef ω b ≠ 0 := by
    intro b
    cases b
    · rw [ptCoef_false]; exact hω0
    · rw [ptCoef_true]; exact hω2
  have hAD : ∀ β β' : Bool, (1 + ptCoef ω β ^ 2 * ptCoef ω β' = 0 ↔ β = β') := by
    intro β β'
    cases β <;> cases β'
    · simp only [ptCoef_false]
      refine iff_of_true ?_ trivial
      linear_combination hω3 + h2
    · simp only [ptCoef_false, ptCoef_true]
      refine iff_of_false ?_ (by decide)
      intro h
      apply hω1
      linear_combination h - ω * hω3 - h2
    · simp only [ptCoef_true, ptCoef_false]
      refine iff_of_false ?_ (by decide)
      intro h
      apply hω21
      linear_combination h - ω ^ 2 * hω3 - h2
    · simp only [ptCoef_true]
      refine iff_of_true ?_ trivial
      linear_combination (ω ^ 3 + 1) * hω3 + h2
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D
  · exact absurd ⟨hA, hB⟩ hAB
  · exact absurd ⟨hA, hB⟩ hAB
  · exact absurd ⟨hA, hB⟩ hAB
  · exact absurd ⟨hA, hB⟩ hAB
  · exact absurd ⟨hA, hC⟩ hAC
  · exact absurd ⟨hA, hC⟩ hAC
  ·
    simp [hA, hB, hC, hD, hAD]
  ·
    simp [hA, hB, hC, hD]
  · exact absurd ⟨hC, hD⟩ hCD
  · exact absurd ⟨hC, hB⟩ hCB
  · exact absurd ⟨hB, hD⟩ hBD
  ·
    simp [hA, hB, hC, hD, hc0]
  · exact absurd ⟨hC, hD⟩ hCD
  ·
    simp [hA, hB, hC, hD, hc0]
  ·
    simp [hA, hB, hC, hD, hc0]
  ·
    simp [hA, hB, hC, hD]

@[expose] def ptsW : List (List (Fin 4) × (ℕ × ℕ) × Bool) :=
  (repLines.flatMap fun x =>
      [(x.1, (x.2.1, x.2.2), false), (x.1, (x.2.1, x.2.2), true)]) ++
    (repLines.flatMap fun x =>
      [(x.1 ++ w0word, (piIdx.getD x.2.1 0, piIdx.getD x.2.2 0), false),
        (x.1 ++ w0word, (piIdx.getD x.2.1 0, piIdx.getD x.2.2 0), true)])

theorem ptsW_map : ptsW.map Prod.snd = pts := by decide +kernel

theorem ptsW_length : ptsW.length = 192 := by decide +kernel

theorem pts_nodup : pts.Nodup := by decide +kernel

theorem ptsW_nodup : ptsW.Nodup :=
  List.Nodup.of_map _ (by rw [ptsW_map]; exact pts_nodup)

theorem ptsW_snd_injOn {x y : List (Fin 4) × (ℕ × ℕ) × Bool} (hx : x ∈ ptsW) (hy : y ∈ ptsW)
    (h : x.2 = y.2) : x = y :=
  List.inj_on_of_nodup_map (by rw [ptsW_map]; exact pts_nodup) hx hy h

theorem ptsW_getElem_snd_inj {i j : ℕ} (hi : i < ptsW.length) (hj : j < ptsW.length)
    (h : ptsW[i].2 = ptsW[j].2) : i = j :=
  (ptsW_nodup.getElem_inj_iff (hi := hi) (hj := hj)).1
    (ptsW_snd_injOn (List.getElem_mem hi) (List.getElem_mem hj) h)

theorem ptsW_idx_all : ptsW.all (fun x => wordIdxN x.1 0 == x.2.1.1 && wordIdxN x.1 1 == x.2.1.2 &&
    wordIdxN x.1 26 == piIdx.getD x.2.1.1 0 && wordIdxN x.1 25 == piIdx.getD x.2.1.2 0) = true := by
  decide +kernel

theorem ptsW_ne_all : ptsW.all (fun x => x.2.1.1 != x.2.1.2 &&
    piIdx.getD x.2.1.1 0 != piIdx.getD x.2.1.2 0) = true := by
  decide +kernel

theorem ptsW_rev_all : ptsW.all (fun x => ptsW.all (fun y =>
    !(y.2.1.1 == piIdx.getD x.2.1.2 0 && y.2.1.2 == piIdx.getD x.2.1.1 0))) = true := by
  decide +kernel

theorem ptsW_idx {x : List (Fin 4) × (ℕ × ℕ) × Bool} (hx : x ∈ ptsW) :
    wordIdxN x.1 0 = x.2.1.1 ∧ wordIdxN x.1 1 = x.2.1.2 ∧
      wordIdxN x.1 26 = piIdx.getD x.2.1.1 0 ∧ wordIdxN x.1 25 = piIdx.getD x.2.1.2 0 := by
  have h := List.all_eq_true.1 ptsW_idx_all x hx
  simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem ptsW_ne {x : List (Fin 4) × (ℕ × ℕ) × Bool} (hx : x ∈ ptsW) :
    x.2.1.1 ≠ x.2.1.2 ∧ piIdx.getD x.2.1.1 0 ≠ piIdx.getD x.2.1.2 0 := by
  have h := List.all_eq_true.1 ptsW_ne_all x hx
  simpa [Bool.and_eq_true, bne_iff_ne] using h

theorem ptsW_rev {x y : List (Fin 4) × (ℕ × ℕ) × Bool} (hx : x ∈ ptsW) (hy : y ∈ ptsW) :
    ¬ (y.2.1.1 = piIdx.getD x.2.1.2 0 ∧ y.2.1.2 = piIdx.getD x.2.1.1 0) := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 ptsW_rev_all x hx) y hy
  rintro ⟨h1, h2⟩
  simp [h1, h2] at h


theorem w0word_idx (b : ℕ) (hb : b < 27) : wordIdxN w0word b = piIdx.getD b 0 := by
  have h := List.all_eq_true.1 w0word_ok b (List.mem_range.2 hb)
  simpa using h

private theorem sRefl_val' (i : Fin TwistTag.E6.tag.rank) (a : Fin e6Data.d) :
    (e6Data_valid.sRefl i a : ℕ) = e6Data.weyl a i := e6Data_valid.sRefl_val i a

theorem wordIdx_val (l : List (Fin TwistTag.E6.foldedTag.rank)) (b : Fin e6Data.d) :
    ((wordIdx l b : Fin e6Data.d) : ℕ) = wordIdxN l (b : ℕ) := by
  have h1 : ∀ (L : List (Fin TwistTag.E6.tag.rank)) (x : Fin e6Data.d),
      ((L.foldr (fun i b => e6Data_valid.sRefl i b) x : Fin e6Data.d) : ℕ) =
        L.foldr (fun i b => e6Data.weyl b i) (x : ℕ) := by
    intro L
    induction L with
    | nil => intro x; rfl
    | cons i L ih =>
      intro x
      show ((e6Data_valid.sRefl i (L.foldr (fun i b => e6Data_valid.sRefl i b) x) : Fin e6Data.d) :
        ℕ) = e6Data.weyl (L.foldr (fun i b => e6Data.weyl b i) (x : ℕ)) i
      rw [sRefl_val', ih]
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    show ((TwistTag.E6.orbitWord a).foldr (fun i b => e6Data_valid.sRefl i b) (wordIdx l b) :
      Fin e6Data.d).val = (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data.weyl b i)
        (wordIdxN l (b : ℕ))
    rw [h1, ih]

theorem idx1_val : (idx1 : ℕ) = 1 := by
  have h := e6Data_valid.sRefl_val (⟨0, by decide⟩ : Fin Tag.E6.rank)
    (⟨0, by decide⟩ : Fin e6Data.d)
  have h2 : e6Data.weyl 0 (⟨0, by decide⟩ : Fin Tag.E6.rank) = 1 := by decide +kernel
  exact h.trans h2

theorem lwIdx_val : (lwIdx : ℕ) = 26 := rfl

theorem lw1Idx_val : (lw1Idx : ℕ) = 25 := by
  have h := e6Data_valid.sRefl_val (⟨5, by decide⟩ : Fin Tag.E6.rank) lwIdx
  have h2 : e6Data.weyl 26 (⟨5, by decide⟩ : Fin Tag.E6.rank) = 25 := by decide +kernel
  exact h.trans h2

theorem wordIdx_w0word_lw : wordIdx w0word lwIdx = ⟨0, by decide⟩ := by
  apply Fin.ext
  have h1 := wordIdx_val w0word lwIdx
  rw [lwIdx_val, w0word_idx 26 (by norm_num)] at h1
  exact h1

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
