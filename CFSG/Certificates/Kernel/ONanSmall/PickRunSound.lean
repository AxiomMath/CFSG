module

public import Certificates.Data.Kernel.ONanSmall.PickRun
public import CFSG.Certificates.Kernel.ONanSmall.CoverSound

public section

namespace CFSG.KC.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.Certificates.Kernel.ONanSmall

variable {M : Type*} [Group M] [DecidableEq M] {D : Type*}

theorem pickRun_sound (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (hinv : ∀ t, inv t = decide (t * t = 1 ∧ t ≠ 1))
    (hconj : ∀ g t r, conj g t r = decide (g * t * g⁻¹ = r))
    (hgen : ∀ d g, gen d = some g → g ∈ L₀) :
    ∀ (xs reps : List M) (W : List (ℕ × D)) (R : List M),
      pickRun L₀ inv conj gen reps xs W = some R →
      xs.foldl (fun reps t => if decide (t * t = 1 ∧ t ≠ 1) && !isCovered L₀ reps t
        then reps ++ [t] else reps) reps = R
  | [], reps, W, R, h => by
    simp only [pickRun, Option.some.injEq] at h
    simpa using h
  | t :: ts, reps, W, R, h => by
    rw [List.foldl_cons]
    unfold pickRun at h
    rw [hinv] at h
    by_cases ht : t * t = 1 ∧ t ≠ 1
    · rw [decide_eq_true ht, if_pos rfl] at h
      match W, h with
      | [], h => exact absurd h (by simp)
      | (j, d) :: W', h =>
        simp only at h
        by_cases hj : (j == reps.length) = true
        · rw [if_pos hj] at h
          by_cases hs : (L₀.any fun g => reps.any fun r => conj g t r) = true
          · rw [if_pos hs] at h
            exact absurd h (by simp)
          · rw [if_neg hs] at h
            have hc : isCovered L₀ reps t = false := by
              unfold isCovered
              simpa [hconj] using hs
            rw [hc, decide_eq_true ht]
            exact pickRun_sound L₀ inv conj gen hinv hconj hgen ts _ W' R h
        · rw [if_neg hj] at h
          match hg : gen d, h with
          | none, h => exact absurd h (by simp)
          | some g, h =>
            simp only at h
            by_cases hk : (j < reps.length && conj g t (reps.getD j 1)) = true
            · rw [if_pos hk] at h
              rw [Bool.and_eq_true, decide_eq_true_iff, hconj, decide_eq_true_iff] at hk
              have hc : isCovered L₀ reps t = true := by
                unfold isCovered
                refine List.any_eq_true.2 ⟨g, hgen d g hg, List.any_eq_true.2 ⟨reps.getD j 1, ?_, ?_⟩⟩
                · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk.1, Option.getD_some]
                  exact List.getElem_mem _
                · simp [hk.2]
              rw [hc]
              simpa using pickRun_sound L₀ inv conj gen hinv hconj hgen ts reps W' R h
            · rw [if_neg hk] at h
              exact absurd h (by simp)
    · rw [decide_eq_false ht] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [decide_eq_false ht]
      simpa using pickRun_sound L₀ inv conj gen hinv hconj hgen ts reps W R h

theorem pickReps_of_pickRun (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (hinv : ∀ t, inv t = decide (t * t = 1 ∧ t ≠ 1))
    (hconj : ∀ g t r, conj g t r = decide (g * t * g⁻¹ = r))
    (hgen : ∀ d g, gen d = some g → g ∈ L₀) (W : List (ℕ × D)) (R : List M)
    (h : pickRun L₀ inv conj gen [] L₀ W = some R) : pickReps L₀ = R :=
  pickRun_sound L₀ inv conj gen hinv hconj hgen L₀ [] W R h

theorem pickRun_cover (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (hinv : ∀ t, inv t = decide (t * t = 1 ∧ t ≠ 1))
    (hconj : ∀ g t r, conj g t r = decide (g * t * g⁻¹ = r))
    (hgen : ∀ d g, gen d = some g → g ∈ L₀) (h1 : (1 : M) ∈ L₀) :
    ∀ (xs reps : List M) (W : List (ℕ × D)) (R : List M),
      pickRun L₀ inv conj gen reps xs W = some R →
      (∀ r ∈ reps, r ∈ R) ∧ ∀ t ∈ xs, t * t = 1 ∧ t ≠ 1 → isCovered L₀ R t = true
  | [], reps, W, R, h => by
    simp only [pickRun, Option.some.injEq] at h
    subst h
    exact ⟨fun r hr => hr, fun t ht => by simp at ht⟩
  | t :: ts, reps, W, R, h => by
    unfold pickRun at h
    rw [hinv] at h
    by_cases ht : t * t = 1 ∧ t ≠ 1
    · rw [decide_eq_true ht, if_pos rfl] at h
      match W, h with
      | [], h => exact absurd h (by simp)
      | (j, d) :: W', h =>
        simp only at h
        by_cases hj : (j == reps.length) = true
        · rw [if_pos hj] at h
          by_cases hs : (L₀.any fun g => reps.any fun r => conj g t r) = true
          · rw [if_pos hs] at h
            exact absurd h (by simp)
          · rw [if_neg hs] at h
            obtain ⟨i1, i2⟩ := pickRun_cover L₀ inv conj gen hinv hconj hgen h1 ts _ W' R h
            refine ⟨fun r hr => i1 r (by simp [hr]), fun x hx hinvx => ?_⟩
            rcases List.mem_cons.1 hx with rfl | hx
            · exact isCovered_self h1 (i1 x (by simp))
            · exact i2 x hx hinvx
        · rw [if_neg hj] at h
          match hg : gen d, h with
          | none, h => exact absurd h (by simp)
          | some g, h =>
            simp only at h
            by_cases hk : (j < reps.length && conj g t (reps.getD j 1)) = true
            · rw [if_pos hk] at h
              obtain ⟨i1, i2⟩ := pickRun_cover L₀ inv conj gen hinv hconj hgen h1 ts reps W' R h
              rw [Bool.and_eq_true, decide_eq_true_iff, hconj, decide_eq_true_iff] at hk
              refine ⟨i1, fun x hx hinvx => ?_⟩
              rcases List.mem_cons.1 hx with rfl | hx
              · refine List.any_eq_true.2 ⟨g, hgen d g hg,
                  List.any_eq_true.2 ⟨reps.getD j 1, i1 _ ?_, by simp [hk.2]⟩⟩
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk.1, Option.getD_some]
                exact List.getElem_mem _
              · exact i2 x hx hinvx
            · rw [if_neg hk] at h
              exact absurd h (by simp)
    · rw [decide_eq_false ht] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨i1, i2⟩ := pickRun_cover L₀ inv conj gen hinv hconj hgen h1 ts reps W R h
      refine ⟨i1, fun x hx hinvx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hinvx ht
      · exact i2 x hx hinvx

theorem coverB_of_pickRun (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (hinv : ∀ t, inv t = decide (t * t = 1 ∧ t ≠ 1))
    (hconj : ∀ g t r, conj g t r = decide (g * t * g⁻¹ = r))
    (hgen : ∀ d g, gen d = some g → g ∈ L₀) (h1 : (1 : M) ∈ L₀) (W : List (ℕ × D)) (R : List M)
    (h : pickRun L₀ inv conj gen R L₀ W = some R) : coverB R L₀ = true := by
  have hc := (pickRun_cover L₀ inv conj gen hinv hconj hgen h1 L₀ R W R h).2
  unfold coverB
  refine List.all_eq_true.2 fun t ht => ?_
  by_cases hi : t * t = 1 ∧ t ≠ 1
  · rw [hc t ht hi, Bool.or_true]
  · simp [hi]

@[expose] def productsOf : List (List M) → List M
  | [] => [1]
  | T :: Ts => T.flatMap fun t => (productsOf Ts).map (t * ·)

theorem mem_genP : ∀ (Ts : List (List M)) (d : List ℕ) (g : M), genP Ts d = some g →
    g ∈ productsOf Ts
  | [], [], g, h => by
    simp only [genP, Option.some.injEq] at h
    simp [productsOf, ← h]
  | [], _ :: _, g, h => by simp [genP] at h
  | _ :: _, [], g, h => by simp [genP] at h
  | T :: Ts, i :: d, g, h => by
    unfold genP at h
    match ht : T[i]?, hx : genP Ts d, h with
    | some t, some x, h =>
      simp only [Option.some.injEq] at h
      subst h
      unfold productsOf
      refine List.mem_flatMap.2 ⟨t, List.mem_of_getElem? ht, List.mem_map.2 ⟨x, ?_, rfl⟩⟩
      exact mem_genP Ts d x hx
    | none, _, h => simp at h
    | some _, none, h => simp at h

end CFSG.KC.ONanSmall
