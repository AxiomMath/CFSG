module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.LAData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

namespace Words

variable {K : Type} [Field K]
  {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}

@[expose] def Oact (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) (c : (Fin Tag.F4.rank → ℤ) → K) : (Fin Tag.F4.rank → ℤ) → K :=
  actFun a1 a2 γ 1 c - c

theorem Oact_add (γ : Fin Tag.F4.rank → ℤ) (c c' : (Fin Tag.F4.rank → ℤ) → K) :
    Oact a1 a2 γ (c + c') = Oact a1 a2 γ c + Oact a1 a2 γ c' := by
  funext ν
  simp only [Oact, actFun, Pi.add_apply, Pi.sub_apply]
  ring

theorem coeff_single_shift {ι : Type} [AddCommGroup ι] [DecidableEq ι] (f : ι → ℤ)
    (δ μ ν : ι) (e : K) :
    (f (ν - δ) : K) * (Pi.single μ e : ι → K) (ν - δ) =
      (Pi.single (μ + δ) ((f μ : K) * e) : ι → K) ν := by
  by_cases h : ν - δ = μ
  · rw [h, Pi.single_eq_same, Pi.single_apply, if_pos (sub_eq_iff_eq_add.1 h)]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne, mul_zero]
    exact fun h' => h (sub_eq_iff_eq_add.2 h')

theorem Oact_single (γ μ : Fin Tag.F4.rank → ℤ) (e : K) :
    Oact a1 a2 γ (Pi.single μ e) =
      Pi.single (μ + γ) ((a1 γ μ : K) * e) + Pi.single (μ + 2 • γ) ((a2 γ μ : K) * e) := by
  funext ν
  have e1 := coeff_single_shift (K := K) (a1 γ) γ μ ν e
  have e2 := coeff_single_shift (K := K) (a2 γ) (2 • γ) μ ν e
  simp only [Oact, actFun, Pi.add_apply, Pi.sub_apply]
  linear_combination e1 + e2

theorem Oact_mem {W : Set ((Fin Tag.F4.rank → ℤ) → K)}
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hstab : ∀ γ ∈ f4ShortList, ∀ t : K, ∀ c ∈ W, actFun a1 a2 γ t c ∈ W)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList) {c : (Fin Tag.F4.rank → ℤ) → K}
    (hc : c ∈ W) : Oact a1 a2 γ c ∈ W := by
  rw [Oact, sub_eq_add_neg]
  exact hadd _ (hstab γ hγ 1 c hc) _ (hneg c hc)

theorem list_sum_single_apply {ι : Type} [DecidableEq ι] (f : ι → K) :
    ∀ (l : List ι), l.Nodup → ∀ ν,
      (l.map fun τ => (Pi.single τ (f τ) : ι → K)).sum ν = if ν ∈ l then f ν else 0
  | [], _, ν => by simp
  | τ :: l, hl, ν => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, Pi.add_apply, list_sum_single_apply f l hl.2 ν]
    by_cases h : ν = τ
    · subst h
      simp [hl.1]
    · simp [h]

theorem eq_list_sum {ι : Type} [DecidableEq ι] {c : ι → K} {l : List ι} (hl : l.Nodup)
    (hs : ∀ ν, c ν ≠ 0 → ν ∈ l) :
    c = (l.map fun τ => (Pi.single τ (c τ) : ι → K)).sum := by
  funext ν
  rw [list_sum_single_apply c l hl]
  by_cases h : ν ∈ l
  · rw [if_pos h]
  · rw [if_neg h]
    by_contra h'
    exact h (hs ν h')

@[expose] def wt (a b c d : ℤ) : Fin Tag.F4.rank → ℤ := ![a, b, c, d]

theorem eq_tops_odd {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsOdd) :
    c = Pi.single (wt 1 1 2 2) (c (wt 1 1 2 2)) + Pi.single (wt 1 2 4 2) (c (wt 1 2 4 2)) := by
  have hs' : ∀ ν, c ν ≠ 0 → ν ∈ [wt 1 1 2 2, wt 1 2 4 2] := hs
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
    eq_list_sum (by decide +kernel) hs'

theorem eq_tops_two {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsTwo) :
    c = Pi.single (wt 1 1 2 2) (c (wt 1 1 2 2)) + (Pi.single (wt 1 1 2 1) (c (wt 1 1 2 1)) +
      (Pi.single (wt 1 2 4 2) (c (wt 1 2 4 2)) + Pi.single (wt 1 2 3 2) (c (wt 1 2 3 2)))) := by
  have hs' : ∀ ν, c ν ≠ 0 → ν ∈ [wt 1 1 2 2, wt 1 1 2 1, wt 1 2 4 2, wt 1 2 3 2] := hs
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
    eq_list_sum (by decide +kernel) hs'

@[expose] def coords (v : Fin Tag.F4.rank → ℤ) : ℤ × ℤ × ℤ × ℤ := (v 0, v 1, v 2, v 3)

@[expose] def ofCoords (t : ℤ × ℤ × ℤ × ℤ) : Fin Tag.F4.rank → ℤ :=
  ![t.1, t.2.1, t.2.2.1, t.2.2.2]

@[expose] def f4PosTuples : List (ℤ × ℤ × ℤ × ℤ) :=
  [(0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 1, 1), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1),
    (0, 1, 2, 0), (0, 1, 2, 1), (0, 1, 2, 2), (1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 0),
    (1, 1, 1, 1), (1, 1, 2, 0), (1, 1, 2, 1), (1, 1, 2, 2), (1, 2, 2, 0), (1, 2, 2, 1),
    (1, 2, 2, 2), (1, 2, 3, 1), (1, 2, 3, 2), (1, 2, 4, 2), (1, 3, 4, 2), (2, 3, 4, 2)]

@[expose] def f4Tuples : List (ℤ × ℤ × ℤ × ℤ) :=
  f4PosTuples ++ f4PosTuples.map fun t => (-t.1, -t.2.1, -t.2.2.1, -t.2.2.2)

theorem coords_mem_f4Tuples : ∀ v ∈ rootFinset .F4, coords v ∈ f4Tuples := by decide +kernel

theorem ofCoords_mem_rootFinset : ∀ t ∈ f4Tuples, ofCoords t ∈ rootFinset .F4 := by decide +kernel

theorem mem_rootFinset_F4 (v : Fin Tag.F4.rank → ℤ) :
    v ∈ rootFinset .F4 ↔ coords v ∈ f4Tuples := by
  refine ⟨coords_mem_f4Tuples v, fun h => ?_⟩
  have e : ofCoords (coords v) = v := by
    funext i
    fin_cases i <;> rfl
  exact e ▸ ofCoords_mem_rootFinset _ h

theorem cast_ne_zero_of_abs_eq_one {z : ℤ} (h : |z| = 1) : (z : K) ≠ 0 := by
  rcases (abs_eq zero_le_one).1 h with rfl | rfl <;> simp

theorem cast_ne_zero_of_abs_eq_two {z : ℤ} (h : |z| = 2) (h2 : (2 : K) ≠ 0) : (z : K) ≠ 0 := by
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).1 h with rfl | rfl
  · simpa using h2
  · simpa using h2

theorem cast_eq_zero_of_abs_eq_two {z : ℤ} (h : |z| = 2) (h2 : (2 : K) = 0) : (z : K) = 0 := by
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).1 h with rfl | rfl
  · simpa using h2
  · simpa using h2

theorem a1_zero (h1 : Adm1 a1) {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList)
    (hμ : μ ∈ deg1Roots) (h : coords (γ + μ) ∉ f4Tuples) : (a1 γ μ : K) = 0 := by
  rw [(h1.short γ hγ μ hμ).2 fun hm => h ((mem_rootFinset_F4 _).1 hm)]
  simp

theorem a1_zero_even (h2K : (2 : K) = 0) (h1 : Adm1 a1) {γ μ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ f4ShortList) (hμ : μ ∈ deg1Roots) (h : coords (γ + μ) ∈ f4Tuples)
    (h' : coords (μ - γ) ∈ f4Tuples) : (a1 γ μ : K) = 0 := by
  have := (h1.short γ hγ μ hμ).1 ((mem_rootFinset_F4 _).2 h)
  rw [if_pos ((mem_rootFinset_F4 _).2 h')] at this
  exact cast_eq_zero_of_abs_eq_two this h2K

theorem a1_ne_zero_odd (h2K : (2 : K) ≠ 0) (h1 : Adm1 a1) {γ μ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ f4ShortList) (hμ : μ ∈ deg1Roots) (h : coords (γ + μ) ∈ f4Tuples) :
    (a1 γ μ : K) ≠ 0 := by
  have := (h1.short γ hγ μ hμ).1 ((mem_rootFinset_F4 _).2 h)
  by_cases h' : μ - γ ∈ rootFinset .F4
  · rw [if_pos h'] at this
    exact cast_ne_zero_of_abs_eq_two this h2K
  · rw [if_neg h'] at this
    exact cast_ne_zero_of_abs_eq_one this

theorem a1_ne_zero_even (h1 : Adm1 a1) {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList)
    (hμ : μ ∈ deg1Roots) (h : coords (γ + μ) ∈ f4Tuples) (h' : coords (μ - γ) ∉ f4Tuples) :
    (a1 γ μ : K) ≠ 0 := by
  have := (h1.short γ hγ μ hμ).1 ((mem_rootFinset_F4 _).2 h)
  rw [if_neg fun hm => h' ((mem_rootFinset_F4 _).1 hm)] at this
  exact cast_ne_zero_of_abs_eq_one this

theorem a2_zero (h2 : Adm2 a2) {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList)
    (hμ : μ ∈ deg1Roots) (h : coords (2 • γ + μ) ∉ f4Tuples) : (a2 γ μ : K) = 0 := by
  rw [(h2.short γ hγ μ hμ).2 fun hm => h ((mem_rootFinset_F4 _).1 hm)]
  simp

theorem word_i (h1 : Adm1 a1) (h2 : Adm2 a2) (h2K : (2 : K) ≠ 0)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsOdd)
    (hc : c (wt 1 1 2 2) ≠ 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧
      Oact a1 a2 (wt 0 0 0 (-1)) (Oact a1 a2 (wt 0 0 0 (-1)) c) = Pi.single ν e := by
  rw [eq_tops_odd hs]
  simp (disch := decide +kernel) only [add_zero, Oact_add, Oact_single, a1_zero h1, a2_zero h2,
    zero_mul, Pi.single_zero, zero_add]
  refine ⟨_, ?_, _, ?_, rfl⟩
  · decide +kernel
  · refine mul_ne_zero (a1_ne_zero_odd h2K h1 ?_ ?_ ?_)
      (mul_ne_zero (a1_ne_zero_odd h2K h1 ?_ ?_ ?_) hc) <;> decide +kernel

theorem word_ii (h1 : Adm1 a1) (h2 : Adm2 a2) (h2K : (2 : K) ≠ 0)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsOdd)
    (hc : c (wt 1 2 4 2) ≠ 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧
      Oact a1 a2 (wt 0 0 (-1) 0) (Oact a1 a2 (wt 0 0 (-1) 0) c) = Pi.single ν e := by
  rw [eq_tops_odd hs]
  simp (disch := decide +kernel) only [add_zero, Oact_add, Oact_single, a1_zero h1, a2_zero h2,
    zero_mul, Pi.single_zero, zero_add]
  refine ⟨_, ?_, _, ?_, rfl⟩
  · decide +kernel
  · refine mul_ne_zero (a1_ne_zero_odd h2K h1 ?_ ?_ ?_)
      (mul_ne_zero (a1_ne_zero_odd h2K h1 ?_ ?_ ?_) hc) <;> decide +kernel

theorem word_iii (h1 : Adm1 a1) (h2 : Adm2 a2) (h2K : (2 : K) = 0)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsTwo)
    (hc : c (wt 1 1 2 2) ≠ 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧
      Oact a1 a2 (wt 0 0 (-1) (-1)) (Oact a1 a2 (wt 0 0 0 (-1)) c) = Pi.single ν e := by
  rw [eq_tops_two hs]
  simp (disch := decide +kernel) only [add_zero, Oact_add, Oact_single, a1_zero h1, a2_zero h2,
    a1_zero_even h2K h1, zero_mul, Pi.single_zero, zero_add]
  refine ⟨_, ?_, _, ?_, rfl⟩
  · decide +kernel
  · refine mul_ne_zero (a1_ne_zero_even h1 ?_ ?_ ?_ ?_)
      (mul_ne_zero (a1_ne_zero_even h1 ?_ ?_ ?_ ?_) hc) <;> decide +kernel

theorem word_iv (h1 : Adm1 a1) (h2 : Adm2 a2) (h2K : (2 : K) = 0)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsTwo)
    (hc : c (wt 1 2 4 2) ≠ 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧
      Oact a1 a2 (wt 0 0 (-1) (-1)) (Oact a1 a2 (wt 0 0 (-1) 0) c) = Pi.single ν e := by
  rw [eq_tops_two hs]
  simp (disch := decide +kernel) only [add_zero, Oact_add, Oact_single, a1_zero h1, a2_zero h2,
    a1_zero_even h2K h1, zero_mul, Pi.single_zero, zero_add]
  refine ⟨_, ?_, _, ?_, rfl⟩
  · decide +kernel
  · refine mul_ne_zero (a1_ne_zero_even h1 ?_ ?_ ?_ ?_)
      (mul_ne_zero (a1_ne_zero_even h1 ?_ ?_ ?_ ?_) hc) <;> decide +kernel

theorem word_v (h1 : Adm1 a1) (h2 : Adm2 a2) (h2K : (2 : K) = 0)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsTwo)
    (hc : c (wt 1 1 2 1) ≠ 0) (hc3 : c (wt 1 2 4 2) = 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧
      Oact a1 a2 (wt 0 0 (-1) 0) c = Pi.single ν e := by
  rw [eq_tops_two hs]
  simp (disch := decide +kernel) only [add_zero, Oact_add, Oact_single, a1_zero h1, a2_zero h2,
    a1_zero_even h2K h1, zero_mul, Pi.single_zero, zero_add, hc3]
  refine ⟨_, ?_, _, ?_, rfl⟩
  · decide +kernel
  · refine mul_ne_zero (a1_ne_zero_even h1 ?_ ?_ ?_ ?_) hc <;> decide +kernel

theorem word_vi (h1 : Adm1 a1) (h2 : Adm2 a2) (h2K : (2 : K) = 0)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hs : ∀ ν, c ν ≠ 0 → ν ∈ topsTwo)
    (hc : c (wt 1 2 3 2) ≠ 0) (hc1 : c (wt 1 1 2 2) = 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧
      Oact a1 a2 (wt 0 0 0 (-1)) c = Pi.single ν e := by
  rw [eq_tops_two hs]
  simp (disch := decide +kernel) only [add_zero, Oact_add, Oact_single, a1_zero h1, a2_zero h2,
    a1_zero_even h2K h1, zero_mul, Pi.single_zero, zero_add, hc1]
  refine ⟨_, ?_, _, ?_, rfl⟩
  · decide +kernel
  · refine mul_ne_zero (a1_ne_zero_even h1 ?_ ?_ ?_ ?_) hc <;> decide +kernel

end Words

theorem words_extract {K : Type} [Field K]
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h1 : Adm1 a1) (h2 : Adm2 a2)
    (W : Set ((Fin Tag.F4.rank → ℤ) → K))
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hstab : ∀ γ ∈ f4ShortList, ∀ t : K, ∀ c ∈ W, actFun a1 a2 γ t c ∈ W)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hc : c ∈ W) (hc0 : c ≠ 0)
    (hsupp : ∀ ν, c ν ≠ 0 → ((2 : K) = 0 → ν ∈ topsTwo) ∧ ((2 : K) ≠ 0 → ν ∈ topsOdd)) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧ Pi.single ν e ∈ W := by
  have hO : ∀ γ ∈ f4ShortList, ∀ d ∈ W, Words.Oact a1 a2 γ d ∈ W :=
    fun γ hγ d hd => Words.Oact_mem hadd hneg hstab hγ hd
  obtain ⟨ν₀, hν₀⟩ : ∃ ν, c ν ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  by_cases h2K : (2 : K) = 0
  · have hs : ∀ ν, c ν ≠ 0 → ν ∈ topsTwo := fun ν hν => (hsupp ν hν).1 h2K
    by_cases hc1 : c (Words.wt 1 1 2 2) = 0
    · by_cases hc3 : c (Words.wt 1 2 4 2) = 0
      · by_cases hc2 : c (Words.wt 1 1 2 1) = 0
        · have hc4 : c (Words.wt 1 2 3 2) ≠ 0 := by
            have hmem : ν₀ ∈ [Words.wt 1 1 2 2, Words.wt 1 1 2 1, Words.wt 1 2 4 2,
                Words.wt 1 2 3 2] := hs ν₀ hν₀
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl
            · exact absurd hc1 hν₀
            · exact absurd hc2 hν₀
            · exact absurd hc3 hν₀
            · exact hν₀
          obtain ⟨ν, hν, e, he, heq⟩ := Words.word_vi h1 h2 h2K hs hc4 hc1
          exact ⟨ν, hν, e, he, heq ▸ hO _ (by decide +kernel) _ hc⟩
        · obtain ⟨ν, hν, e, he, heq⟩ := Words.word_v h1 h2 h2K hs hc2 hc3
          exact ⟨ν, hν, e, he, heq ▸ hO _ (by decide +kernel) _ hc⟩
      · obtain ⟨ν, hν, e, he, heq⟩ := Words.word_iv h1 h2 h2K hs hc3
        exact ⟨ν, hν, e, he, heq ▸ hO _ (by decide +kernel) _
          (hO _ (by decide +kernel) _ hc)⟩
    · obtain ⟨ν, hν, e, he, heq⟩ := Words.word_iii h1 h2 h2K hs hc1
      exact ⟨ν, hν, e, he, heq ▸ hO _ (by decide +kernel) _
        (hO _ (by decide +kernel) _ hc)⟩
  · have hs : ∀ ν, c ν ≠ 0 → ν ∈ topsOdd := fun ν hν => (hsupp ν hν).2 h2K
    by_cases hc1 : c (Words.wt 1 1 2 2) = 0
    · have hc3 : c (Words.wt 1 2 4 2) ≠ 0 := by
        have hmem : ν₀ ∈ [Words.wt 1 1 2 2, Words.wt 1 2 4 2] := hs ν₀ hν₀
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact absurd hc1 hν₀
        · exact hν₀
      obtain ⟨ν, hν, e, he, heq⟩ := Words.word_ii h1 h2 h2K hs hc3
      exact ⟨ν, hν, e, he, heq ▸ hO _ (by decide +kernel) _
        (hO _ (by decide +kernel) _ hc)⟩
    · obtain ⟨ν, hν, e, he, heq⟩ := Words.word_i h1 h2 h2K hs hc1
      exact ⟨ν, hν, e, he, heq ▸ hO _ (by decide +kernel) _
        (hO _ (by decide +kernel) _ hc)⟩

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
