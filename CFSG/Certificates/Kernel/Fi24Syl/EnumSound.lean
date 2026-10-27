module

public import CFSG.Certificates.Kernel.Fi24Syl.MatSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data

public section

namespace CFSG.KS.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KC.Fi24Syl CFSG.KS.Ord CFSG.AGLEmbedding.R3 Matrix

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

noncomputable def leaves : List (List ℕ) → ℕ → List ℕ
  | [], acc => [acc]
  | Pi :: Ps, acc => Pi.flatMap fun P => leaves Ps (mul7 acc P)

@[expose] noncomputable def innerK (step : ℕ → ℕ → ℕ) (Ps : List (List ℕ)) (acc : ℕ) :
    List ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun st => st)
    (fun P _ ih2 st => strictN (mul7 acc P) fun M => strictN (enumK step Ps M st) ih2)

theorem enumK_nil (step : ℕ → ℕ → ℕ) (acc st : ℕ) : enumK step [] acc st = step acc st := rfl

theorem enumK_cons (step : ℕ → ℕ → ℕ) (Pi : List ℕ) (Ps : List (List ℕ)) (acc st : ℕ) :
    enumK step (Pi :: Ps) acc st = innerK step Ps acc Pi st := rfl

theorem innerK_cons (step : ℕ → ℕ → ℕ) (Ps : List (List ℕ)) (acc P : ℕ) (Pi : List ℕ) (st : ℕ) :
    innerK step Ps acc (P :: Pi) st = innerK step Ps acc Pi (enumK step Ps (mul7 acc P) st) := by
  change strictN (mul7 acc P) (fun M => strictN (enumK step Ps M st) (innerK step Ps acc Pi)) = _
  rw [strictN_eq, strictN_eq]

theorem enumK_add (step : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (hs : ∀ M st, step M st = st + c M) :
    ∀ Ps acc st, enumK step Ps acc st = st + ((leaves Ps acc).map c).sum
  | [], acc, st => by
    rw [enumK_nil, hs]
    simp [leaves]
  | Pi :: Ps, acc, st => by
    rw [enumK_cons]
    induction Pi generalizing st with
    | nil => simp [innerK, leaves]
    | cons P Pi ih =>
      rw [innerK_cons, ih, enumK_add step c hs Ps]
      simp only [leaves, List.flatMap_cons, List.map_append, List.sum_append]
      omega

theorem contribK_add (AV La Ha L31 CMa TL T31 T32 T63 R1 N st : ℕ) :
    contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N st =
      st + contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N 0 := by
  unfold contribK
  simp only [strictN_eq]
  change st + _ + _ = st + (0 + _ + _)
  omega

theorem leaves_append : ∀ (Ps Qs : List (List ℕ)) (acc : ℕ),
    leaves (Ps ++ Qs) acc = (leaves Ps acc).flatMap (leaves Qs)
  | [], Qs, acc => by simp [leaves]
  | Pi :: Ps, Qs, acc => by
    simp only [List.cons_append, leaves, leaves_append Ps Qs, List.flatMap_assoc]

noncomputable def pwL (A : List ℕ) : List ℕ := [ONE7, packL A, mul7 (packL A) (packL A)]

theorem pwL_exists {A : List ℕ} (hA : ∀ x ∈ A, x < 3) {a : ℕ} (ha : a < 3) :
    ∃ P ∈ pwL A, C7 P ∧ mat7 P = (toMatL 3 7 A).transpose ^ a := by
  obtain ⟨h1, h2⟩ := packL_sound hA
  obtain ⟨h3, h4⟩ := mul7_sound h1 h1
  have m0 : ONE7 ∈ pwL A := List.mem_cons_self
  have m1 : packL A ∈ pwL A := List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : mul7 (packL A) (packL A) ∈ pwL A :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h0 := one7_sound
  interval_cases a
  · refine ⟨ONE7, m0, h0.1, ?_⟩
    rw [pow_zero]
    exact h0.2
  · refine ⟨packL A, m1, h1, ?_⟩
    rw [pow_one]
    exact h2
  · refine ⟨mul7 (packL A) (packL A), m2, h3, ?_⟩
    rw [h4, h2, pow_two]

theorem pwL_canon' {A : List ℕ} (hA : ∀ x ∈ A, x < 3) {P : ℕ} (hP : P ∈ pwL A) : C7 P := by
  obtain ⟨h1, -⟩ := packL_sound hA
  have h3 := (mul7_sound h1 h1).1
  have h0 := one7_sound.1
  have hP' : P = ONE7 ∨ P = packL A ∨ P = mul7 (packL A) (packL A) := by
    simpa only [pwL, List.mem_cons, List.not_mem_nil, or_false] using hP
  rcases hP' with h | h | h
  · rw [h]
    exact h0
  · rw [h]
    exact h1
  · rw [h]
    exact h3

theorem leaves_words : ∀ (As : List (List ℕ)), (∀ A ∈ As, ∀ x ∈ A, x < 3) →
    ∀ acc, C7 acc → ∀ x ∈ wordsL 3 7 As,
      ∃ M ∈ leaves (As.map pwL).reverse acc, C7 M ∧ mat7 M = mat7 acc * (toMatL 3 7 x).transpose
  | [], _, acc, hacc, x, hx => by
    simp only [wordsL, List.mem_singleton] at hx
    subst hx
    refine ⟨acc, by simp [leaves], hacc, ?_⟩
    rw [toMatL_midL, transpose_one, mul_one]
  | A :: As, hAs, acc, hacc, x, hx => by
    simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨y, hy, a, ha, rfl⟩ := hx
    obtain ⟨M', hM', hC', hm'⟩ :=
      leaves_words As (fun B hB => hAs B (List.mem_cons_of_mem _ hB)) acc hacc y hy
    obtain ⟨P, hP, hPC, hPm⟩ := pwL_exists (hAs A List.mem_cons_self) ha
    obtain ⟨hMC, hMm⟩ := mul7_sound hC' hPC
    refine ⟨mul7 M' P, ?_, hMC, ?_⟩
    · rw [List.map_cons, List.reverse_cons, leaves_append, List.mem_flatMap]
      exact ⟨M', hM', by simp only [leaves, List.mem_flatMap, List.mem_singleton]; exact ⟨_, hP, rfl⟩⟩
    · rw [hMm, hm', hPm, toMatL_mmulL, toMatL_mpowL, transpose_mul, transpose_pow, mul_assoc]

noncomputable def tops9 : List (List ℕ) :=
  AlphaFi24.fi24Tidx.map fun i => (AlphaFi24.fi24Mod.acts.getD i default).mat

theorem tops9_eq :
    tops9 = AlphaFi24.fi24Tidx.map fun i => (AlphaFi24.fi24Mod.acts.getD i default).mat := by
  unfold tops9
  rfl

theorem tops9_lt : ∀ A ∈ tops9, ∀ x ∈ A, x < 3 := by
  unfold tops9
  decide +kernel

theorem one7_mul {X : ℕ} (hX : C7 X) : mul7 ONE7 X = X := by
  obtain ⟨h1, h2⟩ := mul7_sound one7_sound.1 hX
  exact canon7_inj h1 hX (by rw [h2, one7_sound.2, one_mul])

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem tops_eq {T : ℕ → ℕ} {As : List (List ℕ)} (h : topsOK T As = true) :
    As.length = 9 ∧ ∀ k < 9, T k = packL (As.getD k []) := by
  unfold topsOK at h
  obtain ⟨h1, h2⟩ := andB_true h
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_⟩
  have key : ∀ m, Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (Nat.beq (T k) (packL (As.getD k [])))) m = true →
      ∀ k < m, T k = packL (As.getD k []) := by
    intro m
    induction m with
    | zero => intro _ k hk; omega
    | succ m ih =>
      intro hm k hk
      obtain ⟨hm1, hm2⟩ := andB_true hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ih hm1 k hk
      · exact Nat.eq_of_beq_eq_true hm2
  exact key 9 h2

private theorem mem3 {a b d P : ℕ} (h : P ∈ [a, b, d]) : ∃ e < 3, P = [a, b, d].getD e 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩


theorem cover_gen {T : ℕ → ℕ} {As : List (List ℕ)} (hT : topsOK T As = true)
    (hAs : ∀ A ∈ As, ∀ x ∈ A, x < 3) :
    ∀ x ∈ wordsL 3 7 As, ∃ c < 27, ∃ M ∈ leaves (PsK T) (RK T c),
      C7 M ∧ mat7 M = (toMatL 3 7 x).transpose := by
  obtain ⟨hlen, hTk⟩ := tops_eq hT
  intro x hx
  obtain ⟨M, hM, hC, hm⟩ := leaves_words As hAs ONE7 one7_sound.1 x hx
  rw [one7_sound.2, one_mul] at hm
  rcases As with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨t4, _ | ⟨t5, _ | ⟨t6, _ | ⟨t7, _ |
    ⟨t8, _ | ⟨t9, As⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;>
    try omega
  have hpw : ∀ k < 9, pw T k = pwL ([t0, t1, t2, t3, t4, t5, t6, t7, t8].getD k []) :=
    fun k hk => by rw [pw, pwL, hTk k hk]
  have hcan : ∀ k < 9, ∀ P ∈ pw T k, C7 P := by
    intro k hk P hP
    rw [hpw k hk] at hP
    refine pwL_canon' (fun y hy => hAs _ ?_ y hy) hP
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
    exact List.getElem_mem _
  have hP : ([t0, t1, t2, t3, t4, t5, t6, t7, t8].map pwL).reverse =
      [pw T 8, pw T 7, pw T 6] ++ PsK T := by
    simp only [PsK, hpw 0 (by norm_num), hpw 1 (by norm_num), hpw 2 (by norm_num),
      hpw 3 (by norm_num), hpw 4 (by norm_num), hpw 5 (by norm_num), hpw 6 (by norm_num),
      hpw 7 (by norm_num), hpw 8 (by norm_num)]
    rfl
  rw [hP, leaves_append, List.mem_flatMap] at hM
  obtain ⟨R, hR, hMR⟩ := hM
  simp only [leaves, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap,
    List.mem_singleton] at hR
  obtain ⟨P8, hP8, P7, hP7, P6, hP6, rfl⟩ := hR
  obtain ⟨e9, he9, h9⟩ := mem3 hP8
  obtain ⟨e8, he8, h8⟩ := mem3 hP7
  obtain ⟨e7, he7, h7⟩ := mem3 hP6
  refine ⟨e7 + 3 * e8 + 9 * e9, by omega, M, ?_, hC, hm⟩
  have hc1 : Nat.div (e7 + 3 * e8 + 9 * e9) 9 = e9 := by
    change (e7 + 3 * e8 + 9 * e9) / 9 = e9
    omega
  have hc2 : Nat.mod (Nat.div (e7 + 3 * e8 + 9 * e9) 3) 3 = e8 := by
    change (e7 + 3 * e8 + 9 * e9) / 3 % 3 = e8
    omega
  have hc3 : Nat.mod (e7 + 3 * e8 + 9 * e9) 3 = e7 := by
    change (e7 + 3 * e8 + 9 * e9) % 3 = e7
    omega
  have hRK : RK T (e7 + 3 * e8 + 9 * e9) = mul7 (mul7 (mul7 ONE7 P8) P7) P6 := by
    rw [one7_mul (hcan 8 (by norm_num) P8 hP8)]
    unfold RK
    rw [hc1, hc2, hc3, h9, h8, h7]
    rfl
  rw [hRK]
  exact hMR

theorem cover {T : ℕ → ℕ} (hT : topsOK T tops9 = true) :
    ∀ x ∈ wordsL 3 7 tops9, ∃ c < 27, ∃ M ∈ leaves (PsK T) (RK T c),
      C7 M ∧ mat7 M = (toMatL 3 7 x).transpose :=
  cover_gen hT tops9_lt
