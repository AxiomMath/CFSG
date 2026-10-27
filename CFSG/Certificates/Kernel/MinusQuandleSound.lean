module

public import Certificates.Data.Kernel.MinusQuandle

public section

namespace CFSG.KC.MinusQuandle

open CFSG.OddTranspositions.PartThree CFSG.KD.MinusQuandle

@[simp] theorem force_eq {β : Sort _} (y : ℕ) (k : ℕ → β) : force y k = k y := by
  cases y <;> rfl

theorem getElem!_of_map_eq {f : ℕ → ℕ} {A : Array ℕ} (h : (List.range 65).map f = A.toList)
    {j : ℕ} (hj : j < 65) : A[j]! = f j := by
  rcases A with ⟨L⟩
  simp only at h
  subst h
  simp [hj]

theorem tq_spec {R : ℕ → ℕ} (h : rowsOK R = true) {i j : ℕ} (hi : i < 65) (hj : j < 65) :
    minusQuandleT i j = tq R i j ∧ tq R i j < 65 := by
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [Bool.and_eq_true, beq_iff_eq] at h1
  refine ⟨getElem!_of_map_eq h1.1 hj, ?_⟩
  have h2 := List.all_eq_true.1 h1.2 j (List.mem_range.2 hj)
  simpa using h2

theorem dq_spec {D : ℕ → ℕ} (h : derivOK D = true) {a t : ℕ} (ha : a < 65) (ht : t < 65) :
    (minusQuandleDeriv[a]!)[t]! = dq D a t := by
  have h1 := List.all_eq_true.1 h a (List.mem_range.2 ha)
  rw [beq_iff_eq] at h1
  exact getElem!_of_map_eq h1 ht

theorem seq_eq {D : ℕ → ℕ} (h : derivOK D = true) {a t : ℕ} (ha : a < 65) (ht : t < 65) :
    minusQuandleSeq a t = dq D a t % 65 := by
  rw [minusQuandleSeq, dq_spec h ha ht]

theorem code_eq {D : ℕ → ℕ} (h : derivOK D = true) {a t : ℕ} (ha : a < 65) (ht : t < 65) :
    minusQuandleCode a t = dq D a t / 65 := by
  rw [minusQuandleCode, dq_spec h ha ht]

theorem tf_val {R : ℕ → ℕ} (hR : rowsOK R = true) (j y : Fin 65) :
    (minusQuandleTf j y : ℕ) = tq R j y := by
  obtain ⟨h1, h2⟩ := tq_spec hR j.isLt y.isLt
  rw [minusQuandleTf, Fin.val_ofNat, h1, Nat.mod_eq_of_lt h2]

theorem orF_testBit (n : ℕ) (f : ℕ → ℕ) (q : ℕ) :
    (orF n f).testBit q = true ↔ ∃ k < n, (f k).testBit q = true := by
  induction n with
  | zero => simp [orF]
  | succ n ih =>
    change (f n ||| orF n f).testBit q = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inr ⟨k, hk, h⟩
      · exact Or.inl h

theorem allF_spec {n : ℕ} {g : ℕ → Bool} (h : allF n g = true) {k : ℕ} (hk : k < n) :
    g k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    change Bool.rec false (allF n g) (g n) = true at h
    cases hg : g n
    · rw [hg] at h
      exact absurd h Bool.false_ne_true
    · rw [hg] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ih h hk
      · exact hg

theorem lane_testBit (w n i q : ℕ) :
    (lane w n i).testBit q = (decide (q < w) && n.testBit (w * i + q)) := by
  change ((n >>> (w * i)) &&& (2 ^ w - 1)).testBit q = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm]

theorem shift_testBit {n : ℕ} (hn : ∀ q, 4225 ≤ q → n.testBit q = false) (t z : ℕ) {p : ℕ}
    (hp : p < 4225) :
    (n <<< (4225 * t)).testBit (4225 * z + p) = (decide (t = z) && n.testBit p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases htz : t = z
  · subst htz
    simp [show 4225 * t + p - 4225 * t = p by omega]
  · rcases Nat.lt_or_gt_of_ne htz with h | h
    · have := hn (4225 * z + p - 4225 * t) (by omega)
      simp [htz, this]
    · simp [htz]
      omega

theorem lane_high (n i q : ℕ) (hq : 4225 ≤ q) : (lane 4225 n i).testBit q = false := by
  rw [lane_testBit]
  simp [show ¬ q < 4225 by omega]

def PRep (S : ℕ) (K : ℕ → Finset (Fin 65)) : Prop :=
  ∀ (x : Fin 65) (p : ℕ), p < 4225 → (S.testBit (4225 * x + p) = true ↔ x ∈ K p)

theorem lane_rep {S : ℕ} {K : ℕ → Finset (Fin 65)} (hS : PRep S K) (x : Fin 65) {p : ℕ}
    (hp : p < 4225) : (lane 4225 S x).testBit p = true ↔ x ∈ K p := by
  rw [lane_testBit]
  simp only [hp, decide_true, Bool.true_and]
  exact hS x p hp

theorem rep_imgS {R : ℕ → ℕ} (hR : rowsOK R = true) {S : ℕ} {K : ℕ → Finset (Fin 65)}
    (hS : PRep S K) (j : Fin 65) :
    PRep (imgS R j S) (fun p => (K p).image (minusQuandleTf j)) := by
  intro z p hp
  simp only [imgS, force_eq]
  rw [orF_testBit]
  have e : ∀ i, Nat.shiftLeft (lane 4225 S i) (Nat.mul 4225 (lane 7 (R j) i)) =
      lane 4225 S i <<< (4225 * tq R j i) := fun _ => rfl
  simp only [e, shift_testBit (lane_high S _) _ _ hp, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hiz, h⟩
    refine ⟨⟨i, hi⟩, (lane_rep hS ⟨i, hi⟩ hp).1 h, Fin.ext ?_⟩
    rw [tf_val hR]
    exact hiz
  · rintro ⟨y, hy, hyz⟩
    refine ⟨y, y.isLt, ?_, (lane_rep hS y hp).2 hy⟩
    have := congrArg Fin.val hyz
    rw [tf_val hR] at this
    exact this

theorem rep_stepS {R : ℕ → ℕ} (hR : rowsOK R = true) {S : ℕ} {K : ℕ → Finset (Fin 65)}
    (hS : PRep S K) : PRep (stepS R S) (fun p => minusQuandleStepF (K p)) := by
  intro z p hp
  have hI := rep_imgS hR hS
  have hN : ∀ j : Fin 65, ∀ q, (orF 65 fun y => lane 4225 (imgS R j S &&& S) y).testBit q =
      true ↔ q < 4225 ∧ (((K q).image (minusQuandleTf j)) ∩ K q).Nonempty := by
    intro j q
    rw [orF_testBit]
    simp only [lane_testBit, Nat.testBit_and, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, hq, h1, h2⟩
      exact ⟨hq, ⟨y, hy⟩, Finset.mem_inter.2 ⟨(hI j ⟨y, hy⟩ q hq).1 h1, (hS ⟨y, hy⟩ q hq).1 h2⟩⟩
    · rintro ⟨hq, y, hy⟩
      rw [Finset.mem_inter] at hy
      exact ⟨y, y.isLt, hq, (hI j y q hq).2 hy.1, (hS y q hq).2 hy.2⟩
  have hB : ∀ j : Fin 65, (orF 65 fun y => Nat.shiftLeft
      (orF 65 fun y => lane 4225 (imgS R j S &&& S) y) (Nat.mul 4225 y)).testBit
      (4225 * z + p) = true ↔ (((K p).image (minusQuandleTf j)) ∩ K p).Nonempty := by
    intro j
    rw [orF_testBit]
    have hhi : ∀ q, 4225 ≤ q →
        (orF 65 fun y => lane 4225 (imgS R j S &&& S) y).testBit q = false := by
      intro q hq
      cases h : (orF 65 fun y => lane 4225 (imgS R j S &&& S) y).testBit q
      · rfl
      · exact absurd ((hN j q).1 h).1 (by omega)
    have e : ∀ y, Nat.shiftLeft (orF 65 fun y => lane 4225 (imgS R j S &&& S) y)
        (Nat.mul 4225 y) = (orF 65 fun y => lane 4225 (imgS R j S &&& S) y) <<< (4225 * y) :=
      fun _ => rfl
    simp only [e, shift_testBit hhi _ _ hp, Bool.and_eq_true, decide_eq_true_eq, hN j p, hp,
      true_and]
    constructor
    · rintro ⟨_, _, _, h⟩
      exact h
    · intro h
      exact ⟨z, z.isLt, rfl, h⟩
  simp only [stepS, force_eq]
  change (S ||| orF 65 fun j => imgS R j S &&& orF 65 fun y => Nat.shiftLeft
      (orF 65 fun y => lane 4225 (imgS R j S &&& S) y) (Nat.mul 4225 y)).testBit
      (4225 * z + p) = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true, orF_testBit, hS z p hp]
  simp only [Nat.testBit_and, Bool.and_eq_true, minusQuandleStepF, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨j, hj, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨⟨j, hj⟩, ?_⟩
      rw [if_pos ((hB ⟨j, hj⟩).1 h2)]
      exact (hI ⟨j, hj⟩ z p hp).1 h1
  · rintro (h | ⟨j, h⟩)
    · exact Or.inl h
    · by_cases hne : ((K p).image (minusQuandleTf j) ∩ K p).Nonempty
      · rw [if_pos hne] at h
        exact Or.inr ⟨j, j.isLt, (hI j z p hp).2 h, (hB j).2 hne⟩
      · rw [if_neg hne] at h
        simp at h

theorem colS_testBit (q : ℕ) : colS.testBit q = true ↔ q < 4225 ∧ q % 65 = 0 := by
  rw [colS, orF_testBit]
  change (∃ k < 65, (1 <<< (65 * k)).testBit q = true) ↔ _
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, h1⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨q / 65, by omega, by omega⟩

theorem diagS_testBit (q : ℕ) : diagS.testBit q = true ↔ q < 4225 ∧ q / 65 = q % 65 := by
  rw [diagS, orF_testBit]
  change (∃ k < 65, (1 <<< (66 * k)).testBit q = true) ↔ _
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, h1⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨q / 65, by omega, by omega⟩

theorem rep_initS :
    PRep initS (fun p => {Fin.ofNat 65 (p / 65), Fin.ofNat 65 (p % 65)}) := by
  intro z p hp
  simp only [initS, force_eq]
  rw [orF_testBit]
  have hA : ∀ x, x < 65 → ∀ q,
      (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 x)) (Nat.shiftLeft colS x)).testBit q =
        true ↔ (65 * x ≤ q ∧ q < 65 * x + 65) ∨ (x ≤ q ∧ q < 4225 ∧ (q - x) % 65 = 0) := by
    intro x _ q
    change ((2 ^ 65 - 1) <<< (65 * x) ||| colS <<< x).testBit q = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      Bool.and_eq_true, Bool.and_eq_true, Nat.testBit_two_pow_sub_one, colS_testBit]
    simp only [decide_eq_true_eq]
    omega
  have e : ∀ x, Nat.shiftLeft (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 x))
      (Nat.shiftLeft colS x)) (Nat.mul 4225 x) =
      (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 x)) (Nat.shiftLeft colS x)) <<<
        (4225 * x) := fun _ => rfl
  simp only [e]
  have hz := z.isLt
  constructor
  · rintro ⟨x, hx, h⟩
    have hhi : ∀ q, 4225 ≤ q →
        (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 x)) (Nat.shiftLeft colS x)).testBit q =
          false := by
      intro q hq
      cases h : (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 x))
        (Nat.shiftLeft colS x)).testBit q
      · rfl
      · have := (hA x hx q).1 h
        omega
    rw [shift_testBit hhi _ _ hp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hxz, h⟩ := h
    rw [hA x hx] at h
    subst hxz
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_ofNat]
    omega
  · intro h
    have hhi : ∀ q, 4225 ≤ q →
        (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 z)) (Nat.shiftLeft colS z)).testBit q =
          false := by
      intro q hq
      cases h : (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 z))
        (Nat.shiftLeft colS z)).testBit q
      · rfl
      · have := (hA z hz q).1 h
        omega
    refine ⟨z, hz, ?_⟩
    rw [shift_testBit hhi _ _ hp, Bool.and_eq_true, decide_eq_true_eq, hA z hz]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_ofNat] at h
    omega

theorem primitive_of {R : ℕ → ℕ} (hR : rowsOK R = true) (hP : primS R = true) :
    minusQuandlePrimitiveCheck () = true := by
  have hS := rep_stepS hR (rep_stepS hR rep_initS)
  simp only [primS, force_eq] at hP
  have key : ∀ a b, a < 65 → b < 65 → a ≠ b →
      Nat.iterate minusQuandleStepFast 2
        ({Fin.ofNat 65 a, Fin.ofNat 65 b} : Finset (Fin 65)) = Finset.univ := by
    intro a b ha hb hab
    have hp : 65 * a + b < 4225 := by omega
    have h1 : (65 * a + b) / 65 = a := by omega
    have h2 : (65 * a + b) % 65 = b := by omega
    apply Finset.eq_univ_of_forall
    intro x
    have hx := allF_spec hP x.isLt
    rw [Nat.beq_eq] at hx
    have hb' := congrArg (fun n => n.testBit (65 * a + b)) hx
    change (lane 4225 (stepS R (stepS R initS)) x ||| diagS).testBit (65 * a + b) =
      (2 ^ 4225 - 1).testBit (65 * a + b) at hb'
    simp only [Nat.testBit_or, Nat.testBit_two_pow_sub_one, hp, decide_true] at hb'
    have hd : diagS.testBit (65 * a + b) = false := by
      cases h : diagS.testBit (65 * a + b)
      · rfl
      · have := (diagS_testBit _).1 h
        omega
    rw [hd, Bool.or_false] at hb'
    have := (lane_rep hS x hp).1 hb'
    rw [h1, h2] at this
    exact this
  rw [minusQuandlePrimitiveCheck, List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  rw [List.mem_range] at ha hb
  by_cases hab : a = b
  · simp [hab]
  · have hne : (a == b) = false := by simpa using hab
    rw [hne, if_neg (by simp), beq_iff_eq]
    exact key a b ha hb hab

theorem perpA_spec {R D : ℕ → ℕ} (hR : rowsOK R = true) (hD : derivOK D = true) {a : ℕ}
    (ha : a < 65) (h : perpA R D a = true) : minusQuandlePerpOK ⟨a, ha⟩ := by
  simp only [perpA, force_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hseed, hinj⟩, hder⟩, hc⟩ := h
  have hseq : ∀ t, t < 65 → minusQuandleSeq a t = dq D a t % 65 := fun t ht => seq_eq hD ha ht
  have hcode : ∀ t, t < 65 → minusQuandleCode a t = dq D a t / 65 := fun t ht => code_eq hD ha ht
  have hT : ∀ i j, i < 65 → j < 65 → minusQuandleT i j = tq R i j :=
    fun i j hi hj => (tq_spec hR hi hj).1
  have hTlt : ∀ i j, i < 65 → j < 65 → tq R i j < 65 := fun i j hi hj => (tq_spec hR hi hj).2
  have hmod : ∀ t, dq D a t % 65 < 65 := fun t => Nat.mod_lt _ (by norm_num)
  have hinjN : ∀ i j, i < 65 → j < 65 → minusQuandleSeq a i = minusQuandleSeq a j → i = j := by
    intro i j hi hj hij
    rw [hseq i hi, hseq j hj] at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hinj i hi j hj
      simp [hlt, hij] at this
    · have := hinj j hj i hi
      simp [hlt, hij] at this
  have hsrc : ∀ t, t < 65 → 2 ≤ minusQuandleCode a t →
      (minusQuandleCode a t - 2) / 65 < t ∧ (minusQuandleCode a t - 2) % 65 < t ∧
        minusQuandleT (minusQuandleSeq a ((minusQuandleCode a t - 2) / 65))
          (minusQuandleSeq a ((minusQuandleCode a t - 2) % 65)) = minusQuandleSeq a t := by
    intro t ht h2
    have h := hder t ht
    rw [hcode t ht] at h2
    have h0 : (dq D a t / 65 == 0) = false := by simp; omega
    have h1 : (dq D a t / 65 == 1) = false := by simp; omega
    simp only [h0, h1, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨⟨hx, hy⟩, hv⟩ := h
    refine ⟨by rw [hcode t ht]; exact hx, by rw [hcode t ht]; exact hy, ?_⟩
    rw [hcode t ht, hseq _ (by omega), hseq _ (by omega), hseq t ht,
      hT _ _ (hmod _) (hmod _), hv]
  have hsurj : ∀ p, p < 65 → ∃ t, t < 65 ∧ minusQuandleSeq a t = p := by
    let f : Fin 65 → Fin 65 := fun t => ⟨minusQuandleSeq a t, by rw [hseq t t.isLt]; exact hmod _⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext (hinjN i j i.isLt j.isLt (congrArg Fin.val hij))
    intro p hp
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hf) ⟨p, hp⟩
    exact ⟨t, t.isLt, congrArg Fin.val ht⟩
  have hmk : ∀ c d, recOK R D a c d = true → ∀ p, p < 65 →
      (minusQuandleMkD a c)[p]! = lane 7 d p ∧ lane 7 d p < 65 := by
    intro c d hrec
    have hr : ∀ t, t < 65 → lane 7 d (dq D a t % 65) < 65 ∧
        lane 7 d (dq D a t % 65) = (if (dq D a t / 65 == 0) = true then dq D a t % 65
          else if (dq D a t / 65 == 1) = true then c
          else tq R (lane 7 d (dq D a ((dq D a t / 65 - 2) / 65) % 65))
            (lane 7 d (dq D a ((dq D a t / 65 - 2) % 65) % 65))) := by
      intro t ht
      have := List.all_eq_true.1 hrec t (List.mem_range.2 ht)
      simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
    have hpos : ∀ t, t < 65 → (minusQuandleMkD a c)[minusQuandleSeq a t]! =
        lane 7 d (minusQuandleSeq a t) := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro ht
        rw [minusQuandleMkD_get a c t ht (by rw [hseq t ht]; exact hmod _) hinjN
          (fun h2 => ⟨(hsrc t ht h2).1, (hsrc t ht h2).2.1⟩)]
        rw [hseq t ht, (hr t ht).2, hcode t ht]
        by_cases h0 : dq D a t / 65 = 0
        · simp [h0]
        · by_cases h1 : dq D a t / 65 = 1
          · simp [h1]
          · have h2 : 2 ≤ minusQuandleCode a t := by rw [hcode t ht]; omega
            obtain ⟨hx, hy, -⟩ := hsrc t ht h2
            rw [hcode t ht] at hx hy
            simp only [h0, h1, if_false, beq_iff_eq]
            rw [ih _ hx (by omega), ih _ hy (by omega), hseq _ (by omega), hseq _ (by omega)]
            exact hT _ _ ((hr _ (by omega)).1) ((hr _ (by omega)).1)
    intro p hp
    obtain ⟨t, ht, rfl⟩ := hsurj p hp
    refine ⟨hpos t ht, ?_⟩
    rw [hseq t ht]
    exact (hr t ht).1
  have hseedA : minusQuandleSeed[a]! = seedT a := rfl
  refine ⟨hseedA ▸ hseed, fun t => by rw [hseq t t.isLt]; exact hmod _,
    fun i j hij => Fin.ext (hinjN i j i.isLt j.isLt hij), ?_, ?_,
    fun t h2 => hsrc t t.isLt h2, ?_⟩
  · intro t h0
    have h := hder t t.isLt
    rw [hcode t t.isLt] at h0
    simp only [h0, beq_self_eq_true, if_true, beq_iff_eq] at h
    simp only [Fin.val_mk]
    rw [hseq t t.isLt, hT _ _ ha (hmod _), h]
  · intro t h1
    have h := hder t t.isLt
    rw [hcode t t.isLt] at h1
    simp only [h1, Nat.one_ne_zero, beq_iff_eq, if_false, if_true, decide_true,
      Bool.false_eq_true] at h
    rw [hseq t t.isLt]
    exact h
  · intro c
    have h := hc c c.isLt
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    simp only [Fin.val_mk]
    rcases h with (h | h) | ⟨hrec, hbad⟩
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      rw [h]
      exact (hT _ _ ha hseed).symm
    · refine Or.inr (Or.inr ?_)
      obtain ⟨i, hi, hi'⟩ := List.any_eq_true.1 hbad
      obtain ⟨j, hj, hij⟩ := List.any_eq_true.1 hi'
      rw [List.mem_range] at hi hj
      refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_⟩
      have hm := hmk c _ hrec
      change (minusQuandleMkD a c)[minusQuandleT i j]! ≠
        minusQuandleT ((minusQuandleMkD a c)[i]!) ((minusQuandleMkD a c)[j]!)
      rw [(hm i hi).1, (hm j hj).1, hT _ _ hi hj, (hm _ (hTlt _ _ hi hj)).1,
        hT _ _ (hm i hi).2 (hm j hj).2]
      simpa using hij

theorem perp_of {R D : ℕ → ℕ} (hR : rowsOK R = true) (hD : derivOK D = true)
    (hP : ∀ a, a < 65 → perpA R D a = true) : minusQuandlePerpCheck () = true := by
  rw [minusQuandlePerpCheck, List.all_eq_true]
  intro a ha
  rw [List.mem_range] at ha
  have hfa : (Fin.ofNat 65 a : Fin 65) = ⟨a, ha⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt ha])
  rw [hfa]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := perpA_spec hR hD ha (hP a ha)
  simp only [minusQuandlePerpOKBool, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨h1, fun t ht => h2 ⟨t, ht⟩⟩, fun i hi j hj hij => ?_⟩,
    fun t ht => h4 ⟨t, ht⟩⟩, fun t ht => h5 ⟨t, ht⟩⟩, fun t ht => h6 ⟨t, ht⟩⟩,
    fun c hc => h7 ⟨c, hc⟩⟩
  exact congrArg Fin.val (h3 ⟨i, hi⟩ ⟨j, hj⟩ hij)

theorem perpOK_spec {R D : ℕ → ℕ} {lo hi : ℕ} (h : perpOK R D lo hi = true) {a : ℕ}
    (hla : lo ≤ a) (hah : a < hi) : perpA R D a = true :=
  List.all_eq_true.1 h a (List.mem_map.2 ⟨a - lo, List.mem_range.2 (by omega), by omega⟩)

end CFSG.KC.MinusQuandle
