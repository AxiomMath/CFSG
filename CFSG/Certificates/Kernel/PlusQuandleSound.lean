module

public import Certificates.Data.Kernel.PlusQuandle

public section

namespace CFSG.KC.PlusQuandle

open CFSG.OddTranspositions.PartThree CFSG.KD.PlusQuandle

@[simp] theorem force_eq {β : Sort _} (y : ℕ) (k : ℕ → β) : force y k = k y := by
  cases y <;> rfl

theorem getElem!_of_map_eq {f : ℕ → ℕ} {A : Array ℕ} (h : (List.range 60).map f = A.toList)
    {j : ℕ} (hj : j < 60) : A[j]! = f j := by
  rcases A with ⟨L⟩
  simp only at h
  subst h
  simp [hj]

theorem tq_spec {R : ℕ → ℕ} (h : rowsOK R = true) {i j : ℕ} (hi : i < 60) (hj : j < 60) :
    plusQuandleT i j = tq R i j ∧ tq R i j < 60 := by
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [Bool.and_eq_true, beq_iff_eq] at h1
  refine ⟨getElem!_of_map_eq h1.1 hj, ?_⟩
  have h2 := List.all_eq_true.1 h1.2 j (List.mem_range.2 hj)
  simpa using h2

theorem dq_spec {D : ℕ → ℕ} (h : derivOK D = true) {a t : ℕ} (ha : a < 60) (ht : t < 60) :
    (plusQuandleDeriv[a]!)[t]! = dq D a t := by
  have h1 := List.all_eq_true.1 h a (List.mem_range.2 ha)
  rw [beq_iff_eq] at h1
  exact getElem!_of_map_eq h1 ht

theorem seq_eq {D : ℕ → ℕ} (h : derivOK D = true) {a t : ℕ} (ha : a < 60) (ht : t < 60) :
    plusQuandleSeq a t = dq D a t % 60 := by
  rw [plusQuandleSeq, dq_spec h ha ht]

theorem code_eq {D : ℕ → ℕ} (h : derivOK D = true) {a t : ℕ} (ha : a < 60) (ht : t < 60) :
    plusQuandleCode a t = dq D a t / 60 := by
  rw [plusQuandleCode, dq_spec h ha ht]

theorem tf_val {R : ℕ → ℕ} (hR : rowsOK R = true) (j y : Fin 60) :
    (plusQuandleTf j y : ℕ) = tq R j y := by
  obtain ⟨h1, h2⟩ := tq_spec hR j.isLt y.isLt
  rw [plusQuandleTf, Fin.val_ofNat, h1, Nat.mod_eq_of_lt h2]

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

theorem shift_testBit {n : ℕ} (hn : ∀ q, 3600 ≤ q → n.testBit q = false) (t z : ℕ) {p : ℕ}
    (hp : p < 3600) :
    (n <<< (3600 * t)).testBit (3600 * z + p) = (decide (t = z) && n.testBit p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases htz : t = z
  · subst htz
    simp [show 3600 * t + p - 3600 * t = p by omega]
  · rcases Nat.lt_or_gt_of_ne htz with h | h
    · have := hn (3600 * z + p - 3600 * t) (by omega)
      simp [htz, this]
    · simp [htz]
      omega

theorem lane_high (n i q : ℕ) (hq : 3600 ≤ q) : (lane 3600 n i).testBit q = false := by
  rw [lane_testBit]
  simp [show ¬ q < 3600 by omega]

def PRep (S : ℕ) (K : ℕ → Finset (Fin 60)) : Prop :=
  ∀ (x : Fin 60) (p : ℕ), p < 3600 → (S.testBit (3600 * x + p) = true ↔ x ∈ K p)

theorem lane_rep {S : ℕ} {K : ℕ → Finset (Fin 60)} (hS : PRep S K) (x : Fin 60) {p : ℕ}
    (hp : p < 3600) : (lane 3600 S x).testBit p = true ↔ x ∈ K p := by
  rw [lane_testBit]
  simp only [hp, decide_true, Bool.true_and]
  exact hS x p hp

theorem rep_imgS {R : ℕ → ℕ} (hR : rowsOK R = true) {S : ℕ} {K : ℕ → Finset (Fin 60)}
    (hS : PRep S K) (j : Fin 60) :
    PRep (imgS R j S) (fun p => (K p).image (plusQuandleTf j)) := by
  intro z p hp
  simp only [imgS, force_eq]
  rw [orF_testBit]
  have e : ∀ i, Nat.shiftLeft (lane 3600 S i) (Nat.mul 3600 (lane 7 (R j) i)) =
      lane 3600 S i <<< (3600 * tq R j i) := fun _ => rfl
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

theorem rep_stepS {R : ℕ → ℕ} (hR : rowsOK R = true) {S : ℕ} {K : ℕ → Finset (Fin 60)}
    (hS : PRep S K) : PRep (stepS R S) (fun p => plusQuandleStepF (K p)) := by
  intro z p hp
  have hI := rep_imgS hR hS
  have hN : ∀ j : Fin 60, ∀ q, (orF 60 fun y => lane 3600 (imgS R j S &&& S) y).testBit q =
      true ↔ q < 3600 ∧ (((K q).image (plusQuandleTf j)) ∩ K q).Nonempty := by
    intro j q
    rw [orF_testBit]
    simp only [lane_testBit, Nat.testBit_and, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, hq, h1, h2⟩
      exact ⟨hq, ⟨y, hy⟩, Finset.mem_inter.2 ⟨(hI j ⟨y, hy⟩ q hq).1 h1, (hS ⟨y, hy⟩ q hq).1 h2⟩⟩
    · rintro ⟨hq, y, hy⟩
      rw [Finset.mem_inter] at hy
      exact ⟨y, y.isLt, hq, (hI j y q hq).2 hy.1, (hS y q hq).2 hy.2⟩
  have hB : ∀ j : Fin 60, (orF 60 fun y => Nat.shiftLeft
      (orF 60 fun y => lane 3600 (imgS R j S &&& S) y) (Nat.mul 3600 y)).testBit
      (3600 * z + p) = true ↔ (((K p).image (plusQuandleTf j)) ∩ K p).Nonempty := by
    intro j
    rw [orF_testBit]
    have hhi : ∀ q, 3600 ≤ q →
        (orF 60 fun y => lane 3600 (imgS R j S &&& S) y).testBit q = false := by
      intro q hq
      cases h : (orF 60 fun y => lane 3600 (imgS R j S &&& S) y).testBit q
      · rfl
      · exact absurd ((hN j q).1 h).1 (by omega)
    have e : ∀ y, Nat.shiftLeft (orF 60 fun y => lane 3600 (imgS R j S &&& S) y)
        (Nat.mul 3600 y) = (orF 60 fun y => lane 3600 (imgS R j S &&& S) y) <<< (3600 * y) :=
      fun _ => rfl
    simp only [e, shift_testBit hhi _ _ hp, Bool.and_eq_true, decide_eq_true_eq, hN j p, hp,
      true_and]
    constructor
    · rintro ⟨_, _, _, h⟩
      exact h
    · intro h
      exact ⟨z, z.isLt, rfl, h⟩
  simp only [stepS, force_eq]
  change (S ||| orF 60 fun j => imgS R j S &&& orF 60 fun y => Nat.shiftLeft
      (orF 60 fun y => lane 3600 (imgS R j S &&& S) y) (Nat.mul 3600 y)).testBit
      (3600 * z + p) = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true, orF_testBit, hS z p hp]
  simp only [Nat.testBit_and, Bool.and_eq_true, plusQuandleStepF, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨j, hj, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨⟨j, hj⟩, ?_⟩
      rw [if_pos ((hB ⟨j, hj⟩).1 h2)]
      exact (hI ⟨j, hj⟩ z p hp).1 h1
  · rintro (h | ⟨j, h⟩)
    · exact Or.inl h
    · by_cases hne : ((K p).image (plusQuandleTf j) ∩ K p).Nonempty
      · rw [if_pos hne] at h
        exact Or.inr ⟨j, j.isLt, (hI j z p hp).2 h, (hB j).2 hne⟩
      · rw [if_neg hne] at h
        simp at h

theorem colS_testBit (q : ℕ) : colS.testBit q = true ↔ q < 3600 ∧ q % 60 = 0 := by
  rw [colS, orF_testBit]
  change (∃ k < 60, (1 <<< (60 * k)).testBit q = true) ↔ _
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, h1⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨q / 60, by omega, by omega⟩

theorem diagS_testBit (q : ℕ) : diagS.testBit q = true ↔ q < 3600 ∧ q / 60 = q % 60 := by
  rw [diagS, orF_testBit]
  change (∃ k < 60, (1 <<< (61 * k)).testBit q = true) ↔ _
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, h1⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨q / 60, by omega, by omega⟩

theorem rep_initS :
    PRep initS (fun p => {Fin.ofNat 60 (p / 60), Fin.ofNat 60 (p % 60)}) := by
  intro z p hp
  simp only [initS, force_eq]
  rw [orF_testBit]
  have hA : ∀ x, x < 60 → ∀ q,
      (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 x)) (Nat.shiftLeft colS x)).testBit q =
        true ↔ (60 * x ≤ q ∧ q < 60 * x + 60) ∨ (x ≤ q ∧ q < 3600 ∧ (q - x) % 60 = 0) := by
    intro x _ q
    change ((2 ^ 60 - 1) <<< (60 * x) ||| colS <<< x).testBit q = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      Bool.and_eq_true, Bool.and_eq_true, Nat.testBit_two_pow_sub_one, colS_testBit]
    simp only [decide_eq_true_eq]
    omega
  have e : ∀ x, Nat.shiftLeft (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 x))
      (Nat.shiftLeft colS x)) (Nat.mul 3600 x) =
      (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 x)) (Nat.shiftLeft colS x)) <<<
        (3600 * x) := fun _ => rfl
  simp only [e]
  have hz := z.isLt
  constructor
  · rintro ⟨x, hx, h⟩
    have hhi : ∀ q, 3600 ≤ q →
        (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 x)) (Nat.shiftLeft colS x)).testBit q =
          false := by
      intro q hq
      cases h : (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 x))
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
    have hhi : ∀ q, 3600 ≤ q →
        (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 z)) (Nat.shiftLeft colS z)).testBit q =
          false := by
      intro q hq
      cases h : (Nat.lor (Nat.shiftLeft (2 ^ 60 - 1) (Nat.mul 60 z))
        (Nat.shiftLeft colS z)).testBit q
      · rfl
      · have := (hA z hz q).1 h
        omega
    refine ⟨z, hz, ?_⟩
    rw [shift_testBit hhi _ _ hp, Bool.and_eq_true, decide_eq_true_eq, hA z hz]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_ofNat] at h
    omega

theorem primitive_of {R : ℕ → ℕ} (hR : rowsOK R = true) (hP : primS R = true) :
    plusQuandlePrimitiveCheck () = true := by
  have hS := rep_stepS hR (rep_stepS hR rep_initS)
  simp only [primS, force_eq] at hP
  have key : ∀ a b, a < 60 → b < 60 → a ≠ b →
      Nat.iterate plusQuandleStepFast 2
        ({Fin.ofNat 60 a, Fin.ofNat 60 b} : Finset (Fin 60)) = Finset.univ := by
    intro a b ha hb hab
    have hp : 60 * a + b < 3600 := by omega
    have h1 : (60 * a + b) / 60 = a := by omega
    have h2 : (60 * a + b) % 60 = b := by omega
    apply Finset.eq_univ_of_forall
    intro x
    have hx := allF_spec hP x.isLt
    rw [Nat.beq_eq] at hx
    have hb' := congrArg (fun n => n.testBit (60 * a + b)) hx
    change (lane 3600 (stepS R (stepS R initS)) x ||| diagS).testBit (60 * a + b) =
      (2 ^ 3600 - 1).testBit (60 * a + b) at hb'
    simp only [Nat.testBit_or, Nat.testBit_two_pow_sub_one, hp, decide_true] at hb'
    have hd : diagS.testBit (60 * a + b) = false := by
      cases h : diagS.testBit (60 * a + b)
      · rfl
      · have := (diagS_testBit _).1 h
        omega
    rw [hd, Bool.or_false] at hb'
    have := (lane_rep hS x hp).1 hb'
    rw [h1, h2] at this
    exact this
  rw [plusQuandlePrimitiveCheck, List.all_eq_true]
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
    (ha : a < 60) (h : perpA R D a = true) : plusQuandlePerpOK ⟨a, ha⟩ := by
  simp only [perpA, force_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hseed, hinj⟩, hder⟩, hc⟩ := h
  have hseq : ∀ t, t < 60 → plusQuandleSeq a t = dq D a t % 60 := fun t ht => seq_eq hD ha ht
  have hcode : ∀ t, t < 60 → plusQuandleCode a t = dq D a t / 60 := fun t ht => code_eq hD ha ht
  have hT : ∀ i j, i < 60 → j < 60 → plusQuandleT i j = tq R i j :=
    fun i j hi hj => (tq_spec hR hi hj).1
  have hTlt : ∀ i j, i < 60 → j < 60 → tq R i j < 60 := fun i j hi hj => (tq_spec hR hi hj).2
  have hmod : ∀ t, dq D a t % 60 < 60 := fun t => Nat.mod_lt _ (by norm_num)
  have hinjN : ∀ i j, i < 60 → j < 60 → plusQuandleSeq a i = plusQuandleSeq a j → i = j := by
    intro i j hi hj hij
    rw [hseq i hi, hseq j hj] at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hinj i hi j hj
      simp [hlt, hij] at this
    · have := hinj j hj i hi
      simp [hlt, hij] at this
  have hsrc : ∀ t, t < 60 → 2 ≤ plusQuandleCode a t →
      (plusQuandleCode a t - 2) / 60 < t ∧ (plusQuandleCode a t - 2) % 60 < t ∧
        plusQuandleT (plusQuandleSeq a ((plusQuandleCode a t - 2) / 60))
          (plusQuandleSeq a ((plusQuandleCode a t - 2) % 60)) = plusQuandleSeq a t := by
    intro t ht h2
    have h := hder t ht
    rw [hcode t ht] at h2
    have h0 : (dq D a t / 60 == 0) = false := by simp; omega
    have h1 : (dq D a t / 60 == 1) = false := by simp; omega
    simp only [h0, h1, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨⟨hx, hy⟩, hv⟩ := h
    refine ⟨by rw [hcode t ht]; exact hx, by rw [hcode t ht]; exact hy, ?_⟩
    rw [hcode t ht, hseq _ (by omega), hseq _ (by omega), hseq t ht,
      hT _ _ (hmod _) (hmod _), hv]
  have hsurj : ∀ p, p < 60 → ∃ t, t < 60 ∧ plusQuandleSeq a t = p := by
    let f : Fin 60 → Fin 60 := fun t => ⟨plusQuandleSeq a t, by rw [hseq t t.isLt]; exact hmod _⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext (hinjN i j i.isLt j.isLt (congrArg Fin.val hij))
    intro p hp
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hf) ⟨p, hp⟩
    exact ⟨t, t.isLt, congrArg Fin.val ht⟩
  have hmk : ∀ c d, recOK R D a c d = true → ∀ p, p < 60 →
      (plusQuandleMkD a c)[p]! = lane 7 d p ∧ lane 7 d p < 60 := by
    intro c d hrec
    have hr : ∀ t, t < 60 → lane 7 d (dq D a t % 60) < 60 ∧
        lane 7 d (dq D a t % 60) = (if (dq D a t / 60 == 0) = true then dq D a t % 60
          else if (dq D a t / 60 == 1) = true then c
          else tq R (lane 7 d (dq D a ((dq D a t / 60 - 2) / 60) % 60))
            (lane 7 d (dq D a ((dq D a t / 60 - 2) % 60) % 60))) := by
      intro t ht
      have := List.all_eq_true.1 hrec t (List.mem_range.2 ht)
      simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
    have hpos : ∀ t, t < 60 → (plusQuandleMkD a c)[plusQuandleSeq a t]! =
        lane 7 d (plusQuandleSeq a t) := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro ht
        rw [plusQuandleMkD_get a c t ht (by rw [hseq t ht]; exact hmod _) hinjN
          (fun h2 => ⟨(hsrc t ht h2).1, (hsrc t ht h2).2.1⟩)]
        rw [hseq t ht, (hr t ht).2, hcode t ht]
        by_cases h0 : dq D a t / 60 = 0
        · simp [h0]
        · by_cases h1 : dq D a t / 60 = 1
          · simp [h1]
          · have h2 : 2 ≤ plusQuandleCode a t := by rw [hcode t ht]; omega
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
  have hseedA : plusQuandleSeed[a]! = seedT a := rfl
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
      change (plusQuandleMkD a c)[plusQuandleT i j]! ≠
        plusQuandleT ((plusQuandleMkD a c)[i]!) ((plusQuandleMkD a c)[j]!)
      rw [(hm i hi).1, (hm j hj).1, hT _ _ hi hj, (hm _ (hTlt _ _ hi hj)).1,
        hT _ _ (hm i hi).2 (hm j hj).2]
      simpa using hij

theorem perp_of {R D : ℕ → ℕ} (hR : rowsOK R = true) (hD : derivOK D = true)
    (hP : ∀ a, a < 60 → perpA R D a = true) : plusQuandlePerpCheck () = true := by
  rw [plusQuandlePerpCheck, List.all_eq_true]
  intro a ha
  rw [List.mem_range] at ha
  have hfa : (Fin.ofNat 60 a : Fin 60) = ⟨a, ha⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt ha])
  rw [hfa]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := perpA_spec hR hD ha (hP a ha)
  simp only [plusQuandlePerpOKBool, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨h1, fun t ht => h2 ⟨t, ht⟩⟩, fun i hi j hj hij => ?_⟩,
    fun t ht => h4 ⟨t, ht⟩⟩, fun t ht => h5 ⟨t, ht⟩⟩, fun t ht => h6 ⟨t, ht⟩⟩,
    fun c hc => h7 ⟨c, hc⟩⟩
  exact congrArg Fin.val (h3 ⟨i, hi⟩ ⟨j, hj⟩ hij)

theorem perpOK_spec {R D : ℕ → ℕ} {lo hi : ℕ} (h : perpOK R D lo hi = true) {a : ℕ}
    (hla : lo ≤ a) (hah : a < hi) : perpA R D a = true :=
  List.all_eq_true.1 h a (List.mem_map.2 ⟨a - lo, List.mem_range.2 (by omega), by omega⟩)

end CFSG.KC.PlusQuandle
