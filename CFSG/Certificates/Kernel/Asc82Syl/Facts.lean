module

public import CFSG.Certificates.Kernel.Asc82Syl.Codes

public section

namespace CFSG.KS.Asc82Syl

open CFSG.KD.Asc82Syl CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop

theorem keysL_succ (WP p n : Nat) :
    keysL WP p (n + 1) = Nat.mod (canonK (wAt WP n)) p :: keysL WP p n := rfl

theorem mem_keysL (WP p : Nat) : ∀ n e, e < n → Nat.mod (canonK (wAt WP e)) p ∈ keysL WP p n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    rw [keysL_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact List.mem_cons_of_mem _ (mem_keysL WP p n e h)
    · exact List.mem_cons_self

theorem keys_inj (WP p : Nat) : ∀ n, (keysL WP p n).Nodup → ∀ e < n, ∀ f < n,
    canonK (wAt WP e) = canonK (wAt WP f) → e = f
  | 0, _, e, he, _, _, _ => absurd he (Nat.not_lt_zero _)
  | n + 1, h, e, he, f, hf, hef => by
    rw [keysL_succ, List.nodup_cons] at h
    obtain ⟨hn, hnd⟩ := h
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | rfl
    · exact keys_inj WP p n hnd e he f hf hef
    · have hm := mem_keysL WP p _ e he
      rw [hef] at hm
      exact absurd hm hn
    · have hm := mem_keysL WP p _ f hf
      rw [← hef] at hm
      exact absurd hm hn
    · rfl

theorem keyK_sound {WP p n : Nat} (h : keyK WP p n = true)
    (hc : ∀ e < n, Canon3 36 (wAt WP e)) {e f : Nat} (he : e < n) (hf : f < n)
    (hm : mat (wAt WP e) = mat (wAt WP f) ∨ mat (wAt WP e) = -mat (wAt WP f)) : e = f :=
  keys_inj WP p n (CFSG.Decide.nodup_of_bitsetNodup_nat h) e he f hf
    (canonK_eq (hc e he) (hc f hf) hm)

theorem conjL_sound {WP k j : Nat} : ∀ (C : List Nat) (i0 : Nat), conjL WP k j C i0 = true →
    ∀ t < C.length, C.getD t 0 < 2 ^ j ∧ (j < k → C.getD t 0 = 2 ^ (i0 + t)) ∧
      (i0 + t < k → C.getD t 0 < 2 ^ k) ∧
      eqC (MUL (wAt WP (2 ^ (i0 + t))) (wAt WP (2 ^ j)))
        (MUL (wAt WP (2 ^ j)) (wAt WP (C.getD t 0))) = true
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | c :: C, i0, h, t, ht => by
    obtain ⟨h1, h⟩ := bAnd_a82 h
    obtain ⟨h2, h⟩ := bAnd_a82 h
    obtain ⟨h3, h⟩ := bAnd_a82 h
    obtain ⟨h4, h5⟩ := bAnd_a82 h
    rcases t with _ | t
    · simp only [pw_eq] at h1 h2 h3 h4
      refine ⟨Nat.blt_eq.mp h1, fun hj => ?_, fun hi => ?_, h4⟩
      · rw [Nat.blt_eq.mpr hj] at h2
        exact Nat.eq_of_beq_eq_true h2
      · rw [Nat.add_zero, ← Nat.blt_eq] at hi
        rw [hi] at h3
        exact Nat.blt_eq.mp h3
    · have e1 : i0 + (t + 1) = i0 + 1 + t := by omega
      rw [e1]
      exact conjL_sound C (i0 + 1) h5 t (by simpa using ht)

theorem relL_sound {WP k : Nat} : ∀ (R : List (Nat × List Nat)) (j : Nat), relL WP k R j = true →
    ∀ i < R.length, (R.getD i (0, [])).1 < 2 ^ (j + i) ∧
      eqC (MUL (wAt WP (2 ^ (j + i))) (wAt WP (2 ^ (j + i)))) (wAt WP (R.getD i (0, [])).1) = true ∧
      (R.getD i (0, [])).2.length = j + i ∧ conjL WP k (j + i) (R.getD i (0, [])).2 0 = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r :: R, j, h, i, hi => by
    obtain ⟨h1, h⟩ := bAnd_a82 h
    obtain ⟨h2, h⟩ := bAnd_a82 h
    obtain ⟨h3, h⟩ := bAnd_a82 h
    obtain ⟨h4, h5⟩ := bAnd_a82 h
    rcases i with _ | i
    · simp only [pw_eq] at h1 h2
      exact ⟨Nat.blt_eq.mp h1, h2, Nat.eq_of_beq_eq_true h3, h4⟩
    · have e1 : j + (i + 1) = j + 1 + i := by omega
      rw [e1]
      exact relL_sound R (j + 1) h5 i (by simpa using hi)

theorem relK_sound {WP k m : Nat} {R : List (Nat × List Nat)} (h : relK WP k m R = true) :
    ∀ j < m, (R.getD j (0, [])).1 < 2 ^ j ∧
      eqC (MUL (wAt WP (2 ^ j)) (wAt WP (2 ^ j))) (wAt WP (R.getD j (0, [])).1) = true ∧
      ∀ i < j, ((R.getD j (0, [])).2.getD i 0 < 2 ^ j ∧
        (j < k → (R.getD j (0, [])).2.getD i 0 = 2 ^ i) ∧
        (i < k → (R.getD j (0, [])).2.getD i 0 < 2 ^ k) ∧
        eqC (MUL (wAt WP (2 ^ i)) (wAt WP (2 ^ j)))
          (MUL (wAt WP (2 ^ j)) (wAt WP ((R.getD j (0, [])).2.getD i 0))) = true) := by
  obtain ⟨hl, h⟩ := bAnd_a82 h
  have hl' : R.length = m := Nat.eq_of_beq_eq_true hl
  intro j hj
  obtain ⟨h1, h2, h3, h4⟩ := relL_sound R 0 h j (by omega)
  rw [Nat.zero_add] at h1 h2 h3 h4
  refine ⟨h1, h2, fun i hi => ?_⟩
  have := conjL_sound _ 0 h4 i (by omega)
  rw [Nat.zero_add] at this
  exact this

theorem shl_eq (u k : Nat) : Nat.shiftLeft u k = u * 2 ^ k := Nat.shiftLeft_eq u k

theorem qtK_sound {WP QM QF k q : Nat} (h : qtK WP QM QF k q = true) (hq : q ≤ 16) :
    ∀ u < q, ∀ v < q, fld(QF, 8 * (q * u + v), 255) < 2 ^ k ∧
      eqC (MUL (wAt WP (u * 2 ^ k)) (wAt WP (v * 2 ^ k)))
        (wAt WP (fld(QF, 8 * (q * u + v), 255) + fld(QM, 4 * (q * u + v), 15) * 2 ^ k)) = true := by
  intro u hu v hv
  have ht : q * u + v < q * q := by
    have := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hu)
    rw [Nat.mul_succ] at this
    omega
  have hb := allBelow_a82 h (by
    have := Nat.mul_le_mul hq hq
    omega) _ ht
  have hdiv : (q * u + v) / q = u := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
  have hmod : (q * u + v) % q = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  change Bool.rec (motive := fun _ => Bool) false _ (Nat.blt _ (pw k)) = true at hb
  obtain ⟨h1, h2⟩ := bAnd_a82 hb
  change Nat.div (q * u + v) q = u at hdiv
  change Nat.mod (q * u + v) q = v at hmod
  rw [hdiv, hmod, shl_eq, shl_eq, shl_eq] at h2
  rw [pw_eq] at h1
  exact ⟨Nat.blt_eq.mp h1, h2⟩

theorem ctK_sound {WP CT k q : Nat} (h : ctK WP CT k q = true) (hq : q ≤ 16) (hk : k ≤ 6) :
    ∀ u < q, ∀ f < 2 ^ k, fld(CT, 64 * u + f, 1) =
      Bool.rec (motive := fun _ => Nat) 0 1
        (eqC (MUL (wAt WP f) (wAt WP (u * 2 ^ k))) (MUL (wAt WP (u * 2 ^ k)) (wAt WP f))) := by
  intro u hu f hf
  have hf64 : f < 64 := Nat.lt_of_lt_of_le hf (by
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hk
      _ = 64 := rfl)
  have ht : 64 * u + f < q * 64 := by omega
  have hb := allBelow_a82 h (by change q * 64 ≤ 64 * 16; omega) _ ht
  have hdiv : Nat.div (64 * u + f) 64 = u := by
    change (64 * u + f) / 64 = u
    omega
  have hmod : Nat.mod (64 * u + f) 64 = f := by
    change (64 * u + f) % 64 = f
    omega
  change Bool.rec (motive := fun _ => Bool) true _ (Nat.blt (Nat.mod (64 * u + f) 64) (pw k)) = true
    at hb
  rw [hdiv, hmod, pw_eq, Nat.blt_eq.mpr hf, shl_eq] at hb
  exact Nat.eq_of_beq_eq_true hb

theorem omK_sound {WP OM k : Nat} (h : omK WP OM k = true) (hk : k ≤ 6) :
    ∀ f < 2 ^ k, fld(OM, f, 1) =
      Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (canonK (MUL (wAt WP f) (wAt WP f))) ONE) := by
  intro f hf
  have hb := allBelow_a82 h (by
    rw [pw_eq]
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hk
      _ = 64 * 1 := rfl) f (by rw [pw_eq]; exact hf)
  exact Nat.eq_of_beq_eq_true hb

theorem memF_sound {F : List (Nat × List Nat)} {X : Nat} (h : memF F X = true) :
    ∃ r ∈ F, r.1 = X := by
  induction F with
  | nil => exact absurd h Bool.false_ne_true
  | cons r F ih =>
    change Bool.rec (motive := fun _ => Bool) (memF F X) true (Nat.beq r.1 X) = true at h
    cases hb : Nat.beq r.1 X
    · rw [hb] at h
      obtain ⟨r', hr', e⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩
    · exact ⟨r, List.mem_cons_self, Nat.eq_of_beq_eq_true hb⟩

theorem recs_sound (P : Nat → List Nat → Bool) : ∀ L : List (Nat × List Nat),
    List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(P r.1 r.2, ih)) L = true →
    ∀ r ∈ L, P r.1 r.2 = true
  | [], _, r, hr => absurd hr List.not_mem_nil
  | s :: L, h, r, hr => by
    obtain ⟨h1, h2⟩ := bAnd_a82 h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h1
    · exact recs_sound P L h2 r hr

theorem recAnd_of (f : Nat → Bool) : ∀ n, (∀ i < n, f i = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false _ (f n) = true
    rw [h n (by omega)]
    exact recAnd_of f n (fun i hi => h i (by omega))

theorem allBelow_of {m hi : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) :
    allBelow m hi f = true := by
  unfold allBelow
  refine recAnd_of _ hi fun b _ => recAnd_of (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft b 6) l)) 64 fun l _ => ?_
  change Bool.rec (motive := fun _ => Bool) true _ (Nat.blt (Nat.add (Nat.shiftLeft b 6) l) m) = true
  cases hb : Nat.blt (Nat.add (Nat.shiftLeft b 6) l) m
  · rfl
  · exact h _ (Nat.blt_eq.mp hb)

theorem popK_eq (X : Nat) : ∀ n, popK X n = ((Finset.range n).filter (fun i => X.testBit i)).card
  | 0 => rfl
  | n + 1 => by
    change Nat.add (popK X n) (Nat.land (Nat.shiftRight X n) 1) = _
    rw [popK_eq X n, fld1_eq, Finset.range_add_one, Finset.filter_insert]
    cases h : X.testBit n
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      rfl

theorem extK_testBit (QM X x t : Nat) : ∀ q, (extK QM q X x).testBit t = true ↔
    (X.testBit t = true ∨ ∃ h < q, X.testBit h = true ∧ qm QM x h = t)
  | 0 => by simp [extK]
  | q + 1 => by
    change (Bool.rec (motive := fun _ => Nat) (extK QM q X x)
      (Nat.lor (extK QM q X x) (Nat.shiftLeft 1 (qm QM x q)))
      (Nat.beq (Nat.land (Nat.shiftRight X q) 1) 1)).testBit t = true ↔ _
    rw [fld1_eq]
    cases hq : X.testBit q
    · change (extK QM q X x).testBit t = true ↔ _
      rw [extK_testBit QM X x t q]
      constructor
      · rintro (h | ⟨h, hh, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, by omega, h1, h2⟩
      · rintro (h | ⟨h, hh, h1, h2⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
          · exact Or.inr ⟨h, hh, h1, h2⟩
          · rw [hq] at h1
            cases h1
    · change (Nat.lor (extK QM q X x) (Nat.shiftLeft 1 (qm QM x q))).testBit t = true ↔ _
      rw [lor_eq3, shl_eq3, Nat.testBit_or, Bool.or_eq_true, extK_testBit QM X x t q,
        Nat.one_shiftLeft, Nat.testBit_two_pow]
      constructor
      · rintro ((h | ⟨h, hh, h1, h2⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨h, by omega, h1, h2⟩
        · exact Or.inr ⟨q, by omega, hq, of_decide_eq_true h⟩
      · rintro (h | ⟨h, hh, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
          · exact Or.inl (Or.inr ⟨h, hh, h1, h2⟩)
          · exact Or.inr (decide_eq_true h2)

theorem bit1_of {X h : Nat} (e : Nat.beq (Nat.land (Nat.shiftRight X h) 1) 1 = true) :
    X.testBit h = true := by
  have := Nat.eq_of_beq_eq_true e
  rw [fld1_eq] at this
  cases hb : X.testBit h
  · rw [hb] at this
    cases this
  · rfl

theorem cents_testBit (CT k f : Nat) (hf : f < 2 ^ k) (hf64 : f < 64) : ∀ gens : List Nat,
    (cents CT k gens).testBit f = true ↔ ∀ g ∈ gens, CT.testBit (64 * g + f) = true
  | [] => by
    change (Nat.sub (pw (pw k)) 1).testBit f = true ↔ _
    rw [pw_eq, pw_eq]
    change (2 ^ 2 ^ k - 1).testBit f = true ↔ _
    rw [Nat.testBit_two_pow_sub_one]
    simp [hf]
  | g :: gens => by
    change (Nat.land (cents CT k gens)
      (Nat.land (Nat.shiftRight CT (Nat.mul 64 g)) (Nat.sub (Nat.shiftLeft 1 64) 1))).testBit f = true ↔ _
    rw [land_eq3, Nat.testBit_and, Bool.and_eq_true, cents_testBit CT k f hf hf64 gens, land_eq3,
      shr_eq3, mul_eq3, pow_sub_one_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight]
    simp only [hf64, decide_true, Bool.true_and, List.mem_cons, forall_eq_or_imp]
    exact And.comm

theorem subX_sound {q X : Nat} : ∀ {gens : List Nat}, subX q X gens = true →
    ∀ g ∈ gens, g < q ∧ X.testBit g = true
  | [], _, g, hg => absurd hg List.not_mem_nil
  | g :: gens, h, g', hg' => by
    obtain ⟨a1, a⟩ := bAnd_a82 h
    obtain ⟨a2, a3⟩ := bAnd_a82 a
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact ⟨Nat.blt_eq.mp a1, bit1_of a2⟩
    · exact subX_sound a3 g' hg'

theorem recK_sound {F : List (Nat × List Nat)} {QM CT OM k q bound : Nat} {flag : Bool}
    {X : Nat} {gens : List Nat} (h : recK F QM CT OM k q bound flag X gens = true) (hq : q ≤ 64) :
    X < 2 ^ q ∧ (∀ g ∈ gens, g < q ∧ X.testBit g = true) ∧
    popK (Bool.rec (motive := fun _ => Nat) (cents CT k gens) (Nat.land (cents CT k gens) OM) flag)
      (pw k) * popK X q ≤ bound ∧
    ∀ x < q, X.testBit x = false → X.testBit (qm QM x x) = true →
      (∀ h < q, X.testBit h = true → qm QM x h = qm QM h x) →
      ∃ r ∈ F, r.1 = extK QM q X x := by
  obtain ⟨h1, h⟩ := bAnd_a82 h
  obtain ⟨h2, h⟩ := bAnd_a82 h
  obtain ⟨h3, h4⟩ := bAnd_a82 h
  refine ⟨by rw [← pw_eq]; exact Nat.blt_eq.mp h1, ?_, Nat.le_of_ble_eq_true h3, ?_⟩
  · exact subX_sound h2
  · intro x hx hnx hsq hcomm
    have hb := allBelow_a82 h4 (by omega) x hx
    have c1 : Nat.beq (Nat.land (Nat.shiftRight X x) 1) 0 = true := by
      rw [fld1_eq, hnx]
      rfl
    have c2 : Nat.beq (Nat.land (Nat.shiftRight X (qm QM x x)) 1) 1 = true := by
      rw [fld1_eq, hsq]
      rfl
    have c3 : commX QM q X x = true := by
      unfold commX
      refine allBelow_of fun h hh => ?_
      cases hX : X.testBit h
      · have e : Nat.beq (Nat.land (Nat.shiftRight X h) 1) 1 = false := by
          rw [fld1_eq, hX]
          rfl
        change Bool.rec (motive := fun _ => Bool) true _ (Nat.beq (Nat.land (Nat.shiftRight X h) 1) 1) = true
        rw [e]
      · have e : Nat.beq (Nat.land (Nat.shiftRight X h) 1) 1 = true := by
          rw [fld1_eq, hX]
          rfl
        change Bool.rec (motive := fun _ => Bool) true _ (Nat.beq (Nat.land (Nat.shiftRight X h) 1) 1) = true
        rw [e]
        exact Nat.beq_eq_true_eq _ _ ▸ hcomm h hh hX
    change Bool.rec (motive := fun _ => Bool) true _ (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (commX QM q X x)
        (Nat.beq (Nat.land (Nat.shiftRight X (qm QM x x)) 1) 1))
      (Nat.beq (Nat.land (Nat.shiftRight X x) 1) 0)) = true at hb
    rw [c1, c2, c3] at hb
    exact memF_sound hb

theorem famK_sound {F : List (Nat × List Nat)} {QM CT OM k q bound : Nat} {flag : Bool}
    (h : famK F QM CT OM k q bound flag = true) :
    (∃ r ∈ F, r.1 = 1) ∧ ∀ r ∈ F, recK F QM CT OM k q bound flag r.1 r.2 = true := by
  obtain ⟨h1, h2⟩ := bAnd_a82 h
  exact ⟨memF_sound h1, recs_sound (recK F QM CT OM k q bound flag) F h2⟩

end CFSG.KS.Asc82Syl

end
