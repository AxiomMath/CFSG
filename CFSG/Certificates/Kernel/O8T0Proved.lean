module

public import CFSG.Certificates.Kernel.O8T0Defs
public import CFSG.Certificates.Kernel.O8Z4Proved

public section

namespace CFSG.KC.O8.T0Pf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8 CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf
  CFSG.KC.O8.S0Pf CFSG.KC.O8.Z4Pf CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] def VOK (v : Array ℕ) : Prop := ∀ k < 6, v.getD k 0 < 4

theorem vok_ofFn {f : Fin 6 → ℕ} (hf : ∀ k, f k < 4) : VOK (Array.ofFn f) := fun k hk => by
  rw [getD_ofFn6 _ _ hk]
  exact hf _

theorem add_bits : ∀ x < 4, ∀ y < 4, ((x + y) % 4).testBit 0 = (x.testBit 0 ^^ y.testBit 0) ∧
    ((x + y) % 4).testBit 1 = (x.testBit 1 ^^ y.testBit 1 ^^ (x.testBit 0 && y.testBit 0)) := by
  decide

theorem neg_bits : ∀ x < 4, (3 * x % 4).testBit 0 = x.testBit 0 ∧
    (3 * x % 4).testBit 1 = (x.testBit 1 ^^ x.testBit 0) := by
  decide

theorem testBit_lt64 {x : ℕ} (hx : x < 64) {p : ℕ} (hp : 6 ≤ p) : x.testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (by
    have : 2 ^ 6 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    simpa using this))

theorem land63_lt (x : ℕ) : Nat.land x 63 < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem add_shl6 {a b : ℕ} (ha : a < 64) (p : ℕ) :
    (Nat.add a (Nat.shiftLeft b 6)).testBit p = if p < 6 then a.testBit p else b.testBit (p - 6) := by
  have e : Nat.add a (Nat.shiftLeft b 6) = 2 ^ 6 * b + a := by
    change a + b <<< 6 = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [e, Nat.testBit_two_pow_mul_add _ (by simpa using ha)]

theorem addB_eq {v w : Array ℕ} (hv : VOK v) (hw : VOK w) :
    addB (encV v) (encV w) = encV (addV4 v w) := by
  apply Nat.eq_of_testBit_eq
  intro p
  unfold addB
  beta_reduce
  have hxl : Nat.xor (Nat.land (encV v) 63) (Nat.land (encV w) 63) < 64 :=
    Nat.xor_lt_two_pow (n := 6) (land63_lt _) (land63_lt _)
  rw [add_shl6 hxl, testBit_encV]
  have hd : ∀ k < 6, (addV4 v w).getD k 0 = (v.getD k 0 + w.getD k 0) % 4 := fun k hk => by
    unfold addV4
    rw [getD_ofFn6 _ _ hk]
  by_cases hp6 : p < 6
  · rw [if_pos hp6, if_pos hp6, decide_eq_true (by omega : p < 12), Bool.true_and, testBit_nxor,
      testBit_land63, testBit_land63, decide_eq_true hp6, Bool.true_and, Bool.true_and,
      testBit_encV, testBit_encV, hd p hp6, (add_bits _ (hv p hp6) _ (hw p hp6)).1]
    simp [hp6, show p < 12 by omega]
  · rw [if_neg hp6, if_neg hp6, testBit_nxor, testBit_nxor, testBit_shr6, testBit_shr6, testBit_land,
      testBit_land63, testBit_land63, testBit_encV, testBit_encV, testBit_encV, testBit_encV]
    by_cases hp : p < 12
    · have hk : p - 6 < 6 := by omega
      rw [decide_eq_true hp, Bool.true_and, hd _ hk, (add_bits _ (hv _ hk) _ (hw _ hk)).2]
      simp [show 6 + (p - 6) < 12 by omega, show ¬ 6 + (p - 6) < 6 by omega, hk,
        show 6 + (p - 6) - 6 = p - 6 by omega, show p - 6 < 12 by omega]
    · rw [decide_eq_false hp, Bool.false_and]
      simp [show ¬ 6 + (p - 6) < 12 by omega, show ¬ p - 6 < 6 by omega]

theorem negB_eq {v : Array ℕ} (hv : VOK v) : negB (encV v) = encV (negV4 v) := by
  apply Nat.eq_of_testBit_eq
  intro p
  change (Nat.xor (encV v) (Nat.shiftLeft (Nat.land (encV v) 63) 6)).testBit p = _
  have hd : ∀ k < 6, (negV4 v).getD k 0 = 3 * v.getD k 0 % 4 := fun k hk => by
    unfold negV4
    rw [getD_ofFn6 _ _ hk]
  rw [testBit_nxor, show Nat.shiftLeft (Nat.land (encV v) 63) 6 = (Nat.land (encV v) 63) <<< 6 from rfl,
    Nat.testBit_shiftLeft, testBit_encV, testBit_encV]
  by_cases hp6 : p < 6
  · rw [if_pos hp6, if_pos hp6, hd p hp6, (neg_bits _ (hv p hp6)).1]
    simp [show ¬ 6 ≤ p by omega]
  · by_cases hp : p < 12
    · have hk : p - 6 < 6 := by omega
      rw [if_neg hp6, if_neg hp6, hd _ hk, (neg_bits _ (hv _ hk)).2, testBit_land63, testBit_encV]
      simp [hp, hk, show 6 ≤ p by omega, show p - 6 < 12 by omega]
    · rw [decide_eq_false hp]
      simp only [Bool.false_and, Bool.false_xor, decide_eq_true (by omega : 6 ≤ p), Bool.true_and,
        testBit_land63, decide_eq_false (by omega : ¬ p - 6 < 6)]

@[expose] def encT (g : Array ℕ × Bool × ℕ) : ℕ := encV g.1 + 4096 * g.2.1.toNat + 8192 * g.2.2

theorem encT_land (g : Array ℕ × Bool × ℕ) : Nat.land (encT g) 4095 = encV g.1 := by
  rw [show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num]
  change encT g &&& (2 ^ 12 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := encV_lt g.1
  unfold encT
  omega

theorem encT_shr (g : Array ℕ × Bool × ℕ) : Nat.shiftRight (encT g) 13 = g.2.2 := by
  change encT g >>> 13 = _
  rw [Nat.shiftRight_eq_div_pow]
  have := encV_lt g.1
  have : g.2.1.toNat < 2 := Bool.toNat_lt _
  unfold encT
  omega

theorem encT_bit (g : Array ℕ × Bool × ℕ) : bitN (encT g) 12 = g.2.1.toNat := by
  rw [bitN_eq, tb]
  have := encV_lt g.1
  have h2 : g.2.1.toNat < 2 := Bool.toNat_lt _
  have e : encT g / 2 ^ 12 % 2 = g.2.1.toNat := by
    unfold encT
    omega
  rw [e]
  cases g.2.1 <;> rfl

theorem encT_inj {g h : Array ℕ × Bool × ℕ} (hg : g.1.size = 6) (hh : h.1.size = 6) (hg4 : VOK g.1)
    (hh4 : VOK h.1) (e : encT g = encT h) : g = h := by
  have e1 := congrArg (fun x => Nat.land x 4095) e
  have e2 := congrArg (fun x => bitN x 12) e
  have e3 := congrArg (fun x => Nat.shiftRight x 13) e
  simp only [encT_land, encT_bit, encT_shr] at e1 e2 e3
  obtain ⟨v, t, s⟩ := g
  obtain ⟨v', t', s'⟩ := h
  have hv := encV_inj hg hh hg4 hh4 e1
  have ht : t = t' := by cases t <;> cases t' <;> simp_all
  simp_all

theorem tmul_ok (T : Array (Array ℕ)) (LT : Array (Array (Array ℕ))) (g h : Array ℕ × Bool × ℕ) :
    (tmul T LT g h).1.size = 6 ∧ VOK (tmul T LT g h).1 := by
  unfold tmul
  refine ⟨Array.size_ofFn, vok_ofFn fun k => Nat.mod_lt _ (by norm_num)⟩

theorem tmulK_eq {T : Array (Array ℕ)} {LT : Array (Array (Array ℕ))} {LP MT : ℕ}
    {g h : Array ℕ × Bool × ℕ} (hg : VOK g.1) (hh : VOK h.1)
    (hT : tabGet T g.2.2 h.2.2 = tget MT g.2.2 h.2.2)
    (hL : SlOK (LT.getD g.2.2 #[]) (fget LP g.2.2 72))
    (hL4 : ∀ i < 6, ∀ k < 6, m4Get (LT.getD g.2.2 #[]) i k < 4) :
    tmulK POPT LP MT (encT g) (encT h) = encT (tmul T LT g h) := by
  unfold tmulK
  beta_reduce
  rw [encT_land, encT_land, encT_bit, encT_bit, encT_shr, encT_shr, strictN_eq,
    mvB_eq hL hL4 hh]
  have hw : VOK (mv4 (LT.getD g.2.2 #[]) h.1) := by
    unfold mv4
    exact vok_ofFn fun k => Nat.mod_lt _ (by norm_num)
  have hn : VOK (negV4 (mv4 (LT.getD g.2.2 #[]) h.1)) := by
    unfold negV4
    exact vok_ofFn fun k => Nat.mod_lt _ (by norm_num)
  unfold tmul encT
  rw [← hT, xor_toNat, nIf_eq]
  simp only [Nat.add_eq, Nat.mul_eq]
  cases hgt : g.2.1
  · rw [show ((false).toNat).beq 1 = false from rfl, if_neg (by simp), addB_eq hg hw]
    simp only [Bool.false_eq_true, if_false]
    ring
  · rw [show ((true).toNat).beq 1 = true from rfl, if_pos rfl, negB_eq hw, addB_eq hg hn]
    simp only [if_true]
    ring

theorem encV_twoV {q : ℕ} (hq : q < 64) : encV (twoV q) = q <<< 6 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_encV, Nat.testBit_shiftLeft]
  have hd : ∀ k < 6, (twoV q).getD k 0 = if q.testBit k then 2 else 0 := fun k hk => by
    unfold twoV
    rw [getD_ofFn6 _ _ hk]
  by_cases hp6 : p < 6
  · rw [if_pos hp6, hd p hp6, decide_eq_true (by omega : p < 12), decide_eq_false (by omega : ¬ 6 ≤ p)]
    split <;> rfl
  · by_cases hp : p < 12
    · rw [if_neg hp6, hd _ (by omega), decide_eq_true hp, decide_eq_true (by omega : 6 ≤ p)]
      by_cases hb : q.testBit (p - 6) = true
      · rw [if_pos hb, hb]
        rfl
      · rw [if_neg hb, Bool.eq_false_iff.2 hb]
        rfl
    · rw [decide_eq_false hp, decide_eq_true (by omega : 6 ≤ p), testBit_lt64 hq (by omega)]
      rfl

theorem vok_twoV (q : ℕ) : VOK (twoV q) := by
  unfold twoV
  exact vok_ofFn fun k => by split <;> norm_num

theorem vok_dig4 (n : ℕ) : VOK (dig4 n) := by
  unfold dig4
  exact vok_ofFn fun k => Nat.mod_lt _ (by norm_num)

theorem qes_eq {c : ℕ} (hc : c < 8192) :
    qes c = encT (twoV (c % 64), (c / 64 % 2 == 1), c / 128) := by
  have hq : c % 64 < 64 := Nat.mod_lt _ (by norm_num)
  unfold qes encT
  dsimp only
  rw [encV_twoV hq]
  change (Nat.land c 63) <<< 6 + 4096 * (c >>> 6) = _
  rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num]
  change (c &&& (2 ^ 6 - 1)) <<< 6 + _ = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have : (c / 64 % 2 == 1).toNat = c / 64 % 2 := by
    rcases Nat.mod_two_eq_zero_or_one (c / 64) with h | h <;> simp [h]
  rw [this]
  omega

theorem one_eq : (nat_lit 1 : ℕ) = encT (dig4 1, false, 0) := by decide +kernel

theorem c1537_eq : (nat_lit 1537 : ℕ) = encT (dig4 641, false, 0) := by decide +kernel

theorem c64_eq : (nat_lit 64 : ℕ) = encT (twoV 1, false, 0) := by decide +kernel

theorem t0Gen_eq : ∀ k < 6, t0Gen k = encT (t0Gens.getD k (dig4 0, false, 0)) := by decide +kernel

theorem allRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => Bool.rec (motive := fun _ => Bool) false acc (f q)) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change Bool.rec (motive := fun _ => Bool) false _ (f n) = true ↔ _
    rw [show ∀ a b : Bool, Bool.rec (motive := fun _ => Bool) false b a = (a && b) from
      fun a b => by cases a <;> rfl, Bool.and_eq_true, allRec_iff f n]
    constructor
    · rintro ⟨h2, h1⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨h n (by omega), fun q hq => h q (by omega)⟩

theorem allBelow_spec' {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true := by
  intro i him
  have h1 := (allRec_iff _ hi).1 h (i / 64) (by omega)
  have h2 := (allRec_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
    (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr him
  beta_reduce at h2
  rw [e, hb] at h2
  exact h2

theorem shl_lt {a w k : ℕ} (ha : a < 2 ^ w) : Nat.shiftLeft a (Nat.mul w k) < 2 ^ (w * (k + 1)) := by
  change a <<< (w * k) < _
  rw [Nat.shiftLeft_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (a) _]
  exact Nat.mul_lt_mul_of_pos_left ha (Nat.two_pow_pos _)

theorem sliceK_lt (A : ℕ) : sliceK A < 2 ^ 72 := by
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  change (strictN A fun A => orN 6 fun i => Nat.shiftLeft
    (Nat.add (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 0) k)
      (Nat.shiftLeft (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 1) k) 6))
    (Nat.mul 12 i)).testBit p = false
  rw [strictN_eq, Bool.eq_false_iff]
  intro h
  obtain ⟨i, hi, h⟩ := (testBit_orN_iff _ p 6).1 h
  have hr : Nat.add (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 0) k)
      (Nat.shiftLeft (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 1) k) 6) < 2 ^ 12 := by
    have h1 := orN6_lt (f := fun k => bitN (ent4 A i k) 0) (fun k _ => bitN_lt2 _ _)
    have h2 := orN6_lt (f := fun k => bitN (ent4 A i k) 1) (fun k _ => bitN_lt2 _ _)
    change _ + _ <<< 6 < _
    rw [Nat.shiftLeft_eq]
    omega
  have := shl_lt (k := i) hr
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num)
    (by omega)))] at h
  exact absurd h (by decide)

@[expose] noncomputable def ltAux (G C : ℕ) (ws : List (List ℕ)) (i0 : ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun w _ ih i => Nat.lor (Nat.shiftLeft (sliceK (prod4K G C w)) (Nat.mul (nat_lit 72) i))
      (ih (Nat.succ i))) ws i0

theorem ltAux_low (G C : ℕ) : ∀ (ws : List (List ℕ)) (i0 p : ℕ), p < 72 * i0 →
    (ltAux G C ws i0).testBit p = false
  | [], _, _, _ => Nat.zero_testBit _
  | w :: ws, i0, p, hp => by
    change ((sliceK (prod4K G C w)) <<< (72 * i0) ||| ltAux G C ws (i0 + 1)).testBit p = false
    rw [Nat.testBit_or, ltAux_low G C ws (i0 + 1) p (by omega), Bool.or_false, Nat.testBit_shiftLeft]
    simp [show ¬ 72 * i0 ≤ p by omega]

theorem fget_ltAux (G C : ℕ) : ∀ (ws : List (List ℕ)) (i0 j : ℕ) (hj : j < ws.length),
    fget (ltAux G C ws i0) (i0 + j) 72 = sliceK (prod4K G C (ws[j]'hj))
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | w :: ws, i0, j, hj => by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [testBit_fget]
    by_cases hp : p < 72
    · rw [decide_eq_true hp, Bool.true_and]
      change ((sliceK (prod4K G C w)) <<< (72 * i0) ||| ltAux G C ws (i0 + 1)).testBit
        ((i0 + j) * 72 + p) = _
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      rcases j with _ | j
      · rw [ltAux_low G C ws (i0 + 1) _ (by omega), Bool.or_false,
          decide_eq_true (by omega : 72 * i0 ≤ (i0 + 0) * 72 + p), Bool.true_and,
          show (i0 + 0) * 72 + p - 72 * i0 = p by omega]
        rfl
      · have ih := fget_ltAux G C ws (i0 + 1) j (by simpa using hj)
        have h3 := congrArg (fun x => Nat.testBit x p) ih
        simp only [testBit_fget, decide_eq_true hp, Bool.true_and] at h3
        rw [show (i0 + (j + 1)) * 72 + p = (i0 + 1 + j) * 72 + p by ring, h3,
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (sliceK_lt _)
            (Nat.pow_le_pow_right (by norm_num) (by omega : 72 ≤ (i0 + 1 + j) * 72 + p - 72 * i0))),
          Bool.and_false, Bool.false_or]
        rfl
    · rw [decide_eq_false hp, Bool.false_and, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (sliceK_lt _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] noncomputable def wordsAux (G L : ℕ) (ws : List (List ℕ)) (i0 : ℕ) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 64))
    (fun w _ ih i => andB (lettersOK w) (andB (Nat.beq (wordRowsK G w) (mat L i)) (ih (Nat.succ i))))
    ws i0

theorem wordsAux_spec (G L : ℕ) : ∀ (ws : List (List ℕ)) (i0 : ℕ), wordsAux G L ws i0 = true →
    i0 + ws.length = 64 ∧ ∀ t (ht : t < ws.length), lettersOK (ws[t]'ht) = true ∧
      wordRowsK G (ws[t]'ht) = mat L (i0 + t)
  | [], i0, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun t ht => absurd ht (by simp)⟩
  | w :: ws, i0, h => by
    change andB (lettersOK w) (andB (Nat.beq (wordRowsK G w) (mat L i0)) (wordsAux G L ws (i0 + 1))) =
      true at h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := wordsAux_spec G L ws (i0 + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun t ht => ?_⟩
    rcases t with _ | t
    · exact ⟨h1, by simpa using Nat.eq_of_beq_eq_true h2⟩
    · obtain ⟨a, b⟩ := ih2 t (by simpa using ht)
      exact ⟨a, by rw [List.getElem_cons_succ, b]; congr 1; omega⟩

theorem letters_of {w : List ℕ} (h : lettersOK w = true) : ∀ s ∈ w, s < 6 := by
  induction w with
  | nil => simp
  | cons s w ih =>
    change andB (Nat.blt s 6) (lettersOK w) = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h.1
    · exact ih h.2 t ht

@[expose] def OKT (g : Array ℕ × Bool × ℕ) : Prop := g.1.size = 6 ∧ VOK g.1 ∧ g.2.2 < 64

theorem tmul_snd (T : Array (Array ℕ)) (LT : Array (Array (Array ℕ))) (g h : Array ℕ × Bool × ℕ) :
    (tmul T LT g h).2.2 = tabGet T g.2.2 h.2.2 := rfl

@[expose] def ModelBind (T : Array (Array ℕ)) (LT : Array (Array (Array ℕ))) (LP MT : ℕ) : Prop :=
  (∀ i < 64, ∀ j < 64, tabGet T i j = tget MT i j) ∧
    ∀ s < 64, SlOK (LT.getD s #[]) (fget LP s 72) ∧ ∀ i < 6, ∀ k < 6, m4Get (LT.getD s #[]) i k < 4

theorem tmulK_ok {T : Array (Array ℕ)} {LT : Array (Array (Array ℕ))} {LP MT : ℕ}
    (hB : ModelBind T LT LP MT) {g h : Array ℕ × Bool × ℕ} (hg : OKT g) (hh : OKT h) :
    tmulK POPT LP MT (encT g) (encT h) = encT (tmul T LT g h) ∧ OKT (tmul T LT g h) := by
  refine ⟨tmulK_eq hg.2.1 hh.2.1 (hB.1 _ hg.2.2 _ hh.2.2) (hB.2 _ hg.2.2).1 (hB.2 _ hg.2.2).2, ?_⟩
  refine ⟨(tmul_ok T LT g h).1, (tmul_ok T LT g h).2, ?_⟩
  rw [tmul_snd, hB.1 _ hg.2.2 _ hh.2.2]
  exact tget_lt _ _ _

theorem beq_encT {g h : Array ℕ × Bool × ℕ} (hg : OKT g) (hh : OKT h) :
    Nat.beq (encT g) (encT h) = (g == h) := by
  by_cases e : g = h
  · subst e
    rw [Nat.beq_refl, beq_self_eq_true]
  · rw [beq_eq_false_iff_ne.2 e]
    cases hb : Nat.beq (encT g) (encT h)
    · rfl
    · exact absurd (encT_inj hg.1 hh.1 hg.2.1 hh.2.1 (Nat.eq_of_beq_eq_true hb)) e

theorem okt_const : OKT (dig4 1, false, 0) ∧ OKT (dig4 641, false, 0) ∧ OKT (twoV 1, false, 0) ∧
    ∀ k < 6, OKT (t0Gens.getD k (dig4 0, false, 0)) := by
  refine ⟨⟨rfl, vok_dig4 1, by norm_num⟩, ⟨rfl, vok_dig4 641, by norm_num⟩,
    ⟨rfl, vok_twoV 1, by norm_num⟩, ?_⟩
  intro k hk
  interval_cases k
  · change OKT (twoV 1, false, 0)
    exact ⟨rfl, vok_twoV _, by norm_num⟩
  · change OKT (twoV 2, false, 0)
    exact ⟨rfl, vok_twoV _, by norm_num⟩
  · change OKT (twoV 4, false, 0)
    exact ⟨rfl, vok_twoV _, by norm_num⟩
  · change OKT (dig4 0, false, 4)
    exact ⟨rfl, vok_dig4 _, by norm_num⟩
  · change OKT (dig4 0, false, 5)
    exact ⟨rfl, vok_dig4 _, by norm_num⟩
  · change OKT (dig4 0, false, 6)
    exact ⟨rfl, vok_dig4 _, by norm_num⟩

theorem modelBind_of {S : Array (Array ℕ)} {G C : ℕ → Array ℕ} {W : Array (List ℕ)}
    {GP CP L MT : Nat} {ws : List (List ℕ)} (hL : S0Bind S L)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hw : W.toList = ws) (hl : wordsOK GP L ws = true)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) :
    ModelBind (mulTabG S) (liftTabG G C W) (ltK GP CP ws) MT := by
  obtain ⟨hlen, hws⟩ := wordsAux_spec GP L ws 0 hl
  refine ⟨fun i hi j hj => table_eq hL hd hm hi hj, fun s hs => ?_⟩
  have hs' : s < ws.length := by omega
  have hW : W.getD s [] = ws[s]'hs' := by
    subst hw
    have hsz : s < W.size := by simpa using hs'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
    simp
  have e1 : (liftTabG G C W).getD s #[] = dec4M (prod4K GP CP (ws[s]'hs')) := by
    unfold liftTabG
    rw [getD_ofFn64 _ _ hs, hW, prod4K_eq hG hC _ (letters_of (hws s hs').1)]
  have e2 : fget (ltK GP CP ws) s 72 = sliceK (prod4K GP CP (ws[s]'hs')) := by
    have := fget_ltAux GP CP ws 0 s hs'
    rw [Nat.zero_add] at this
    exact this
  rw [e1, e2]
  exact ⟨slOK_slice _, fun i hi k hk => by rw [m4Get_dec4M _ hi hk]; exact ent4_lt _ _ _⟩

end CFSG.KC.O8.T0Pf

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf
  CFSG.KC.O8.S0Pf CFSG.KC.O8.Z4Pf CFSG.KC.O8.T0Pf CFSG.EvenSmallLie.UnitarySix.YamadaPar
  CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem words_sound_proved {G : ℕ → Array ℕ} {S : Array (Array ℕ)} {W : Array (List ℕ)} {GP L : Nat}
    {ws : List (List ℕ)} (hL : S0Bind S L) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hw : W.toList = ws) (h : wordsOK GP L ws = true) : wordsCheckG G S W = true := by
  obtain ⟨hlen, hws⟩ := wordsAux_spec GP L ws 0 h
  unfold wordsCheckG
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have hs' : i < ws.length := by omega
  have hW : W.getD i [] = ws[i]'hs' := by
    subst hw
    have hsz : i < W.size := by simpa using hs'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
    simp
  rw [hW, ← wordRowsK_eq hG _ (letters_of (hws i hs').1), (hws i hs').2, Nat.zero_add,
    s0Get_lt hL hi', beq_self_eq_true]

theorem uIdx_sound_proved {S : Array (Array ℕ)} {U : ℕ → Array ℕ} {L UP : Nat} (hL : S0Bind S L)
    (hU : ∀ k < 6, U k = decR (mat UP k))
    (h : andB (Nat.beq (mat L 4) (mat UP 3)) (andB (Nat.beq (mat L 5) (mat UP 4))
      (Nat.beq (mat L 6) (mat UP 5))) = true) : uIdxCheckG S U = true := by
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h4, h5, h6⟩ := h
  unfold uIdxCheckG
  rw [s0Get_lt hL (by norm_num), s0Get_lt hL (by norm_num), s0Get_lt hL (by norm_num),
    hU 3 (by norm_num), hU 4 (by norm_num), hU 5 (by norm_num), Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6]
  simp

theorem e0_sound_proved {S : Array (Array ℕ)} {L : Nat} (hL : S0Bind S L) (h : e0OK L = true) :
    e0CheckG S = true := by
  unfold e0CheckG
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have h1 := allN_iff.1 h i hi'
  rw [s0Get_lt hL hi', ← bvecK_eq, Nat.eq_of_beq_eq_true h1, beq_self_eq_true]

theorem t0_sound_proved {S : Array (Array ℕ)} {G C : ℕ → Array ℕ} {W : Array (List ℕ)}
    {GP CP L MT YW : Nat} {ws : List (List ℕ)} (hL : S0Bind S L)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hw : W.toList = ws) (hl : wordsOK GP L ws = true)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (h : t0OK (ltK GP CP ws) MT YW = true) :
    t0CheckG S (liftTabG G C W) = true := by
  have hB := modelBind_of hL hG hC hw hl hd hm
  unfold t0OK at h
  rw [strictN_eq, strictN_eq] at h
  have hall := allBelow_spec' (nIf_one h) (by norm_num)
  obtain ⟨h1, -, -, hgen⟩ := okt_const
  simp only [t0CheckG, List.all_eq_true, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false,
    List.any_eq_true]
  intro q hq e he s hs
  have hc : q + 64 * (e.toNat + 2 * s) < 8192 := by
    have := Bool.toNat_lt e
    omega
  have hf := hall _ hc
  rw [strictN_eq] at hf
  have hq' : (q + 64 * (e.toNat + 2 * s)) % 64 = q := by omega
  have he' : ((q + 64 * (e.toNat + 2 * s)) / 64 % 2 == 1) = e := by
    have := Bool.toNat_lt e
    cases e <;> simp <;> omega
  have hs' : (q + 64 * (e.toNat + 2 * s)) / 128 = s := by
    have := Bool.toNat_lt e
    omega
  rw [qes_eq hc, hq', he', hs'] at hf
  have hx := tmulK_ok hB h1 (⟨rfl, vok_twoV q, hs⟩ : OKT (twoV q, e, s))
  have hx1 : tmulK POPT (ltK GP CP ws) MT (nat_lit 1) (encT (twoV q, e, s)) =
      encT (tmul (mulTabG S) (liftTabG G C W) (dig4 1, false, 0) (twoV q, e, s)) :=
    (congrArg (fun z => tmulK POPT (ltK GP CP ws) MT z (encT (twoV q, e, s))) one_eq).trans hx.1
  rw [hx1] at hf
  have ht := nIf_one hf
  unfold t0At at ht
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true'] at ht
  obtain ⟨hk, hne⟩ := ht
  set k := fget YW (q + 64 * (e.toNat + 2 * s)) 3
  set y := t0Gens.getD k (dig4 0, false, 0)
  rw [t0Gen_eq k hk, (tmulK_ok hB hx.2 (hgen k hk)).1, (tmulK_ok hB (hgen k hk) hx.2).1,
    beq_encT (tmulK_ok hB hx.2 (hgen k hk)).2 (tmulK_ok hB (hgen k hk) hx.2).2] at hne
  refine ⟨y, ?_, by rw [hne]; rfl⟩
  have hy : y = t0Gens[k]'(by simpa [t0Gens] using hk) := by
    simp [y, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [t0Gens] using hk : k < t0Gens.length)]
  rw [hy]
  exact List.getElem_mem _

theorem comm_sound_proved {S : Array (Array ℕ)} {G C : ℕ → Array ℕ} {W : Array (List ℕ)}
    {GP CP L MT : Nat} {ws : List (List ℕ)} (hL : S0Bind S L)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hw : W.toList = ws) (hl : wordsOK GP L ws = true)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (h : commOK (ltK GP CP ws) MT = true) :
    commCheckG S (liftTabG G C W) = true := by
  have hB := modelBind_of hL hG hC hw hl hd hm
  unfold commOK at h
  rw [strictN_eq, strictN_eq] at h
  have hall := allBelow_spec' (nIf_one h) (by norm_num)
  obtain ⟨-, h641, h64, -⟩ := okt_const
  simp only [commCheckG, List.all_eq_true, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false,
    Bool.or_eq_true]
  intro q hq e he s hs
  have hc : q + 64 * (e.toNat + 2 * s) < 8192 := by
    have := Bool.toNat_lt e
    omega
  have hf := hall _ hc
  have hq' : (q + 64 * (e.toNat + 2 * s)) % 64 = q := by omega
  have he' : ((q + 64 * (e.toNat + 2 * s)) / 64 % 2 == 1) = e := by
    have := Bool.toNat_lt e
    cases e <;> simp <;> omega
  have hs' : (q + 64 * (e.toNat + 2 * s)) / 128 = s := by
    have := Bool.toNat_lt e
    omega
  have hg : OKT (twoV q, e, s) := ⟨rfl, vok_twoV q, hs⟩
  unfold commAt at hf
  rw [qes_eq hc, hq', he', hs', c1537_eq, c64_eq] at hf
  have hl' := tmulK_ok hB h641 hg
  have hr' := tmulK_ok hB hg h641
  have hrr := tmulK_ok hB hr'.2 h64
  rw [strictN_eq] at hf
  beta_reduce at hf
  rw [hl'.1, strictN_eq] at hf
  beta_reduce at hf
  rw [hr'.1, hrr.1, nIf_eq] at hf
  rw [orB_eq, beq_encT hl'.2 hr'.2, beq_encT hl'.2 hrr.2] at hf
  by_cases hb : ((tmul (mulTabG S) (liftTabG G C W) (dig4 641, false, 0) (twoV q, e, s) ==
      tmul (mulTabG S) (liftTabG G C W) (twoV q, e, s) (dig4 641, false, 0)) ||
    (tmul (mulTabG S) (liftTabG G C W) (dig4 641, false, 0) (twoV q, e, s) ==
      tmul (mulTabG S) (liftTabG G C W) (tmul (mulTabG S) (liftTabG G C W) (twoV q, e, s)
        (dig4 641, false, 0)) (twoV 1, false, 0))) = true
  · rw [Bool.or_eq_true] at hb
    exact hb
  · rw [if_neg hb] at hf
    exact absurd hf (by decide)

end CFSG.KC.O8

end
