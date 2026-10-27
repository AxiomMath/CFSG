module

public import Certificates.Data.Kernel.ONanF2.Defs
public import CFSG.Certificates.Kernel.ONanF2KSound

public section

namespace CFSG.KS.ONanF2

open CFSG.KC.ONanF2 CFSG.KC.ONanF2K
open CFSG.OddStandard.ONanRec.F2 hiding enc

theorem enc_lt (x : AlpE) : enc x < 512 := by
  have h1 := x.d.isLt
  have h2 := ZMod.val_lt x.v0
  have h3 := ZMod.val_lt x.v1
  have h4 := ZMod.val_lt x.v2
  simp only [enc, Nat.add_eq, Nat.mul_eq]
  omega

theorem enc_eq_cdN (x : AlpE) : enc x = cdN x := by
  simp only [enc, cdN, Nat.add_eq, Nat.mul_eq]
  ring

theorem dec_enc (x : AlpE) : dec (enc x) = x := by
  rw [enc_eq_cdN]
  exact decN_cdN x

theorem dec_eq_iff {a b : ℕ} (ha : a < 512) (hb : b < 512) : dec a = dec b ↔ a = b := by
  rw [dec, dec, decN_eq_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem enc_dec {c : ℕ} (hc : c < 512) : enc (dec c) = c :=
  (dec_eq_iff (enc_lt _) hc).1 (dec_enc _)

theorem enc_inj {x y : AlpE} : enc x = enc y ↔ x = y :=
  ⟨fun h => by rw [← dec_enc x, h, dec_enc], fun h => h ▸ rfl⟩

theorem mulK_lt (a b : ℕ) : mulK a b < 512 := by
  have h : lane dmulT (a / 64 % 8 * 8 + b / 64 % 8) 3 < 8 := Nat.mod_lt _ (by decide)
  rw [mulK_eq]
  omega

theorem dec_mulK (a b : ℕ) : dec (mulK a b) = dec a * dec b := (decN_mul a b).symm

theorem enc_mul (x y : AlpE) : enc (x * y) = mulK (enc x) (enc y) := by
  rw [← enc_dec (mulK_lt (enc x) (enc y)), dec_mulK, dec_enc, dec_enc]

theorem beq_iff {a b : ℕ} (ha : a < 512) (hb : b < 512) : Nat.beq a b = true ↔ dec a = dec b := by
  rw [Nat.beq_eq, dec_eq_iff ha hb]

theorem cmK_iff {a b : ℕ} (ha : a < 512) (hb : b < 512) :
    cmK a b = true ↔ dec a * dec b = dec b * dec a := by
  rw [cmK, beq_iff (mulK_lt _ _) (mulK_lt _ _), dec_mulK, dec_mulK]

theorem dec_zero : dec 0 = 1 := decN_zero

theorem enc_one : enc 1 = 0 := rfl

theorem dC_enc (x : AlpE) : dC (enc x) = x.d.val := by
  have h2 := ZMod.val_lt x.v0
  have h3 := ZMod.val_lt x.v1
  have h4 := ZMod.val_lt x.v2
  have e : dC (enc x) = enc x / 64 := Nat.shiftRight_eq_div_pow (enc x) 6
  rw [e]
  simp only [enc, Nat.add_eq, Nat.mul_eq]
  omega

theorem bitB_eq (m c : ℕ) : bitB m c = m.testBit c := by
  have key : ∀ i, (Nat.land m (Nat.shiftLeft 1 c)).testBit i = (m.testBit c && decide (c = i)) := by
    intro i
    change (m &&& 1 <<< c).testBit i = _
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : c = i
    · subst h
      simp
    · simp [h]
  unfold bitB
  cases h : m.testBit c
  · have h0 : Nat.land m (Nat.shiftLeft 1 c) = 0 :=
      Nat.eq_of_testBit_eq fun i => by rw [key, h, Nat.zero_testBit, Bool.false_and]
    rw [h0]
    rfl
  · have h0 : Nat.land m (Nat.shiftLeft 1 c) ≠ 0 := fun h0 => by
      have := key c
      rw [h0, h, Nat.zero_testBit] at this
      simp at this
    have : 0 < Nat.land m (Nat.shiftLeft 1 c) := Nat.pos_of_ne_zero h0
    simpa [Nat.blt_eq] using this

theorem testBit_setB (m c y : ℕ) : (setB m c).testBit y = (m.testBit y || decide (c = y)) := by
  change (m ||| 1 <<< c).testBit y = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_diffM (a b y : ℕ) : (diffM a b).testBit y = (a.testBit y && !b.testBit y) := by
  change (a ^^^ (a &&& b)).testBit y = _
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit y <;> cases b.testBit y <;> rfl

theorem testBit_lor (a b y : ℕ) : (Nat.lor a b).testBit y = (a.testBit y || b.testBit y) :=
  Nat.testBit_or a b y

theorem testBit_land (a b y : ℕ) : (Nat.land a b).testBit y = (a.testBit y && b.testBit y) :=
  Nat.testBit_and a b y

theorem iffB_iff (a b : Bool) : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

theorem allB_iff (q : ℕ → Bool) (k : ℕ) : allB q k = true ↔ ∀ c < k, q c = true := by
  induction k with
  | zero => exact ⟨fun _ c hc => absurd hc (Nat.not_lt_zero c), fun _ => rfl⟩
  | succ k ih =>
    have e : allB q (k + 1) = Bool.rec false (allB q k) (q k) := rfl
    rw [e]
    cases h : q k with
    | false =>
      refine ⟨fun h' => absurd h' Bool.false_ne_true, fun H => ?_⟩
      have := H k (Nat.lt_succ_self k)
      rw [h] at this
      exact absurd this Bool.false_ne_true
    | true =>
      change allB q k = true ↔ _
      rw [ih]
      constructor
      · intro H c hc
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · exact H c hc
        · exact h
      · intro H c hc
        exact H c (Nat.lt_succ_of_lt hc)

theorem forall_of_allB {q : ℕ → Bool} (h : allB q 512 = true) (x : AlpE) : q (enc x) = true :=
  (allB_iff q 512).1 h (enc x) (enc_lt x)

theorem allL_iff (l : List ℕ) (q : ℕ → Bool) : allL l q = true ↔ ∀ z ∈ l, q z = true := by
  induction l with
  | nil => simp [allL]
  | cons z l ih =>
    have e : allL (z :: l) q = Bool.rec false (allL l q) (q z) := rfl
    rw [e]
    cases h : q z
    · simp only [List.mem_cons, forall_eq_or_imp, h]
      exact ⟨fun h' => absurd h' Bool.false_ne_true, fun h' => absurd h'.1 Bool.false_ne_true⟩
    · change allL l q = true ↔ _
      simp [ih, h]

theorem testBit_maskOf (q : ℕ → Bool) (k y : ℕ) :
    (maskOf q k).testBit y = (decide (y < k) && q y) := by
  induction k with
  | zero => simp [maskOf]
  | succ k ih =>
    have e : maskOf q (k + 1) = Bool.rec (maskOf q k) (setB (maskOf q k) k) (q k) := rfl
    rw [e]
    by_cases hy : y = k
    · subst hy
      cases h : q y
      · change (maskOf q y).testBit y = _
        rw [ih]
        simp
      · change (setB (maskOf q y) y).testBit y = _
        simp [testBit_setB]
    · have hlt : decide (y < k + 1) = decide (y < k) := by
        rw [decide_eq_decide]
        omega
      cases h : q k
      · change (maskOf q k).testBit y = _
        rw [ih, hlt]
      · change (setB (maskOf q k) k).testBit y = _
        rw [testBit_setB, ih, hlt]
        simp [Ne.symm hy]

theorem testBit_maskOf_enc (q : ℕ → Bool) (x : AlpE) : (maskOf q 512).testBit (enc x) = q (enc x) := by
  rw [testBit_maskOf]
  simp [enc_lt]

theorem cntM_eq (M k : ℕ) :
    cntM M k = ((Finset.range k).filter fun c => M.testBit c = true).card := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : cntM M (k + 1) = Bool.rec (cntM M k) (Nat.succ (cntM M k)) (bitB M k) := rfl
    rw [e, Finset.range_add_one, Finset.filter_insert, bitB_eq]
    cases h : M.testBit k
    · simp only [Bool.false_eq_true, if_false]
      exact ih
    · simp only [if_true]
      rw [Finset.card_insert_of_notMem (by simp), ← ih]

theorem cntQ_eq (q : ℕ → Bool) (k : ℕ) :
    cntQ q k = ((Finset.range k).filter fun c => q c = true).card := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : cntQ q (k + 1) = Bool.rec (cntQ q k) (Nat.succ (cntQ q k)) (q k) := rfl
    rw [e, Finset.range_add_one, Finset.filter_insert]
    cases h : q k
    · simp only [Bool.false_eq_true, if_false]
      exact ih
    · simp only [if_true]
      rw [Finset.card_insert_of_notMem (by simp), ← ih]

theorem card_filter_cntQ (p : AlpE → Prop) [DecidablePred p] (q : ℕ → Bool)
    (hq : ∀ x, q (enc x) = true ↔ p x) : (Finset.univ.filter p).card = cntQ q 512 := by
  rw [cntQ_eq]
  refine Finset.card_bij' (fun x _ => enc x) (fun c _ => dec c) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨enc_lt x, (hq x).2 hx⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hc ⊢
    rw [← hq, enc_dec hc.1]
    exact hc.2
  · intro x _
    exact dec_enc x
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    exact enc_dec hc.1

theorem testBit_lorL (l : List ℕ) (acc y : ℕ) :
    (lorL l acc).testBit y = true ↔ acc.testBit y = true ∨ y ∈ l := by
  induction l with
  | nil => simp [lorL]
  | cons z l ih =>
    have e : lorL (z :: l) acc = setB (lorL l acc) z := rfl
    rw [e, testBit_setB, Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      exacts [Or.inl h, Or.inr (Or.inr h), Or.inr (Or.inl h.symm)]
    · rintro (h | h | h)
      exacts [Or.inl (Or.inl h), Or.inr h.symm, Or.inl (Or.inr h)]

theorem testBit_imgM (nxt : ℕ → List ℕ) (F k y : ℕ) :
    (imgM nxt F k).testBit y = true ↔ ∃ c < k, F.testBit c = true ∧ y ∈ nxt c := by
  induction k with
  | zero => simp [imgM]
  | succ k ih =>
    have e : imgM nxt F (k + 1) =
        Bool.rec (imgM nxt F k) (lorL (nxt k) (imgM nxt F k)) (bitB F k) := rfl
    rw [e, bitB_eq]
    cases h : F.testBit k
    · change (imgM nxt F k).testBit y = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨c, hc, h1, h2⟩
        exact ⟨c, Nat.lt_succ_of_lt hc, h1, h2⟩
      · rintro ⟨c, hc, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · exact ⟨c, hc, h1, h2⟩
        · rw [h] at h1
          exact absurd h1 Bool.false_ne_true
    · change (lorL (nxt k) (imgM nxt F k)).testBit y = true ↔ _
      rw [testBit_lorL, ih]
      constructor
      · rintro (⟨c, hc, h1, h2⟩ | h2)
        · exact ⟨c, Nat.lt_succ_of_lt hc, h1, h2⟩
        · exact ⟨k, Nat.lt_succ_self k, h, h2⟩
      · rintro ⟨c, hc, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · exact Or.inl ⟨c, hc, h1, h2⟩
        · exact Or.inr h2

theorem testBit_lorP (L : List (ℕ × ℕ)) (y : ℕ) :
    (lorP L).testBit y = true ↔ ∃ p ∈ L, p.2.testBit y = true := by
  induction L with
  | nil => simp [lorP]
  | cons p L ih =>
    have e : lorP (p :: L) = Nat.lor p.2 (lorP L) := rfl
    rw [e, testBit_lor, Bool.or_eq_true, ih]
    simp

abbrev Rep (M : ℕ) (L : List AlpE) : Prop :=
  (∀ x, x ∈ L ↔ M.testBit (enc x) = true) ∧ ∀ c, M.testBit c = true → c < 512

theorem Rep.mem_iff {M : ℕ} {A B : List AlpE} (hA : Rep M A) (hB : Rep M B) (x : AlpE) :
    x ∈ A ↔ x ∈ B := by rw [hA.1, hB.1]

theorem rep_lorL (l : List ℕ) (hl : ∀ c ∈ l, c < 512) : Rep (lorL l 0) (l.map dec) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [testBit_lorL, Nat.zero_testBit, List.mem_map]
    simp only [Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rwa [enc_dec (hl c hc)]
    · intro h
      exact ⟨enc x, h, dec_enc x⟩
  · rw [testBit_lorL, Nat.zero_testBit] at hc
    exact hl c (hc.resolve_left Bool.false_ne_true)

theorem rep_maskOf {q : ℕ → Bool} {M : ℕ} {L : List AlpE} (h : maskOf q 512 = M)
    (hL : Rep M L) (x : AlpE) : x ∈ L ↔ q (enc x) = true := by
  rw [hL.1, ← h, testBit_maskOf_enc]

theorem exists_common {M N : ℕ} {A B : List AlpE} (hA : Rep M A) (hB : Rep N B) :
    (∃ u ∈ A, u ∈ B) ↔ Nat.blt 0 (Nat.land M N) = true := by
  rw [Nat.blt_eq]
  constructor
  · rintro ⟨u, hu, hu'⟩
    have hb : (Nat.land M N).testBit (enc u) = true := by
      rw [testBit_land, (hA.1 u).1 hu, (hB.1 u).1 hu']
      rfl
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.zero_testBit] at hb
    exact Bool.false_ne_true hb
  · intro h
    obtain ⟨c, hc⟩ : ∃ c, (Nat.land M N).testBit c = true := by
      by_contra hne
      simp only [not_exists] at hne
      have : Nat.land M N = 0 := Nat.eq_of_testBit_eq fun i => by
        rw [Nat.zero_testBit]
        simpa using hne i
      omega
    rw [testBit_land, Bool.and_eq_true] at hc
    have hlt := hA.2 c hc.1
    refine ⟨dec c, (hA.1 _).2 ?_, (hB.1 _).2 ?_⟩ <;> rw [enc_dec hlt]
    exacts [hc.1, hc.2]

theorem Rep.eq_zero_iff {M : ℕ} {L : List AlpE} (h : Rep M L) : M = 0 ↔ L = [] := by
  constructor
  · rintro rfl
    refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
    have := (h.1 x).1 hx
    rw [Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  · rintro rfl
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.zero_testBit]
    cases hi : M.testBit i
    · rfl
    · have hlt := h.2 i hi
      have := (h.1 (dec i)).2 (by rwa [enc_dec hlt])
      exact absurd this List.not_mem_nil

theorem card_eq_cntM (S : Finset AlpE) (M : ℕ) (hS : ∀ x, x ∈ S ↔ M.testBit (enc x) = true)
    (hM : ∀ c, M.testBit c = true → c < 512) : S.card = cntM M 512 := by
  rw [cntM_eq]
  refine Finset.card_bij' (fun x _ => enc x) (fun c _ => dec c) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨enc_lt x, (hS x).1 hx⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    rw [hS, enc_dec hc.1]
    exact hc.2
  · intro x _
    exact dec_enc x
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    exact enc_dec hc.1

theorem Rep.length_eq {M : ℕ} {L : List AlpE} (h : Rep M L) (hL : L.Nodup) :
    L.length = cntM M 512 := by
  rw [← List.toFinset_card_of_nodup hL]
  exact card_eq_cntM _ _ (fun x => by rw [List.mem_toFinset]; exact h.1 x) h.2

theorem length_filter_eq {M P : ℕ} {L : List AlpE} (h : Rep M L) (hL : L.Nodup) (p : AlpE → Prop)
    [DecidablePred p] (hp : ∀ x, p x ↔ P.testBit (enc x) = true) :
    (L.filter fun x => decide (p x)).length = cntM (Nat.land M P) 512 := by
  refine Rep.length_eq ⟨fun x => ?_, fun c hc => ?_⟩ (hL.filter _)
  · rw [List.mem_filter, decide_eq_true_eq, testBit_land, Bool.and_eq_true, h.1, hp]
  · rw [testBit_land, Bool.and_eq_true] at hc
    exact h.2 c hc.1

theorem rep_single {r : ℕ} (hr : r < 512) : Rep (setB 0 r) [dec r] := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [testBit_setB, Nat.zero_testBit, Bool.false_or, List.mem_singleton, decide_eq_true_eq,
      ← enc_inj, enc_dec hr, eq_comm]
  · rw [testBit_setB, Nat.zero_testBit, Bool.false_or, decide_eq_true_eq] at hc
    exact hc ▸ hr

theorem rep_one : Rep 1 [(1 : AlpE)] := by
  have h := rep_single (r := 0) (by decide)
  rw [dec_zero] at h
  exact h

theorem rep_append {V N : ℕ} {vis new : List AlpE} (hV : Rep V vis) (hN : Rep N new) :
    Rep (Nat.lor V N) (vis ++ new) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [List.mem_append, testBit_lor, Bool.or_eq_true, hV.1, hN.1]
  · rw [testBit_lor, Bool.or_eq_true] at hc
    exact hc.elim (hV.2 c) (hN.2 c)

theorem beq0 {N : ℕ} (h0 : N ≠ 0) : Nat.beq N 0 = false := by
  cases hb : Nat.beq N 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h0

theorem rep_new (nxt : AlpE → List AlpE) (nxtK : ℕ → List ℕ)
    (hn : ∀ c < 512, ∀ y, y ∈ nxtK c ↔ ∃ z ∈ nxt (dec c), enc z = y)
    {vis fr : List AlpE} {V F : ℕ} (hV : Rep V vis) (hF : Rep F fr) :
    Rep (newM nxtK F V) ((fr.flatMap nxt).dedup.filter fun y => y ∉ vis) := by
  have himg : ∀ y, (imgM nxtK F 512).testBit y = true ↔ ∃ x ∈ fr, ∃ z ∈ nxt x, enc z = y := by
    intro y
    rw [testBit_imgM]
    constructor
    · rintro ⟨c, hc, hFc, hy⟩
      obtain ⟨z, hz, rfl⟩ := (hn c hc y).1 hy
      exact ⟨dec c, (hF.1 _).2 (by rwa [enc_dec hc]), z, hz, rfl⟩
    · rintro ⟨x, hx, z, hz, rfl⟩
      exact ⟨enc x, enc_lt x, (hF.1 x).1 hx, (hn _ (enc_lt x) _).2 ⟨z, by rwa [dec_enc], rfl⟩⟩
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · rw [newM, testBit_diffM, Bool.and_eq_true, himg, Bool.not_eq_true', List.mem_filter,
      List.mem_dedup, List.mem_flatMap, decide_eq_true_eq]
    have hv := hV.1 y
    constructor
    · rintro ⟨⟨x, hx, hy⟩, hnv⟩
      refine ⟨⟨x, hx, y, hy, rfl⟩, ?_⟩
      cases h : V.testBit (enc y)
      · rfl
      · exact absurd (hv.2 h) hnv
    · rintro ⟨⟨x, hx, z, hz, he⟩, hnv⟩
      rw [enc_inj] at he
      subst he
      refine ⟨⟨x, hx, hz⟩, fun hm => ?_⟩
      rw [hv.1 hm] at hnv
      exact Bool.noConfusion hnv
  · rw [newM, testBit_diffM, Bool.and_eq_true] at hc
    obtain ⟨x, -, z, -, rfl⟩ := (himg c).1 hc.1
    exact enc_lt z

theorem hn_rmul (gensK : List ℕ) :
    ∀ c < 512, ∀ y, y ∈ rmulK gensK c ↔ ∃ z ∈ (gensK.map dec).map (dec c * ·), enc z = y := by
  intro c hc y
  simp only [rmulK, List.map_map, List.mem_map, Function.comp]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, by rw [← dec_mulK, enc_dec (mulK_lt _ _)]⟩
  · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, by rw [← dec_mulK, enc_dec (mulK_lt _ _)]⟩

theorem hn_conj (ps : List (ℕ × ℕ)) (hinv : ∀ p ∈ ps, dec p.2 = (dec p.1)⁻¹) :
    ∀ c < 512, ∀ y, y ∈ conjK ps c ↔ ∃ z ∈ (ps.map fun p => dec p.1).flatMap
      (fun g => [g⁻¹ * dec c * g, g * dec c * g⁻¹]), enc z = y := by
  intro c hc y
  simp only [conjK, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨p, hp, hy⟩
    refine ⟨if y = mulK (mulK p.2 c) p.1 then (dec p.1)⁻¹ * dec c * dec p.1
      else dec p.1 * dec c * (dec p.1)⁻¹, ⟨dec p.1, ⟨p, hp, rfl⟩, ?_⟩, ?_⟩
    · split_ifs <;> simp
    · rcases hy with rfl | rfl
      · rw [if_pos rfl, ← hinv p hp, ← dec_mulK, ← dec_mulK, enc_dec (mulK_lt _ _)]
      · split_ifs with h
        · rw [← hinv p hp, ← dec_mulK, ← dec_mulK, enc_dec (mulK_lt _ _), h]
        · rw [← hinv p hp, ← dec_mulK, ← dec_mulK, enc_dec (mulK_lt _ _)]
  · rintro ⟨z, ⟨g, ⟨p, hp, rfl⟩, hz⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    rcases hz with rfl | rfl
    · left
      rw [← hinv p hp, ← dec_mulK, ← dec_mulK, enc_dec (mulK_lt _ _)]
    · right
      rw [← hinv p hp, ← dec_mulK, ← dec_mulK, enc_dec (mulK_lt _ _)]

theorem rep_bfs (gens : List AlpE) (nxtK : ℕ → List ℕ)
    (hn : ∀ c < 512, ∀ y, y ∈ nxtK c ↔ ∃ z ∈ gens.map (dec c * ·), enc z = y) :
    ∀ (n : ℕ) (vis fr : List AlpE) (V F : ℕ), Rep V vis → Rep F fr →
      Rep (bfsM nxtK n V F) (bfs gens n vis fr)
  | 0, vis, fr, V, F, hV, _ => by
    rw [bfs]
    exact hV
  | n + 1, vis, fr, V, F, hV, hF => by
    have hN : Rep (newM nxtK F V) ((fr.flatMap fun x => gens.map (x * ·)).dedup.filter
        fun y => y ∉ vis) := rep_new (fun x => gens.map (x * ·)) nxtK hn hV hF
    rw [bfs]
    have e : bfsM nxtK (n + 1) V F = bfsStep (bfsM nxtK n) V (newM nxtK F V) := rfl
    rw [e]
    generalize ((fr.flatMap fun x => gens.map (x * ·)).dedup.filter fun y => y ∉ vis) = new at hN ⊢
    generalize newM nxtK F V = N at hN ⊢
    by_cases h0 : N = 0
    · subst h0
      rw [(hN.eq_zero_iff).1 rfl]
      exact hV
    · have hb : Nat.beq N 0 = false := beq0 h0
      have hne : new ≠ [] := fun h => h0 ((hN.eq_zero_iff).2 h)
      have e2 : bfsStep (bfsM nxtK n) V N = bfsM nxtK n (Nat.lor V N) N := by
        simp only [bfsStep, hb]
      rw [e2, if_neg (by simpa using hne)]
      exact rep_bfs gens nxtK hn n _ _ _ _ (rep_append hV hN) hN

theorem rep_bfsC (gens : List AlpE) (nxtK : ℕ → List ℕ)
    (hn : ∀ c < 512, ∀ y, y ∈ nxtK c ↔
      ∃ z ∈ gens.flatMap (fun g => [g⁻¹ * dec c * g, g * dec c * g⁻¹]), enc z = y) :
    ∀ (n : ℕ) (vis fr : List AlpE) (V F : ℕ), Rep V vis → Rep F fr →
      Rep (bfsM nxtK n V F) (bfsC gens n vis fr)
  | 0, vis, fr, V, F, hV, _ => by
    rw [bfsC]
    exact hV
  | n + 1, vis, fr, V, F, hV, hF => by
    have hN : Rep (newM nxtK F V) ((fr.flatMap fun x =>
        gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]).dedup.filter fun y => y ∉ vis) :=
      rep_new (fun x => gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]) nxtK hn hV hF
    rw [bfsC]
    have e : bfsM nxtK (n + 1) V F = bfsStep (bfsM nxtK n) V (newM nxtK F V) := rfl
    rw [e]
    generalize ((fr.flatMap fun x => gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]).dedup.filter
      fun y => y ∉ vis) = new at hN ⊢
    generalize newM nxtK F V = N at hN ⊢
    by_cases h0 : N = 0
    · subst h0
      rw [(hN.eq_zero_iff).1 rfl]
      exact hV
    · have hb : Nat.beq N 0 = false := beq0 h0
      have hne : new ≠ [] := fun h => h0 ((hN.eq_zero_iff).2 h)
      have e2 : bfsStep (bfsM nxtK n) V N = bfsM nxtK n (Nat.lor V N) N := by
        simp only [bfsStep, hb]
      rw [e2, if_neg (by simpa using hne)]
      exact rep_bfsC gens nxtK hn n _ _ _ _ (rep_append hV hN) hN

theorem nodup_step {α : Type*} [DecidableEq α] (vis l : List α) (hv : vis.Nodup) :
    (vis ++ l.dedup.filter fun y => y ∉ vis).Nodup := by
  rw [List.nodup_append]
  refine ⟨hv, (List.nodup_dedup l).filter _, fun a ha b hb hab => ?_⟩
  subst hab
  rw [List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 ha

theorem nodup_bfs (gens : List AlpE) :
    ∀ (n : ℕ) (vis fr : List AlpE), vis.Nodup → (bfs gens n vis fr).Nodup
  | 0, vis, fr, hv => by
    rw [bfs]
    exact hv
  | n + 1, vis, fr, hv => by
    rw [bfs]
    split
    · exact hv
    · exact nodup_bfs gens n _ _ (nodup_step _ _ hv)

theorem nodup_bfsC (gens : List AlpE) :
    ∀ (n : ℕ) (vis fr : List AlpE), vis.Nodup → (bfsC gens n vis fr).Nodup
  | 0, vis, fr, hv => by
    rw [bfsC]
    exact hv
  | n + 1, vis, fr, hv => by
    rw [bfsC]
    split
    · exact hv
    · exact nodup_bfsC gens n _ _ (nodup_step _ _ hv)

theorem conj_bfsC (gens : List AlpE) (r : AlpE) :
    ∀ (n : ℕ) (vis fr : List AlpE), (∀ x ∈ vis, IsConj r x) → (∀ x ∈ fr, IsConj r x) →
      ∀ x ∈ bfsC gens n vis fr, IsConj r x
  | 0, vis, fr, hv, _ => by
    rw [bfsC]
    exact hv
  | n + 1, vis, fr, hv, hf => by
    rw [bfsC]
    have hnew : ∀ y ∈ ((fr.flatMap fun x =>
        gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]).dedup.filter fun y => y ∉ vis),
        IsConj r y := by
      intro y hy
      rw [List.mem_filter, List.mem_dedup, List.mem_flatMap] at hy
      obtain ⟨⟨x, hx, hy⟩, -⟩ := hy
      rw [List.mem_flatMap] at hy
      obtain ⟨g, -, hy⟩ := hy
      refine (hf x hx).trans (isConj_iff.2 ?_)
      rcases List.mem_pair.1 hy with rfl | rfl
      · exact ⟨g⁻¹, by rw [inv_inv]⟩
      · exact ⟨g, rfl⟩
    split
    · exact hv
    · refine conj_bfsC gens r n _ _ (fun x hx => ?_) hnew
      rcases List.mem_append.1 hx with hx | hx
      · exact hv x hx
      · exact hnew x hx

theorem subOK_of_subB (gensK : List ℕ) (gens : List AlpE) (hg : gens = gensK.map dec) (M n : ℕ)
    (h : subB gensK M n = true) : SubOK gens (ballFix gens) n ∧ Rep M (ballFix gens) := by
  subst hg
  simp only [subB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hn := hn_rmul gensK
  have hR : Rep M (ballFix (gensK.map dec)) :=
    h1 ▸ rep_bfs _ (rmulK gensK) hn 64 _ _ _ _ rep_one rep_one
  have hnd : (ballFix (gensK.map dec)).Nodup := nodup_bfs _ 64 _ _ (List.nodup_singleton 1)
  refine ⟨⟨rfl, (hR.length_eq hnd).trans h2, hnd, fun x hx g hg => ?_⟩, hR⟩
  have hE := (rep_new (fun x => (gensK.map dec).map (x * ·)) (rmulK gensK) hn hR hR).eq_zero_iff.1 h3
  by_contra hxg
  have hm : x * g ∈ (((ballFix (gensK.map dec)).flatMap fun x => (gensK.map dec).map (x * ·)).dedup.filter
      fun y => y ∉ ballFix (gensK.map dec)) := by
    rw [List.mem_filter, List.mem_dedup, List.mem_flatMap, decide_eq_true_eq]
    exact ⟨⟨x, hx, List.mem_map.2 ⟨g, hg, rfl⟩⟩, hxg⟩
  rw [hE] at hm
  exact List.not_mem_nil hm

theorem orbit_of_clsB (ps : List (ℕ × ℕ)) (hinv : ∀ p ∈ ps, dec p.2 = (dec p.1)⁻¹)
    (gens : List AlpE) (hg : gens = ps.map fun p => dec p.1) {r : ℕ} (hr : r < 512) (M : ℕ)
    (h1 : clsB ps r M = true) :
    Rep M (orbitC gens (dec r)) ∧ (orbitC gens (dec r)).Nodup ∧
      ∀ x ∈ orbitC gens (dec r), IsConj (dec r) x := by
  subst hg
  rw [clsB, Nat.beq_eq] at h1
  have hR : Rep M (orbitC (ps.map fun p => dec p.1) (dec r)) :=
    h1 ▸ rep_bfsC _ (conjK ps) (hn_conj ps hinv) 64 _ _ _ _ (rep_single hr) (rep_single hr)
  have hnd := nodup_bfsC (ps.map fun p => dec p.1) 64 _ [dec r] (List.nodup_singleton (dec r))
  have hc : ∀ x ∈ orbitC (ps.map fun p => dec p.1) (dec r), IsConj (dec r) x := by
    refine conj_bfsC _ (dec r) 64 _ _ ?_ ?_ <;>
    · intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ IsConj.refl _
  exact ⟨hR, hnd, hc⟩

theorem classOK_of_clsOKB (ps : List (ℕ × ℕ)) (hinv : ∀ p ∈ ps, dec p.2 = (dec p.1)⁻¹)
    (gens : List AlpE) (hg : gens = ps.map fun p => dec p.1) {r : ℕ} (hr : r < 512) (M n : ℕ)
    (h : clsOKB ps r M n = true) :
    ClassOK gens (dec r) (orbitC gens (dec r)) n ∧ Rep M (orbitC gens (dec r)) := by
  simp only [clsOKB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hR, hnd, -⟩ := orbit_of_clsB ps hinv gens hg hr M h1
  have hn := hn_conj ps hinv
  rw [← hg] at hn
  refine ⟨⟨rfl, (hR.length_eq hnd).trans h2, hnd, fun x hx g hg' => ?_⟩, hR⟩
  have hE := (rep_new (fun x => gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]) (conjK ps)
    hn hR hR).eq_zero_iff.1 h3
  have key : ∀ y ∈ gens.flatMap (fun g => [g⁻¹ * x * g, g * x * g⁻¹]),
      y ∈ orbitC gens (dec r) := by
    intro y hy
    by_contra hy'
    have hm : y ∈ (((orbitC gens (dec r)).flatMap fun x =>
        gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]).dedup.filter
        fun y => y ∉ orbitC gens (dec r)) := by
      rw [List.mem_filter, List.mem_dedup, List.mem_flatMap, decide_eq_true_eq]
      exact ⟨⟨x, hx, hy⟩, hy'⟩
    rw [hE] at hm
    exact List.not_mem_nil hm
  refine ⟨key _ ?_, key _ ?_⟩ <;>
  · rw [List.mem_flatMap]
    exact ⟨g, hg', by simp⟩

theorem nvB_sound (ps : List (ℕ × ℕ)) (L : List (ℕ × ℕ)) (h : nvB ps L = true) :
    ∀ p ∈ L, clsB ps p.1 p.2 = true ∧ 16 ≤ cntM p.2 512 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have e : nvB ps (p :: L) = Bool.rec false (Bool.rec false (nvB ps L)
        (Nat.ble 16 (cntM p.2 512))) (clsB ps p.1 p.2) := rfl
    rw [e] at h
    cases h1 : clsB ps p.1 p.2
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      cases h2 : Nat.ble 16 (cntM p.2 512)
      · rw [h2] at h
        exact absurd h Bool.false_ne_true
      · rw [h2] at h
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨h1, Nat.le_of_ble_eq_true h2⟩
        · exact ih h q hq

theorem card_cent_mul_le {G : Type*} [Group G] [Fintype G] [DecidableEq G] (x : G) (L : List G)
    (hL : L.Nodup) (hc : ∀ y ∈ L, IsConj x y) :
    (Finset.univ.filter fun g => g * x = x * g).card * L.length ≤ Fintype.card G := by
  choose! h hh using fun y (hy : y ∈ L) => isConj_iff.1 (hc y hy)
  have key : ∀ y g, y ∈ L → g * x = x * g → (h y * g) * x * (h y * g)⁻¹ = y := by
    intro y g hy hg
    calc (h y * g) * x * (h y * g)⁻¹ = h y * (g * x * g⁻¹) * (h y)⁻¹ := by group
      _ = h y * x * (h y)⁻¹ := by rw [hg, mul_inv_cancel_right]
      _ = y := hh y hy
  rw [← List.toFinset_card_of_nodup hL, mul_comm, ← Finset.card_product, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => h p.1 * p.2) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨y, g⟩ hp ⟨y', g'⟩ hp' he
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  simp only at he
  have hy : y = y' := by rw [← key y g hp.1 hp.2, he, key y' g' hp'.1 hp'.2]
  subst hy
  exact Prod.ext rfl (mul_left_cancel he)

theorem card_alpE : Fintype.card AlpE = 512 := by
  rw [Fintype.card_congr AlpE.equivProd]
  simp [Fintype.card_prod, ZMod.card]

end CFSG.KS.ONanF2
