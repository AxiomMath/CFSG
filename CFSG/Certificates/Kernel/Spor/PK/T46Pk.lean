module

public import CFSG.Certificates.Kernel.Spor.PK.MiscPerm
public import CFSG.Certificates.Kernel.Spor.PK.F4Code
public import CFSG.Certificates.Kernel.Spor.PK.Str
public import Certificates.Data.CFSGNative.Fi22.LocalData

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46 CFSG.F4.Native
  CFSG.Sporadic.Fi22.Native

namespace T46Pk

private theorem beq_false_of_ne' {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

private theorem beq_eq_false_iff' {a b : Nat} : Nat.beq a b = false ↔ a ≠ b :=
  ⟨Nat.ne_of_beq_eq_false, beq_false_of_ne'⟩

private theorem ne_of_not_beq {a b : Nat} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro e
  subst e
  simp at h

private def orFrom (a : Nat) : List Nat → Nat
  | [] => a
  | p :: t => orFrom a t ||| 2 ^ p

private def sumPow : List Nat → Nat
  | [] => 0
  | p :: t => sumPow t + 2 ^ p

private theorem recOr_eq (a : Nat) (O : List Nat) :
    (List.rec (motive := fun _ => Nat) a (fun p _ ih => Nat.lor ih (Nat.shiftLeft 1 p)) O) =
      orFrom a O := by
  induction O with
  | nil => rfl
  | cons p t ih =>
    refine (congrArg (fun x => Nat.lor x (Nat.shiftLeft 1 p)) ih).trans ?_
    show (orFrom a t ||| 1 <<< p) = orFrom a t ||| 2 ^ p
    rw [Nat.one_shiftLeft]

private theorem recSum_eq (O : List Nat) :
    (List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.add ih (Nat.shiftLeft 1 p)) O) =
      sumPow O := by
  induction O with
  | nil => rfl
  | cons p t ih =>
    refine (congrArg (fun x => Nat.add x (Nat.shiftLeft 1 p)) ih).trans ?_
    show (sumPow t + 1 <<< p) = sumPow t + 2 ^ p
    rw [Nat.one_shiftLeft]

private theorem testBit_orFrom (a : Nat) (O : List Nat) (q : Nat) :
    (orFrom a O).testBit q = (a.testBit q || decide (q ∈ O)) := by
  induction O with
  | nil => simp [orFrom]
  | cons p t ih =>
    rw [show orFrom a (p :: t) = orFrom a t ||| 2 ^ p from rfl, Nat.testBit_or, ih,
      Nat.testBit_two_pow]
    by_cases h : p = q
    · subst h
      simp
    · have h' : q ≠ p := fun e => h e.symm
      simp [h, h']

private theorem or_two_pow_of_testBit_true {x p : Nat} (h : x.testBit p = true) :
    x ||| 2 ^ p = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : p = i
  · subst hi
    simp [h]
  · simp [hi]

private theorem or_two_pow_of_testBit_false {x p : Nat} (h : x.testBit p = false) :
    x ||| 2 ^ p = x + 2 ^ p := by
  obtain ⟨q, r, hrlt, rfl⟩ : ∃ q r, r < 2 ^ (p + 1) ∧ x = 2 ^ (p + 1) * q + r :=
    ⟨x / 2 ^ (p + 1), x % 2 ^ (p + 1), Nat.mod_lt _ (Nat.two_pow_pos _),
      (Nat.div_add_mod _ _).symm⟩
  rw [Nat.testBit_two_pow_mul_add q hrlt p, if_pos (Nat.lt_succ_self p)] at h
  have hr : r < 2 ^ p := by
    rcases Nat.lt_or_ge r (2 ^ p) with hlt | hge
    · exact hlt
    · exact absurd (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hge hrlt)
        (by rw [h]; decide)
  have hlt1 : r + 2 ^ p < 2 ^ (p + 1) := by
    rw [Nat.pow_succ]
    omega
  calc (2 ^ (p + 1) * q + r) ||| 2 ^ p
      = ((2 ^ (p + 1) * q) ||| r) ||| 2 ^ p := by rw [← Nat.two_pow_add_eq_or_of_lt hrlt]
    _ = (2 ^ (p + 1) * q) ||| (r ||| 2 ^ p) := Nat.or_assoc _ _ _
    _ = (2 ^ (p + 1) * q) ||| (r + 2 ^ p) := by rw [Nat.or_two_pow_eq_add_of_lt hr]
    _ = 2 ^ (p + 1) * q + (r + 2 ^ p) := (Nat.two_pow_add_eq_or_of_lt hlt1 q).symm
    _ = (2 ^ (p + 1) * q + r) + 2 ^ p := by omega

private theorem orFrom_zero_le_nodup (O : List Nat) :
    orFrom 0 O ≤ sumPow O ∧ (orFrom 0 O = sumPow O → O.Nodup) := by
  induction O with
  | nil => simp [orFrom, sumPow]
  | cons p t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpos : 0 < 2 ^ p := Nat.two_pow_pos p
    show orFrom 0 t ||| 2 ^ p ≤ sumPow t + 2 ^ p ∧
      (orFrom 0 t ||| 2 ^ p = sumPow t + 2 ^ p → (p :: t).Nodup)
    cases hb : (orFrom 0 t).testBit p
    · rw [or_two_pow_of_testBit_false hb]
      refine ⟨by omega, fun heq => ?_⟩
      refine List.nodup_cons.2 ⟨fun hp => ?_, ih2 (by omega)⟩
      have := testBit_orFrom 0 t p
      rw [hb] at this
      simp [hp] at this
    · rw [or_two_pow_of_testBit_true hb]
      exact ⟨by omega, fun heq => by omega⟩

private theorem land_shiftRight_one {S q : Nat} :
    Nat.beq (Nat.land (Nat.shiftRight S q) 1) 1 = S.testBit q := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e : Nat.land (Nat.shiftRight S q) 1 = S / 2 ^ q % 2 := by
    rw [show Nat.land (Nat.shiftRight S q) 1 = (S >>> q) &&& 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [e, Bool.eq_iff_iff]
  simp

private theorem testBit_pow_sub {n p : Nat} (hp : p < n) :
    (Nat.sub (Nat.shiftLeft 1 n) 1).testBit p = true := by
  show ((1 <<< n) - 1).testBit p = true
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  simpa using hp

private noncomputable def lvRec (f : Nat → Bool) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) []
    (fun l acc => Bool.rec (motive := fun _ => List Nat) acc (List.cons l acc) (f l)) n

private theorem lvRec_succ (f : Nat → Bool) (n : Nat) :
    lvRec f (n + 1) = if f n = true then n :: lvRec f n else lvRec f n := by
  show Bool.rec (motive := fun _ => List Nat) (lvRec f n) (List.cons n (lvRec f n)) (f n) = _
  cases f n <;> rfl

private theorem mem_lvRec (f : Nat → Bool) (n l : Nat) : l ∈ lvRec f n ↔ l < n ∧ f l = true := by
  induction n with
  | zero =>
    show l ∈ ([] : List Nat) ↔ l < 0 ∧ f l = true
    simp
  | succ n ih =>
    rw [lvRec_succ]
    by_cases hf : f n = true
    · rw [if_pos hf, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by omega, hf⟩
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hl : l = n
        · exact Or.inl hl
        · exact Or.inr ⟨by omega, h2⟩
    · rw [if_neg hf, ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        have : l ≠ n := by
          rintro rfl
          exact hf h2
        exact ⟨by omega, h2⟩

private theorem letLN'_gen (k : List Nat → Bool) (l : List Nat) : ∀ acc : List Nat,
    (List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc.reverse)
      (fun x _ ih acc => letB x fun x => ih (List.cons x acc)) l) acc = k (acc.reverse ++ l) := by
  induction l with
  | nil =>
    intro acc
    simp
  | cons x l ih =>
    intro acc
    refine (letB_eq _ _).trans ?_
    rw [ih]
    simp

private theorem letLN'_eq (l : List Nat) (k : List Nat → Bool) : treesK.letLN' l k = k l := by
  have := letLN'_gen k l []
  rw [List.reverse_nil, List.nil_append] at this
  exact this

private noncomputable def fmtR (cs : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun st => notB (Nat.beq st 1))
    (fun c _ ih st => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (andB (Nat.ble 48 c) (Nat.ble c 57)) (ih 2))
        (andB (Nat.beq st 0) (ih 1)) (Nat.beq c 45))
      (andB (notB (Nat.beq st 1)) (ih 0)) (Nat.beq c 32)) cs

private noncomputable def intsR (cs : List Nat) : Nat → Bool → List Int :=
  List.rec (motive := fun _ => Nat → Bool → List Int)
    (fun cur ng => Bool.rec (motive := fun _ => List Int) [intsK.tok cur ng] [] (Nat.beq cur 0))
    (fun c _ ih cur ng => Bool.rec (motive := fun _ => List Int)
      (Bool.rec (motive := fun _ => List Int)
        (ih (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))) ng) (ih cur true)
        (Nat.beq c 45))
      (Bool.rec (motive := fun _ => List Int) (List.cons (intsK.tok cur ng) (ih 0 false))
        (ih 0 false) (Nat.beq cur 0))
      (Nat.beq c 32)) cs

private theorem fmtW_eq_R (cs : List Nat) : fmtW cs = fmtR cs 0 := rfl

private theorem intsK_eq_R (cs : List Nat) : intsK cs = intsR cs 0 false := rfl

private theorem fmtR_nil (st : Nat) : fmtR [] st = true ↔ st ≠ 1 := by
  show notB (Nat.beq st 1) = true ↔ st ≠ 1
  constructor
  · intro h e
    subst e
    simp [notB] at h
  · intro h
    simp [notB, beq_false_of_ne' h]

private theorem fmtR_cons (c : Nat) (cs : List Nat) (st : Nat) :
    fmtR (c :: cs) st = true ↔
      (c = 32 ∧ st ≠ 1 ∧ fmtR cs 0 = true) ∨
      (c ≠ 32 ∧ c = 45 ∧ st = 0 ∧ fmtR cs 1 = true) ∨
      (c ≠ 32 ∧ c ≠ 45 ∧ (48 ≤ c ∧ c ≤ 57) ∧ fmtR cs 2 = true) := by
  have e : fmtR (c :: cs) st =
      if c = 32 then (!(Nat.beq st 1) && fmtR cs 0)
      else if c = 45 then (Nat.beq st 0 && fmtR cs 1)
      else ((Nat.ble 48 c && Nat.ble c 57) && fmtR cs 2) := by
    simp only [fmtR, boolRec_eq, Bool.cond_eq_ite, Nat.beq_eq, andB_eq, notB_eq]
  rw [e]
  by_cases h32 : c = 32
  · simp [h32, beq_eq_false_iff']
  · by_cases h45 : c = 45
    · simp [h32, h45]
    · simp [h32, h45]

private theorem intsR_nil (cur : Nat) (ng : Bool) :
    intsR [] cur ng = if cur = 0 then [] else [intsK.tok cur ng] := by
  simp only [intsR, boolRec_eq, Bool.cond_eq_ite, Nat.beq_eq]

private theorem intsR_space (cs : List Nat) (cur : Nat) (ng : Bool) :
    intsR (32 :: cs) cur ng =
      (if cur = 0 then [] else [intsK.tok cur ng]) ++ intsR cs 0 false := by
  by_cases h : cur = 0
  · subst h
    rfl
  · simp [intsR, beq_false_of_ne' h, h]

private theorem intsR_neg (cs : List Nat) (cur : Nat) (ng : Bool) :
    intsR (45 :: cs) cur ng = intsR cs cur true := rfl

private theorem intsR_digit (c : Nat) (cs : List Nat) (cur : Nat) (ng : Bool) (h32 : c ≠ 32)
    (h45 : c ≠ 45) :
    intsR (c :: cs) cur ng =
      intsR cs (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))) ng := by
  simp [intsR, beq_false_of_ne' h32, beq_false_of_ne' h45]

private def stOf (ng : Bool) (ds : List Nat) : Nat :=
  if ds = [] then (if ng then 1 else 0) else 2

private def curOf (ds : List Nat) : Nat := if ds = [] then 0 else decVal ds + 1

private def pre (ng : Bool) (ds : List Nat) : List Nat := (if ng then [45] else []) ++ ds

private def IsTok (l : List Nat) : Prop := IsDigits l ∨ ∃ ds, IsDigits ds ∧ l = 45 :: ds

private def tokVal (l : List Nat) : Int :=
  if l.head? = some 45 then -(decVal l.tail : Int) else (decVal l : Int)

private theorem stOf_ne {ng : Bool} {ds : List Nat} (h : ds ≠ []) : stOf ng ds = 2 := by
  simp [stOf, h]

private theorem curOf_nil : curOf [] = 0 := by simp [curOf]

private theorem pre_false_nil : pre false [] = [] := by simp [pre]

private theorem pre_true_nil : pre true [] = [45] := by simp [pre]

private theorem decVal_snoc (ds : List Nat) (c : Nat) :
    decVal (ds ++ [c]) = 10 * decVal ds + (c - 48) := by
  simp [decVal, List.foldl_append]

private theorem curOf_snoc (ds : List Nat) (c : Nat) :
    curOf (ds ++ [c]) = Nat.succ (Nat.add (Nat.mul 10 (Nat.pred (curOf ds))) (Nat.sub c 48)) := by
  by_cases h : ds = []
  · subst h
    simp [curOf, decVal]
  · simp [curOf, h, decVal_snoc]

private theorem pre_no32 (ng : Bool) (ds : List Nat) (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57) :
    32 ∉ pre ng ds := by
  intro h
  cases ng
  · have := hds 32 (by simpa [pre] using h)
    omega
  · simp only [pre, if_true, List.singleton_append, List.mem_cons] at h
    rcases h with h | h
    · omega
    · have := hds 32 h
      omega

private theorem pre_snoc (ng : Bool) (ds : List Nat) (c : Nat) (cs : List Nat) :
    pre ng (ds ++ [c]) ++ cs = pre ng ds ++ c :: cs := by
  simp [pre, List.append_assoc]

private theorem tok_eq (cur : Nat) (ng : Bool) :
    intsK.tok cur ng = if ng then -((cur - 1 : Nat) : Int) else ((cur - 1 : Nat) : Int) := by
  cases ng
  · rfl
  · rfl

private theorem tokVal_pre (ng : Bool) (ds : List Nat) (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57) :
    tokVal (pre ng ds) = if ng then -(decVal ds : Int) else (decVal ds : Int) := by
  cases ng
  · cases ds with
    | nil => simp [tokVal, pre]
    | cons d t =>
      have hd := hds d (by simp)
      have hne : d ≠ 45 := by omega
      simp [tokVal, pre, hne]
  · simp [tokVal, pre]

private theorem isTok_pre (ng : Bool) (ds : List Nat) (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57)
    (hd : ds ≠ []) : IsTok (pre ng ds) := by
  cases ng
  · exact Or.inl ⟨by simpa [pre] using hd, by simpa [pre] using hds⟩
  · exact Or.inr ⟨ds, ⟨hd, hds⟩, by simp [pre]⟩

private theorem endTok (ng : Bool) (ds : List Nat) (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57)
    (hst : ¬ (ds = [] ∧ ng = true)) (R : List (List Nat)) :
    (((pre ng ds :: R).filter (· != [])).map tokVal =
      (if curOf ds = 0 then [] else [intsK.tok (curOf ds) ng]) ++
        (R.filter (· != [])).map tokVal) ∧
    (∀ l ∈ (pre ng ds :: R).filter (· != []), l ∈ R.filter (· != []) ∨ IsTok l) := by
  by_cases hd : ds = []
  · have hng : ng = false := by
      cases ng
      · rfl
      · exact absurd ⟨hd, rfl⟩ hst
    subst hd
    subst hng
    refine ⟨by simp [pre_false_nil, curOf_nil], fun l hl => Or.inl ?_⟩
    simpa [pre_false_nil] using hl
  · have hcur : curOf ds ≠ 0 := by simp [curOf, hd]
    have hcur1 : curOf ds - 1 = decVal ds := by simp [curOf, hd]
    have hne : pre ng ds ≠ [] := by
      cases ng
      · simpa [pre] using hd
      · simp [pre]
    have htok : intsK.tok (curOf ds) ng = tokVal (pre ng ds) := by
      rw [tok_eq, tokVal_pre ng ds hds, hcur1]
    have hbne : (pre ng ds != []) = true := by simpa using hne
    constructor
    · rw [List.filter_cons, if_pos hbne, List.map_cons, if_neg hcur, htok]
      rfl
    · intro l hl
      rw [List.filter_cons, if_pos hbne] at hl
      rcases List.mem_cons.1 hl with rfl | hl'
      · exact Or.inr (isTok_pre ng ds hds hd)
      · exact Or.inl hl'

private theorem intsK_main (cs : List Nat) : ∀ (ng : Bool) (ds : List Nat),
    (∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57) → fmtR cs (stOf ng ds) = true →
    intsR cs (curOf ds) ng = (((pre ng ds ++ cs).splitOn 32).filter (· != [])).map tokVal ∧
    (∀ l ∈ ((pre ng ds ++ cs).splitOn 32).filter (· != []), IsTok l) ∧ (∀ c ∈ cs, c < 128) := by
  induction cs with
  | nil =>
    intro ng ds hds h
    have hst : ¬ (ds = [] ∧ ng = true) := by
      rintro ⟨rfl, rfl⟩
      exact (fmtR_nil _).1 h (by simp [stOf])
    rw [List.append_nil, List.splitOn_eq_singleton (pre_no32 ng ds hds)]
    obtain ⟨e1, e2⟩ := endTok ng ds hds hst []
    refine ⟨?_, fun l hl => ?_, fun c hc => by simp at hc⟩
    · rw [intsR_nil]
      simpa using e1.symm
    · rcases e2 l hl with h | h
      · simp at h
      · exact h
  | cons c cs ih =>
    intro ng ds hds h
    rcases (fmtR_cons c cs _).1 h with ⟨rfl, hst, h'⟩ | ⟨hne, rfl, hst, h'⟩ |
      ⟨hne32, hne45, hdig, h'⟩
    · have hst' : ¬ (ds = [] ∧ ng = true) := by
        rintro ⟨rfl, rfl⟩
        exact hst (by simp [stOf])
      obtain ⟨ih1, ih2, ih3⟩ := ih false [] (by simp) (by simpa [stOf] using h')
      simp only [pre_false_nil, curOf_nil, List.nil_append] at ih1 ih2
      obtain ⟨e1, e2⟩ := endTok ng ds hds hst' (cs.splitOn 32)
      rw [List.splitOn_append_cons_self_of_not_mem (pre_no32 ng ds hds)]
      refine ⟨?_, fun l hl => ?_, fun c' hc' => ?_⟩
      · rw [intsR_space, e1, ih1]
      · rcases e2 l hl with h2 | h2
        · exact ih2 l h2
        · exact h2
      · rcases List.mem_cons.1 hc' with rfl | hc''
        · omega
        · exact ih3 c' hc''
    · have hdsnil : ds = [] ∧ ng = false := by
        by_cases hd : ds = []
        · subst hd
          cases ng
          · exact ⟨rfl, rfl⟩
          · simp [stOf] at hst
        · simp [stOf, hd] at hst
      obtain ⟨rfl, rfl⟩ := hdsnil
      obtain ⟨ih1, ih2, ih3⟩ := ih true [] (by simp) (by simpa [stOf] using h')
      simp only [pre_true_nil, pre_false_nil, curOf_nil, List.nil_append,
        List.singleton_append] at ih1 ih2 ⊢
      refine ⟨?_, ih2, ?_⟩
      · rw [intsR_neg]
        exact ih1
      · intro c' hc'
        rcases List.mem_cons.1 hc' with rfl | hc''
        · omega
        · exact ih3 c' hc''
    · have hds' : ∀ x ∈ ds ++ [c], 48 ≤ x ∧ x ≤ 57 := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hds x hx
        · simp at hx
          subst hx
          exact hdig
      have hne : ds ++ [c] ≠ [] := by simp
      obtain ⟨ih1, ih2, ih3⟩ := ih ng (ds ++ [c]) hds' (by rw [stOf_ne hne]; exact h')
      rw [pre_snoc] at ih1 ih2
      refine ⟨?_, ih2, ?_⟩
      · rw [intsR_digit c cs _ ng hne32 hne45, ← curOf_snoc]
        exact ih1
      · intro c' hc'
        rcases List.mem_cons.1 hc' with rfl | hc''
        · omega
        · exact ih3 c' hc''

private theorem tokVal_digits {l : List Nat} (hd : IsDigits l) : tokVal l = (decVal l : Int) := by
  obtain ⟨hne, hall⟩ := hd
  cases l with
  | nil => exact absurd rfl hne
  | cons d t =>
    have h := hall d (by simp)
    have h45 : d ≠ 45 := by omega
    simp [tokVal, h45]

private theorem tokVal_neg {ds : List Nat} : tokVal (45 :: ds) = -(decVal ds : Int) := by
  simp [tokVal]

end T46Pk

open T46Pk

theorem ptsK_spec {UL : List Nat} {UP : Nat} (h : ptsK UL UP = true) :
    UL.length = 693 ∧ UP < 2 ^ (12 * 693) ∧ (∀ i < 693, fd 12 UP i = UL.getD i 0) ∧
      (∀ i < 692, UL.getD i 0 < UL.getD (i + 1) 0) ∧
      ∀ x < 693, normC (tvC 0 (UL.getD x 0)) = UL.getD x 0 := by
  unfold ptsK at h
  simp only [andB_eq, letB_eq, Bool.and_eq_true, allN_lqt_iff, Nat.beq_eq, Nat.blt_eq, at'_eq,
    nthN_eq, lenN_misc_eq, normK_eq, tvK_eq, Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · have e : Nat.shiftLeft 1 (Nat.mul 12 693) = 2 ^ (12 * 693) := Nat.one_shiftLeft _
    rw [e] at h2
    exact h2
  · intro i hi
    have := h4 i hi
    rwa [h3 i (by omega), h3 (i + 1) (by omega)] at this
  · intro x hx
    have := h5 x hx
    rwa [h3 x hx] at this

theorem genK_spec {UP v G : Nat} (h : genK UP v G = true) :
    G < 2 ^ (10 * 693) ∧ IsPermN 693 (fd 10 G) ∧
      ∀ x < 693, fd 12 UP (fd 10 G x) = normC (tvC v (fd 12 UP x)) := by
  unfold genK at h
  simp only [andB_eq, letB_eq, Bool.and_eq_true, allN_lqt_iff, Nat.beq_eq, Nat.blt_eq, at'_eq,
    normK_eq, tvK_eq] at h
  obtain ⟨hp, hx⟩ := h
  obtain ⟨hlt, hperm⟩ := permK_iff.1 hp
  refine ⟨hlt, hperm, fun x hx' => ?_⟩
  exact (hx x hx').2

theorem gensOK_spec {UL : List Nat} {UP : Nat} {GP : List Nat}
    (h : ∀ k < 46, gensOK UL UP GP k 1 = true) :
    (gensK UL).length = 46 ∧ GP.length = 46 ∧
      ∀ k < 46, genK UP ((gensK UL).getD k 0) (GP.getD k 0) = true := by
  have h0 := h 0 (by decide)
  unfold gensOK at h0
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq] at h0
  refine ⟨h0.1, h0.2.1, fun k hk => ?_⟩
  have hk' := h k hk
  unfold gensOK at hk'
  simp only [andB_eq, letB_eq, impB_eq, Bool.and_eq_true, allN_lqt_iff, Nat.blt_eq, nthN_eq] at hk'
  have h2 := hk'.2.2 0 (by decide)
  have hb : Nat.blt k 46 = true := Nat.blt_eq.mpr hk
  simp [hb] at h2
  simpa using h2

theorem lettersOK_iff (m : Nat) (w : List Int) :
    lettersOK m w = true ↔ ∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ m := by
  induction w with
  | nil => simp [lettersOK]
  | cons z t ih =>
    have e : lettersOK m (z :: t) =
        (((Nat.ble 1 z.natAbs) && (Nat.ble z.natAbs m)) && lettersOK m t) := rfl
    rw [e]
    simp [ih]

theorem lettersK_spec {GP : List Nat} {WC : List (List Nat)} {LP : List Nat}
    (h : lettersK GP WC LP = true) :
    WC.length = 53 ∧ LP.length = 106 ∧ (∀ w ∈ WC, fmtW w = true) ∧
      (∀ k < 46, intsK (WC.getD k []) = [(k : Int) + 1]) ∧
      ∀ j < 53, lettersOK 46 (intsK (WC.getD j [])) = true ∧
        LP.getD (2 * j) 0 = wordG GP (intsK (WC.getD j [])) ∧
        permK 693 10 (LP.getD (2 * j + 1) 0) = true ∧
        compP 693 10 (LP.getD (2 * j) 0) (LP.getD (2 * j + 1) 0) = idP 693 10 := by
  unfold lettersK at h
  simp only [andB_eq, letB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq, lenLLN_eq, allLL_iff,
    allN_lqt_iff, decide_eq_true_eq, nthL_eq, nthN_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun k hk => ?_, h5⟩
  rw [h4 k hk]
  simp

theorem mem_lvK {LP : List Nat} {b l : Nat} :
    l ∈ lvK LP b ↔ l < LP.length ∧ fd 10 (LP.getD l 0) b = b := by
  have e : lvK LP b = lvRec (fun l => Nat.beq (at' 10 (wordM7.nthN LP l) b) b) LP.length := by
    unfold lvK lvRec
    rw [lenN_misc_eq]
  rw [e, mem_lvRec]
  simp [at'_eq, nthN_eq]

theorem orbK_spec {LP lv : List Nat} {root m : Nat} {O Pa La : List Nat} (hm : 0 < m)
    (h : orbK LP lv root m O Pa La = true) :
    O.length = m ∧ (∀ p ∈ O, p < 693) ∧ O.Nodup ∧ O.head? = some root ∧
      (∀ i < m, 0 < i → ∃ a < i, ∃ l ∈ lv, fd 10 (LP.getD l 0) (O.getD a 0) = O.getD i 0) ∧
      ∀ l ∈ lv, ∀ p ∈ O, fd 10 (LP.getD l 0) p ∈ O := by
  unfold orbK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨hO, hPa, hLa, hlt, hsum, hroot, hpar, hcl⟩ := h
  simp only [recOr_eq, recSum_eq] at hsum hcl
  have hOlen : O.length = m := by
    have := Nat.eq_of_beq_eq_true hO
    rwa [lenN_misc_eq] at this
  refine ⟨hOlen, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := (allL_lqt_iff.1 hlt) p hp
    simpa using this
  · exact (orFrom_zero_le_nodup O).2 (Nat.eq_of_beq_eq_true hsum).symm
  · have h0 : O.getD 0 0 = root := by
      have := Nat.eq_of_beq_eq_true hroot
      rwa [nthN_eq] at this
    cases O with
    | nil =>
      simp at hOlen
      omega
    | cons a t => simpa using h0
  · intro i hi hi0
    have := allN_lqt_iff.1 hpar i hi
    rw [impB_eq] at this
    have hb : Nat.blt 0 i = true := Nat.blt_eq.mpr hi0
    simp only [hb, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, memN_eq,
      decide_eq_true_eq, at'_eq, nthN_eq] at this
    obtain ⟨ha, hl, he⟩ := this
    exact ⟨Pa.getD i 0, ha, La.getD i 0, hl, he⟩
  · intro l hl p hp
    have h1 := allL_lqt_iff.1 hcl l hl
    have h2 := allL_lqt_iff.1 h1 p hp
    rw [land_shiftRight_one, at'_eq, nthN_eq] at h2
    have := testBit_orFrom 0 O (fd 10 (LP.getD l 0) p)
    rw [h2] at this
    simpa using this.symm

theorem treesK_spec {LP BL : List Nat} {r : Nat} {O1 Pa1 La1 O2 Pa2 La2 : List Nat}
    (h : treesK LP BL r O1 Pa1 La1 O2 Pa2 La2 = true) :
    BL.length = 5 ∧ orbK LP (lvK LP (BL.getD 0 0)) (BL.getD 1 0) 512 O1 Pa1 La1 = true ∧
      orbK LP (lvK LP (BL.getD 0 0)) r 180 O2 Pa2 La2 = true ∧
      ∀ p < 693, p = 0 ∨ p ∈ O1 ∨ p ∈ O2 := by
  unfold treesK at h
  rw [letLN'_eq] at h
  simp only [andB_eq, letB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq, nthN_eq] at h
  obtain ⟨hBL, h1, h2, hS⟩ := h
  refine ⟨hBL, h1, h2, fun p hp => ?_⟩
  rw [recOr_eq] at hS
  have hb := testBit_orFrom 1 (List.append O1 O2) p
  rw [hS, testBit_pow_sub hp] at hb
  have hb' : Nat.testBit 1 p = true ∨ p ∈ O1 ∨ p ∈ O2 := by
    simpa using hb.symm
  rcases hb' with hb' | hb' | hb'
  · exact Or.inl (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hb')
  · exact Or.inr (Or.inl hb')
  · exact Or.inr (Or.inr hb')

theorem xyK_spec {GP : List Nat} {xw yw : List Int} (h : xyK GP xw yw = true) :
    lettersOK 46 xw = true ∧ lettersOK 46 yw = true ∧
      powP 2 (powP 3 (wordG GP xw)) = idP 693 10 ∧ powP 3 (wordG GP xw) ≠ idP 693 10 ∧
      powP 3 (powP 2 (wordG GP yw)) = idP 693 10 ∧ powP 2 (wordG GP yw) ≠ idP 693 10 ∧
      powP 11 (compP 693 10 (powP 3 (wordG GP xw)) (powP 2 (wordG GP yw))) = idP 693 10 ∧
      compP 693 10 (powP 3 (wordG GP xw)) (powP 2 (wordG GP yw)) ≠ idP 693 10 := by
  unfold xyK at h
  simp only [andB_eq, letB_eq, notB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, ne_of_not_beq h4, h5, ne_of_not_beq h6, h7, ne_of_not_beq h8⟩

theorem tvWordsK_spec {GP : List Nat} {xw yw : List Int} {TW : List (List Nat)}
    (h : ∀ k < 46, tvWordsK GP xw yw TW k 1 = true) :
    TW.length = 46 ∧ ∀ k < 46,
      wordXY (powP 3 (wordG GP xw)) (powP 2 (wordG GP yw)) (TW.getD k []) = GP.getD k 0 := by
  have h0 := h 0 (by decide)
  unfold tvWordsK at h0
  simp only [andB_eq, letB_eq, Bool.and_eq_true, Nat.beq_eq, lenLLN_eq] at h0
  refine ⟨h0.1, fun k hk => ?_⟩
  have hk' := h k hk
  unfold tvWordsK at hk'
  simp only [andB_eq, letB_eq, impB_eq, Bool.and_eq_true, allN_lqt_iff, Nat.blt_eq, Nat.beq_eq,
    nthN_eq, nthL_eq] at hk'
  have h2 := hk'.2 0 (by decide)
  have hb : Nat.blt k 46 = true := Nat.blt_eq.mpr hk
  simp [hb] at h2
  simpa using h2

theorem intsK_eq {cs : List Nat} (h : fmtW cs = true) :
    wordOfInts (strL cs) = intsK cs := by
  rw [fmtW_eq_R] at h
  obtain ⟨h1, h2, h3⟩ := intsK_main cs false [] (by simp) (by simpa [stOf] using h)
  simp only [pre_false_nil, curOf_nil, List.nil_append] at h1 h2
  rw [intsK_eq_R, h1]
  unfold wordOfInts
  rw [splitOn_space_strL h3, List.filter_map, List.map_map]
  have hf : List.filter ((· != "") ∘ strL) (cs.splitOn 32) =
      List.filter (· != []) (cs.splitOn 32) :=
    List.filter_congr (fun l _ => by
      rw [Function.comp_apply, Bool.eq_iff_iff]
      simp [strL_eq_empty_iff])
  rw [hf]
  apply List.map_congr_left
  intro l hl
  rcases h2 l hl with hd | ⟨ds, hds, rfl⟩
  · simp [Function.comp, toInt?_strL hd, tokVal_digits hd]
  · simp [Function.comp, toInt?_strL_neg hds, tokVal_neg]

end CFSG.KS.PK

end
