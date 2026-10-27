module

public import Certificates.Data.Kernel.ExactGen.Parse
import all CFSG.LocalAnalysis.ComponentClassification.ExactGenParse
import all Init.Data.String.Slice
import all Init.Data.String.Search
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Char.Basic

public section

namespace CFSG.KC.ExactGen

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

private theorem forIn_yield {L : List Char}
    {f : Char → Option Bool × Bool → Id (ForInStep (Option Bool × Bool))}
    (hf : ∀ c ∈ L, ∀ s, f c s = pure (.yield (none, true))) :
    ∀ s, forIn L s f = pure (if L = [] then s else (none, true)) := by
  induction L with
  | nil => intro s; rfl
  | cons c L ih =>
    intro s
    rw [List.forIn_cons, hf c List.mem_cons_self s]
    change forIn L (none, true) f = _
    rw [ih (fun c hc s => hf c (List.mem_cons_of_mem _ hc) s)]
    simp

private theorem digit_ne {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl
  exact absurd h (by decide)

private theorem isNat_of {r : String.Slice} {ds : List Char} (hr : r.copy.toList = ds)
    (hd : ∀ c ∈ ds, c.isDigit = true) : r.isNat = !ds.isEmpty := by
  unfold String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, hr]
  rw [forIn_yield]
  · cases ds <;> rfl
  · intro c hc s
    simp [digit_ne (hd c hc), hd c hc]

private theorem foldl_digits : ∀ (L : List Char) (acc : Nat), (∀ c ∈ L, c.isDigit = true) →
    L.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) acc =
      L.foldl (fun n c => n * 10 + (c.toNat - 48)) acc
  | [], _, _ => rfl
  | c :: L, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, ite_eq_right (digit_ne (h c List.mem_cons_self))]
    exact foldl_digits L _ fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem natGo_eq : ∀ (ds : List Char) (acc : ℕ),
    natGo acc ds = ds.foldl (fun n c => n * 10 + (c.toNat - 48)) acc
  | [], _ => rfl
  | c :: ds, acc => natGo_eq ds _

private theorem toNat_of {r : String.Slice} {ds : List Char} (hr : r.copy.toList = ds)
    (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) : r.toNat? = some (natOfL ds) := by
  unfold String.Slice.toNat?
  rw [isNat_of hr hd]
  cases ds with
  | nil => exact absurd rfl hne
  | cons c L =>
    simp only [List.isEmpty_cons, Bool.not_false, ↓reduceIte, String.Slice.foldl_eq_foldl_toList, hr]
    exact congrArg some ((foldl_digits (c :: L) 0 hd).trans (natGo_eq (c :: L) 0).symm)

private theorem beq_char (c d : Char) : Nat.beq c.toNat d.toNat = decide (c = d) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, Char.toNat_inj]

theorem isWs_eq (c : Char) : isWs c = c.isWhitespace := by
  have e1 : (32 : ℕ) = ' '.toNat := rfl
  have e2 : (9 : ℕ) = '\t'.toNat := rfl
  have e3 : (13 : ℕ) = '\r'.toNat := rfl
  have e4 : (10 : ℕ) = '\n'.toNat := rfl
  unfold isWs Char.isWhitespace
  rw [e1, e2, e3, e4, beq_char, beq_char, beq_char, beq_char]

theorem isDig_eq (c : Char) : isDig c = c.isDigit := by
  rw [Bool.eq_iff_iff]
  unfold isDig Char.isDigit
  simp only [Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq, UInt32.le_iff_toNat_le]
  rfl

theorem allDig_iff : ∀ ds : List Char, allDig ds = true ↔ ∀ c ∈ ds, c.isDigit = true
  | [] => by simp [allDig]
  | c :: ds => by
    simp only [allDig, Bool.and_eq_true, isDig_eq, allDig_iff ds, List.mem_cons, forall_eq_or_imp]

theorem minus_eq (c : Char) : Nat.beq c.toNat 45 = decide (c = '-') := by
  have e : (45 : ℕ) = '-'.toNat := rfl
  rw [e, beq_char]

theorem toInt_ofList {t : List Char} (h : tokOK t = true) : (String.ofList t).toInt! = intOfL t := by
  unfold String.toInt! String.Slice.toInt! String.Slice.toInt?
  cases t with
  | nil => exact absurd h (by decide)
  | cons c ds =>
    by_cases hc : c = '-'
    · subst hc
      simp only [tokOK, minus_eq, decide_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff, allDig_iff] at h
      obtain ⟨hne, hd⟩ := h
      have hs : (String.ofList ('-' :: ds)).toSlice.startsWith '-' = true := by
        rw [String.Slice.startsWith_char_eq_head?, String.copy_toSlice, String.toList_ofList]
        rfl
      obtain ⟨r, hr⟩ : ∃ r, (String.ofList ('-' :: ds)).toSlice.dropPrefix? '-' = some r := by
        cases e : (String.ofList ('-' :: ds)).toSlice.dropPrefix? '-' with
        | none =>
          rw [String.Slice.dropPrefix?_eq_none_iff, hs] at e
          exact absurd e (by decide)
        | some r => exact ⟨r, rfl⟩
      have hcopy := String.Slice.eq_append_of_dropPrefix?_char_eq_some hr
      rw [String.copy_toSlice] at hcopy
      have hl : r.copy.toList = ds := by
        have e := congrArg String.toList hcopy
        rw [String.toList_ofList, String.toList_append, String.toList_singleton] at e
        exact (List.cons.inj e).2.symm
      rw [hr]
      simp only [toNat_of hl hd hne, Option.map_some, intOfL, minus_eq, decide_true, ↓reduceIte]
    · simp only [tokOK, minus_eq, hc, decide_false, Bool.false_eq_true, ↓reduceIte,
        allDig_iff] at h
      have hs : (String.ofList (c :: ds)).toSlice.startsWith '-' = false := by
        rw [String.Slice.startsWith_char_eq_head?, String.copy_toSlice, String.toList_ofList]
        simp [hc]
      have hn := String.Slice.dropPrefix?_eq_none_iff.2 hs
      rw [hn]
      have hr : (String.ofList (c :: ds)).toSlice.copy.toList = c :: ds := by
        rw [String.copy_toSlice, String.toList_ofList]
      simp only [toNat_of hr h (List.cons_ne_nil c ds), Option.map_some, intOfL, minus_eq, hc,
        decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem isEmpty_ofList (t : List Char) : (String.ofList t).isEmpty = t.isEmpty := by
  cases t with
  | nil => rfl
  | cons c t =>
    rw [List.isEmpty_cons, Bool.eq_false_iff]
    intro he
    have e := congrArg String.toList (String.isEmpty_iff.1 he)
    simp at e

theorem toksGo_eq : ∀ (cs acc : List Char),
    toksGo cs acc = (List.splitOnPPrepend Char.isWhitespace cs acc).filter fun t => !t.isEmpty
  | [], acc => by
    cases acc <;> simp [toksGo, List.splitOnPPrepend]
  | c :: t, acc => by
    rw [toksGo, List.splitOnPPrepend, isWs_eq]
    by_cases hc : c.isWhitespace = true
    · simp only [hc, ↓reduceIte, List.filter_cons, toksGo_eq t []]
      cases acc <;> simp
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, toksGo_eq t (c :: acc)]

theorem toksL_eq (cs : List Char) :
    toksL cs = (List.splitOnP Char.isWhitespace cs).filter fun t => !t.isEmpty := by
  rw [toksL, toksGo_eq, List.splitOnP_eq_splitOnPPrepend]

theorem fcTokens_ofList {cs : List Char} (h : intsOK cs = true) :
    fcTokens (String.ofList cs) = (intsL cs).toArray := by
  unfold fcTokens intsL intsOK at *
  rw [toksL_eq] at *
  rw [String.splitToList_of_valid, String.toList_ofList, List.filter_map]
  have hf : ((fun s : String => !s.isEmpty) ∘ String.ofList) = fun t : List Char => !t.isEmpty := by
    funext t
    simp only [Function.comp_apply, isEmpty_ofList]
  rw [hf, List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  exact toInt_ofList (List.all_eq_true.1 h t ht)

def Corr {α : Type} (f : RdM α) (g : RL α) : Prop :=
  ∀ (A : Array ℤ) (p : ℕ), ∃ q, f.run ⟨A, p⟩ = ((g (A.toList.drop p)).1, (⟨A, q⟩ : Rd)) ∧
    (g (A.toList.drop p)).2 = A.toList.drop q

theorem corr_congr {α : Type} {f : RdM α} {g g' : RL α} (h : Corr f g) (e : ∀ l, g l = g' l) :
    Corr f g' := by
  intro A p
  rw [← e]
  exact h A p

theorem getElem!_eq_headD (A : Array ℤ) (p : ℕ) : A[p]! = (A.toList.drop p).headD 0 := by
  by_cases h : p < A.size
  · rw [getElem!_pos A p h, List.drop_eq_getElem_cons (by simpa using h), List.headD_cons,
      Array.getElem_toList]
  · rw [getElem!_neg A p h, List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt h)]
    rfl

theorem corr_int : Corr rdInt rlInt := by
  intro A p
  refine ⟨p + 1, ?_, ?_⟩
  · have e : rdInt.run ⟨A, p⟩ = (A[p]!, (⟨A, p + 1⟩ : Rd)) := rfl
    rw [e, getElem!_eq_headD]
    rfl
  · simp only [rlInt, List.tail_drop]

theorem corr_pure {α : Type} (a : α) : Corr (pure a) (fun l => (a, l)) := by
  intro A p
  exact ⟨p, rfl, rfl⟩

theorem corr_bind {α β : Type} {f : RdM α} {g : RL α} {k : α → RdM β} {h : α → RL β}
    (hf : Corr f g) (hk : ∀ a, Corr (k a) (h a)) : Corr (f >>= k) (rlBind g h) := by
  intro A p
  obtain ⟨q, e1, e2⟩ := hf A p
  obtain ⟨q', e3, e4⟩ := hk (g (A.toList.drop p)).1 A q
  have eb : (f >>= k).run ⟨A, p⟩ = (k (f.run ⟨A, p⟩).1).run (f.run ⟨A, p⟩).2 := rfl
  have er : rlBind g h (A.toList.drop p) =
      h (g (A.toList.drop p)).1 (g (A.toList.drop p)).2 := rfl
  refine ⟨q', ?_, ?_⟩
  · rw [eb, e1, er, e2]
    exact e3
  · rw [er, e2]
    exact e4

theorem corr_nat : Corr rdNat rlNat :=
  corr_congr (corr_bind corr_int fun x => corr_pure x.toNat) fun _ => rfl

abbrev pushBody {α : Type} (f : RdM α) : ℕ → Array α → RdM (ForInStep (Array α)) :=
  fun _ r => do
    let x ← f
    pure (ForInStep.yield (r.push x))

theorem corr_forIn {α : Type} {f : RdM α} {g : RL α} (hf : Corr f g) :
    ∀ (L : List ℕ) (acc : Array α), Corr (forIn L acc (pushBody f))
      (fun l => (acc ++ (rlRep g L.length l).1.toArray, (rlRep g L.length l).2))
  | [], acc => by
    intro A p
    refine ⟨p, ?_, rfl⟩
    have e : (forIn ([] : List ℕ) acc (pushBody f)).run ⟨A, p⟩ = (acc, (⟨A, p⟩ : Rd)) := rfl
    rw [e]
    simp [rlRep]
  | i :: L, acc => by
    intro A p
    obtain ⟨q, e1, e2⟩ := hf A p
    obtain ⟨q', e3, e4⟩ := corr_forIn hf L (acc.push (g (A.toList.drop p)).1) A q
    have eb : (forIn (i :: L) acc (pushBody f)).run ⟨A, p⟩ =
        (forIn L (acc.push (f.run ⟨A, p⟩).1) (pushBody f)).run (f.run ⟨A, p⟩).2 := by
      rw [List.forIn_cons]
      rfl
    have er : rlRep g (i :: L).length (A.toList.drop p) =
        ((g (A.toList.drop p)).1 :: (rlRep g L.length (g (A.toList.drop p)).2).1,
          (rlRep g L.length (g (A.toList.drop p)).2).2) := rfl
    beta_reduce at e3 e4 ⊢
    refine ⟨q', ?_, ?_⟩
    · rw [eb, e1, e3, er, e2]
      simp
    · rw [er, e2]
      exact e4

theorem range_size (m : ℕ) : ([:m] : Std.Legacy.Range).size = m := by
  simp [Std.Legacy.Range.size]

theorem rdList_eq {α : Type} (f : RdM α) : rdList f = (rdNat >>= fun len =>
    forIn (List.range' 0 len) #[] (pushBody f) >>= fun out => pure out.toList) := by
  unfold rdList
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size]

theorem rdArr_eq {α : Type} (f : RdM α) : rdArr f = (rdNat >>= fun len =>
    forIn (List.range' 0 len) #[] (pushBody f) >>= fun out => pure out) := by
  unfold rdArr
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size]

theorem rdPerm_eq (n : ℕ) : rdPerm n =
    (forIn (List.range' 0 n) (Array.mkEmpty n) (pushBody rdNat) >>= fun out => pure out) := by
  unfold rdPerm
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size]

theorem corr_list {α : Type} {f : RdM α} {g : RL α} (hf : Corr f g) : Corr (rdList f) (rlList g) := by
  rw [rdList_eq]
  refine corr_congr (corr_bind corr_nat fun len =>
    corr_bind (corr_forIn hf (List.range' 0 len) #[]) fun (out : Array α) => corr_pure out.toList)
    fun l => ?_
  simp [rlList, rlBind, rlNat, List.length_range']

theorem corr_arr {α : Type} {f : RdM α} {g : RL α} (hf : Corr f g) : Corr (rdArr f) (rlArr g) := by
  rw [rdArr_eq]
  refine corr_congr (corr_bind corr_nat fun len =>
    corr_bind (corr_forIn hf (List.range' 0 len) #[]) fun (out : Array α) => corr_pure out)
    fun l => ?_
  simp [rlArr, rlList, rlBind, rlNat, List.length_range']

theorem corr_perm (n : ℕ) : Corr (rdPerm n) (rlPerm n) := by
  rw [rdPerm_eq]
  refine corr_congr (corr_bind (corr_forIn corr_nat (List.range' 0 n) (Array.mkEmpty n)) fun out =>
    corr_pure out) fun l => ?_
  simp [rlPerm, rlBind, List.length_range', Array.mkEmpty]

theorem corr_word : Corr rdWord rlWord := corr_list corr_int

theorem corr_words : Corr rdWords rlWords := corr_list corr_word

theorem corr_chain (n : ℕ) : Corr (rdChain n) (rlChain n) :=
  corr_bind (corr_arr (corr_perm n)) fun S => corr_bind corr_nat fun k =>
    corr_bind (corr_list corr_nat) fun base => corr_bind (corr_arr corr_word) fun W =>
      corr_bind corr_nat fun chunks => corr_pure _

theorem corr_ctx (n : ℕ) : Corr (rdCtx n) (rlCtx n) :=
  corr_bind (corr_chain n) fun chP => corr_bind (corr_chain n) fun chN =>
    corr_bind corr_words fun normW => corr_bind corr_words fun transW =>
      corr_bind (corr_list corr_nat) fun stabLetters => corr_pure _

theorem corr_pair {α β : Type} {f : RdM α} {g : RL α} {f' : RdM β} {g' : RL β} (hf : Corr f g)
    (hf' : Corr f' g') : Corr (do let a ← f; let b ← f'; return (a, b)) (rlPair g g') :=
  corr_bind hf fun a => corr_bind hf' fun b => corr_pure (a, b)

theorem corr_cover : Corr rdCover rlCover :=
  corr_bind corr_words fun ws => corr_bind (corr_list (corr_pair corr_nat corr_word)) fun cj =>
    corr_pure _

theorem corr_gen : Corr rdGen rlGen :=
  corr_bind corr_words fun Aw => corr_bind (corr_list corr_nat) fun ka =>
    corr_bind corr_words fun Bw => corr_bind (corr_list corr_nat) fun kb =>
      corr_bind corr_words fun pw => corr_pure _

theorem corr_rep (n : ℕ) : Corr (rdRep n) (rlRepC n) :=
  corr_bind corr_word fun nuW => corr_bind (corr_chain n) fun chC =>
  corr_bind corr_words fun cgW => corr_bind (corr_list (corr_pair corr_nat corr_int)) fun par =>
  corr_bind (corr_list corr_nat) fun ord => corr_bind (corr_chain n) fun chX =>
  corr_bind corr_words fun xgW => corr_bind (corr_list corr_words) fun xnorm =>
  corr_bind (corr_list corr_words) fun xcomm => corr_bind (corr_chain n) fun chT =>
  corr_bind corr_words fun tgW => corr_bind corr_nat fun sylA => corr_bind corr_nat fun sylM =>
  corr_bind corr_cover fun tel => corr_bind corr_words fun epsW =>
  corr_bind (corr_list corr_gen) fun gens => corr_pure _

theorem corr_fc (n : ℕ) : Corr (rdFC n) (rlFC n) :=
  corr_bind (corr_ctx n) fun ctx => corr_bind (corr_chain n) fun chTN =>
  corr_bind corr_words fun tnW => corr_bind corr_nat fun sylA => corr_bind corr_nat fun sylM =>
  corr_bind corr_cover fun tel => corr_bind (corr_list (corr_rep n)) fun reps => corr_pure _

theorem parseFC_eq (n : ℕ) {cs : List Char} (h : intsOK cs = true) :
    parseFC n (String.ofList cs) = parseFCL n (intsL cs) := by
  unfold parseFC parseFCL
  rw [fcTokens_ofList h]
  obtain ⟨q, e, -⟩ := corr_fc n (intsL cs).toArray 0
  have e' : (rdFC n).run' ⟨(intsL cs).toArray, 0⟩ = ((rdFC n).run ⟨(intsL cs).toArray, 0⟩).1 := rfl
  rw [e', e]
  simp

end CFSG.KC.ExactGen

end
