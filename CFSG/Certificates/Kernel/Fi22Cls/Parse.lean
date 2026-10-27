module

public import Certificates.Data.Kernel.Fi22Cls.Words
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
public import CFSG.Certificates.Kernel.Fi22S0.Parse

public section

namespace CFSG.KS.Fi22ClsParse

open CFSG.KD.LyS0 CFSG.KC.Fi22Cls CFSG.KS.LyS0Parse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native (labRep labCls conjW splitWords
  labRepStr labClsStr conjStr)

@[expose] def wlist (wo wd : Nat → Nat) (c : Nat) : List Nat :=
  (List.range' (wo c) (wo (c + 1) - wo c)).map wd

@[expose] def blocks (wo wd : Nat → Nat) (c m : Nat) : List Nat :=
  (List.range' c m).flatMap fun c' => (wo (c' + 1) - wo c') :: wlist wo wd c'

theorem blocks_succ (wo wd : Nat → Nat) (c m : Nat) :
    blocks wo wd c (m + 1) = ((wo (c + 1) - wo c) :: wlist wo wd c) ++ blocks wo wd (c + 1) m := by
  unfold blocks
  rw [List.range'_succ, List.flatMap_cons]

variable {wo wd : Nat → Nat} {nl : Nat}

theorem blocks_length : ∀ c m, m ≤ (blocks wo wd c m).length
  | _, 0 => Nat.zero_le _
  | c, m + 1 => by
    rw [blocks_succ, List.length_append, List.length_cons]
    have := blocks_length (c + 1) m
    omega

theorem wordsT_nil (c i : Nat) :
    wordsT wo wd nl [] c i = bAnd(Nat.beq c nl, Nat.beq i (wo nl)) := rfl

theorem wordsT_cons (x : Nat) (xs : List Nat) (c i : Nat) :
    wordsT wo wd nl (x :: xs) c i = bIf(Nat.blt i (wo c),
      bAnd(Nat.beq x (wd i), wordsT wo wd nl xs c (Nat.succ i)),
      bAnd(Nat.blt c nl, bAnd(Nat.beq i (wo c),
        bAnd(Nat.beq x (Nat.sub (wo (Nat.succ c)) (wo c)), wordsT wo wd nl xs (Nat.succ c) i)))) :=
  rfl

theorem wordsT_spec : ∀ (xs : List Nat) (c i : Nat), wordsT wo wd nl xs c i = true →
    c ≤ nl ∧ xs = (List.range' i (wo c - i)).map wd ++ blocks wo wd c (nl - c)
  | [], c, i, h => by
    rw [wordsT_nil] at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    have e1 := Nat.eq_of_beq_eq_true h1
    have e2 := Nat.eq_of_beq_eq_true h2
    subst e1 e2
    refine ⟨Nat.le_refl _, ?_⟩
    simp [blocks]
  | x :: xs, c, i, h => by
    rw [wordsT_cons] at h
    cases hb : Nat.blt i (wo c)
    · rw [hb] at h
      obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
      obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
      obtain ⟨h5, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h4
      have hc : c < nl := by rw [← Nat.blt_eq]; exact h1
      have hi : i = wo c := Nat.eq_of_beq_eq_true h3
      have hx : x = wo (c + 1) - wo c := Nat.eq_of_beq_eq_true h5
      obtain ⟨-, ih⟩ := wordsT_spec xs (c + 1) i h6
      refine ⟨Nat.le_of_lt hc, ?_⟩
      have hm : nl - c = (nl - (c + 1)) + 1 := by omega
      rw [ih, hm, blocks_succ, hi, Nat.sub_self, List.range'_zero, List.map_nil, List.nil_append,
        hx]
      rfl
    · rw [hb] at h
      obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
      have hi : i < wo c := by rw [← Nat.blt_eq]; exact hb
      have hx : x = wd i := Nat.eq_of_beq_eq_true h1
      obtain ⟨hc, ih⟩ := wordsT_spec xs c (i + 1) h2
      refine ⟨hc, ?_⟩
      have hm : wo c - i = (wo c - (i + 1)) + 1 := by omega
      rw [ih, hm, List.range'_succ, List.map_cons, List.cons_append, hx]

theorem getElem!_mid {pre rest : List Nat} {y : Nat} {p : Nat} (hp : pre.length = p) :
    (pre ++ y :: rest).toArray[p]! = y := by
  rw [List.getElem!_toArray, getElem!_pos _ p (by (try simp) <;> omega), List.getElem_append_right
    (by omega)]
  simp [hp]

theorem getElem!_mid' {pre w rest : List Nat} {p t : Nat} (hp : pre.length = p) (ht : t < w.length) :
    (pre ++ (w ++ rest)).toArray[p + t]! = w[t] := by
  rw [List.getElem!_toArray, getElem!_pos _ (p + t) (by (try simp) <;> omega), List.getElem_append_right
    (by omega), List.getElem_append_left (by (try simp) <;> omega)]
  congr 1
  omega

theorem splitWords_spec (L : List Nat) : ∀ (m c : Nat) (pre : List Nat) (f : Nat) (acc : Array (List Nat)),
    L = pre ++ blocks wo wd c m → m ≤ f →
      splitWords L.toArray f pre.length acc = acc ++ ((List.range' c m).map (wlist wo wd)).toArray
  | 0, c, pre, f, acc, hL, _ => by
    have hs : L.toArray.size = pre.length := by
      rw [List.size_toArray, hL]
      simp [blocks]
    cases f with
    | zero => simp [splitWords]
    | succ f =>
      rw [splitWords]
      simp [hs]
  | m + 1, c, pre, f, acc, hL, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [blocks_succ] at hL
    have hlen : (wlist wo wd c).length = wo (c + 1) - wo c := by simp [wlist]
    have hL' : L = (pre ++ ((wo (c + 1) - wo c) :: wlist wo wd c)) ++ blocks wo wd (c + 1) m := by
      rw [hL, List.append_assoc]
    have hlt : pre.length < L.toArray.size := by
      rw [List.size_toArray, hL]
      simp
    have ha : L.toArray[pre.length]! = wo (c + 1) - wo c := by
      rw [hL, List.cons_append]
      exact getElem!_mid rfl
    have hw : ((List.range (wo (c + 1) - wo c)).map fun t => L.toArray[pre.length + 1 + t]!) =
        wlist wo wd c := by
      apply List.ext_getElem (by simp [hlen])
      intro t h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have ht : t < (wlist wo wd c).length := h2
      have e : pre.length + 1 + t = (pre ++ [wo (c + 1) - wo c]).length + t := by (try simp) <;> omega
      rw [e, hL, List.cons_append, ← List.singleton_append, ← List.append_assoc]
      exact getElem!_mid' rfl ht
    rw [splitWords]
    simp only [hlt, ↓reduceIte]
    rw [ha, hw]
    have hp : pre.length + 1 + (wo (c + 1) - wo c) =
        (pre ++ ((wo (c + 1) - wo c) :: wlist wo wd c)).length := by simp [hlen]; omega
    rw [hp, splitWords_spec L m (c + 1) _ f _ hL' (by omega), List.range'_succ, List.map_cons]
    apply Array.toList_inj.1
    simp

theorem arr_of {f : Nat → Nat} {cs : List Char} {n : Nat} {s : String} (hc : s = String.ofList cs)
    (h : parseOK f cs n = true) :
    CFSG.Sporadic.Fi22.S0.parseNats s = Array.ofFn (n := n) fun i => f i.val := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Fi22S0Parse.parseNats_of h
  rw [hc]
  apply Array.ext (by rw [h1, Array.size_ofFn])
  intro i hi1 hi2
  rw [Array.getElem_ofFn, ← h2 i (by rw [← h1]; exact hi1), getElem!_pos _ i hi1]

theorem labRep_of {f : Nat → Nat} {cs : List Char} (hc : labRepStr = String.ofList cs)
    (h : parseOK f cs 126 = true) : labRep () = Array.ofFn (n := 126) fun i => f i.val :=
  arr_of hc h

theorem labCls_of {f : Nat → Nat} {cs : List Char} (hc : labClsStr = String.ofList cs)
    (h : parseOK f cs 126 = true) : labCls () = Array.ofFn (n := 126) fun i => f i.val :=
  arr_of hc h

theorem conjW_of {cs : List Char} (hc : conjStr = String.ofList cs) (h : wordsOK wo wd nl cs = true) :
    conjW () = ((List.range' 0 nl).map (wlist wo wd)).toArray := by
  unfold wordsOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, e⟩ := wordsT_spec (natsL cs) 0 (wo 0) h2
  rw [Nat.sub_self, List.range'_zero, List.map_nil, List.nil_append, Nat.sub_zero] at e
  have hp : CFSG.Sporadic.Fi22.S0.parseNats conjStr = (natsL cs).toArray := by
    rw [hc]
    exact parse_ofList h1
  have hcw : conjW () = splitWords (CFSG.Sporadic.Fi22.S0.parseNats conjStr)
      (CFSG.Sporadic.Fi22.S0.parseNats conjStr).size 0 #[] := rfl
  rw [hcw, hp]
  have hs := splitWords_spec (wo := wo) (wd := wd) (natsL cs) nl 0 [] (natsL cs).toArray.size #[]
    (by rw [e]; rfl) (by rw [List.size_toArray, e]; exact blocks_length 0 nl)
  rw [List.length_nil] at hs
  rw [hs, Array.empty_append]

end CFSG.KS.Fi22ClsParse

end
