module

public import CFSG.Certificates.Kernel.Spor.PK.Str
public import CFSG.Certificates.Kernel.Spor.PK.MiscBase
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

namespace CFSG.KS.PK

open CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.YGroups.ModelNative

@[expose] def lineVal (w : Nat) (l : List Nat) : Nat :=
  l.length + 2 ^ 16 * enc w (fun i => l.getD i 0) l.length

theorem fmtK_iff (cs : List Nat) :
    CFSG.KC.Misc.O73.fmtK cs = true ↔ ∀ c ∈ cs, c = 32 ∨ c = 10 ∨ (48 ≤ c ∧ c ≤ 57) := by
  unfold CFSG.KC.Misc.O73.fmtK
  rw [allL_lqt_iff]
  refine forall₂_congr fun c _ => ?_
  simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]

private noncomputable def pkR (w : Nat) (cs : List Nat) : Nat → Nat → Nat → Bool → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool → List Nat)
    (fun cur cnt acc ne => Bool.rec (motive := fun _ => List Nat) List.nil
      [parseK.fin w cur cnt acc] ne)
    (fun c _ ih cur cnt acc ne => Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat)
        (ih (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))) cnt acc true)
        (Bool.rec (motive := fun _ => List Nat)
          (ih 0 (Nat.succ cnt) (Nat.lor acc (Nat.shiftLeft (Nat.pred cur) (Nat.mul w cnt))) true)
          (ih 0 cnt acc true) (Nat.beq cur 0))
        (Nat.beq c 32))
      (Bool.rec (motive := fun _ => List Nat) (ih 0 0 0 false)
        (List.cons (parseK.fin w cur cnt acc) (ih 0 0 0 false)) ne)
      (Nat.beq c 10)) cs

private noncomputable def tkR (B : Nat) (cs : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun cur => Nat.ble cur B)
    (fun c _ ih cur => Bool.rec (motive := fun _ => Bool)
      (ih (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))))
      (CFSG.KC.Ord.andB (Nat.ble cur B) (ih 0))
      (CFSG.KC.Ord.orB (Nat.beq c 32) (Nat.beq c 10))) cs

private theorem parseK_eq_pkR (w : Nat) (cs : List Nat) :
    parseK w cs = pkR w cs 0 0 0 false := rfl

private theorem beq_false_of_ne' {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')

private theorem pkR_nil (w cur cnt acc : Nat) (ne : Bool) :
    pkR w [] cur cnt acc ne = if ne = true then [parseK.fin w cur cnt acc] else [] := by
  cases ne <;> rfl

private theorem pkR_newline (w : Nat) (cs : List Nat) (cur cnt acc : Nat) (ne : Bool) :
    pkR w (10 :: cs) cur cnt acc ne =
      (if ne = true then [parseK.fin w cur cnt acc] else []) ++ pkR w cs 0 0 0 false := by
  cases ne <;> rfl

private theorem pkR_space (w : Nat) (cs : List Nat) (cur cnt acc : Nat) (ne : Bool) :
    pkR w (32 :: cs) cur cnt acc ne =
      if cur = 0 then pkR w cs 0 cnt acc true
      else pkR w cs 0 (cnt + 1) (acc ||| (cur - 1) <<< (w * cnt)) true := by
  cases cur <;> rfl

private theorem pkR_digit {c : Nat} (hc10 : c ≠ 10) (hc32 : c ≠ 32) (w : Nat) (cs : List Nat)
    (cur cnt acc : Nat) (ne : Bool) :
    pkR w (c :: cs) cur cnt acc ne = pkR w cs (10 * (cur - 1) + (c - 48) + 1) cnt acc true := by
  unfold pkR
  dsimp only
  rw [beq_false_of_ne' hc10, beq_false_of_ne' hc32]
  rfl

private theorem tkR_sep {c : Nat} (hc : c = 32 ∨ c = 10) (B : Nat) (cs : List Nat) (cur : Nat) :
    tkR B (c :: cs) cur = (Nat.ble cur B && tkR B cs 0) := by
  rcases hc with rfl | rfl <;> exact andB_eq _ _

private theorem tkR_digit {c : Nat} (hc10 : c ≠ 10) (hc32 : c ≠ 32) (B : Nat) (cs : List Nat)
    (cur : Nat) : tkR B (c :: cs) cur = tkR B cs (10 * (cur - 1) + (c - 48) + 1) := by
  unfold tkR
  dsimp only
  rw [beq_false_of_ne' hc10, beq_false_of_ne' hc32]
  rfl

private def encL (w : Nat) (T : List Nat) : Nat := enc w (fun i => T.getD i 0) T.length

private theorem lineVal_eq (w : Nat) (l : List Nat) :
    lineVal w l = l.length + 2 ^ 16 * encL w l := rfl

private theorem encL_nil (w : Nat) : encL w [] = 0 := rfl

private theorem encL_append_singleton (w : Nat) (T : List Nat) (v : Nat) :
    encL w (T ++ [v]) = encL w T + v * 2 ^ (w * T.length) := by
  unfold encL
  rw [List.length_append, List.length_singleton, enc_succ]
  congr 1
  · exact enc_congr fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · simp [List.getD_eq_getElem?_getD]

private theorem encL_lt (w : Nat) (T : List Nat) (hT : ∀ t ∈ T, t < 2 ^ w) :
    encL w T < 2 ^ (w * T.length) := by
  unfold encL
  apply enc_lt
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hT _ (List.getElem_mem hi)

private def curOf (d : List Nat) : Nat := if d = [] then 0 else decVal d + 1

private theorem curOf_nil : curOf [] = 0 := rfl

private theorem curOf_append_digit (d : List Nat) (c : Nat) :
    curOf (d ++ [c]) = 10 * (curOf d - 1) + (c - 48) + 1 := by
  by_cases h : d = []
  · subst h; simp [curOf, decVal]
  · simp [curOf, h, decVal, List.foldl_append]

private def tkv (l : List Nat) : List Nat :=
  ((l.splitOn 32).filter fun t => !t.isEmpty).map decVal

private theorem tkv_nil : tkv [] = [] := by
  simp [tkv]

private theorem tkv_digits {d : List Nat} (hd : ∀ c ∈ d, 48 ≤ c ∧ c ≤ 57) :
    tkv d = if d = [] then [] else [decVal d] := by
  have h32 : (32 : Nat) ∉ d := fun h => by have := hd 32 h; omega
  unfold tkv
  rw [List.splitOn_eq_singleton h32]
  by_cases h : d = [] <;> simp [h]

private theorem tkv_append_space (a l : List Nat) : tkv (a ++ 32 :: l) = tkv a ++ tkv l := by
  unfold tkv
  rw [List.splitOn_append_cons_self, List.filter_append, List.map_append]

private def lnsV (w : Nat) (ls : List (List Nat)) : List Nat :=
  (ls.filter fun l => !l.isEmpty).map fun l => lineVal w (tkv l)

private theorem lnsV_cons (w : Nat) (l : List Nat) (ls : List (List Nat)) :
    lnsV w (l :: ls) = (if (!l.isEmpty) = true then [lineVal w (tkv l)] else []) ++ lnsV w ls := by
  unfold lnsV
  rw [List.filter_cons]
  by_cases h : (!l.isEmpty) = true <;> simp [h]

private theorem fin_eq (w : Nat) {T d : List Nat} (hT : ∀ t ∈ T, t < 2 ^ w)
    (hd : ∀ c ∈ d, 48 ≤ c ∧ c ≤ 57) :
    parseK.fin w (curOf d) T.length (encL w T) = lineVal w (T ++ tkv d) := by
  rw [tkv_digits hd]
  by_cases h : d = []
  · subst h
    simp only [curOf_nil, if_true, List.append_nil]
    show T.length + (encL w T <<< 16) = _
    rw [lineVal_eq, Nat.shiftLeft_eq, Nat.mul_comm]
  · have hc : curOf d = decVal d + 1 := by simp [curOf, h]
    rw [hc, if_neg h]
    show (T.length + 1) + ((encL w T ||| (decVal d <<< (w * T.length))) <<< 16) = _
    rw [lor_shiftLeft_eq_add (encL_lt w T hT), Nat.shiftLeft_eq, lineVal_eq, encL_append_singleton]
    simp [Nat.mul_comm]

private theorem splitOn_cons_self (cs : List Nat) :
    (10 :: cs).splitOn 10 = [] :: cs.splitOn 10 := by
  simp [List.splitOn_cons_eq_ite_modifyHead]

private theorem splitOn_cons_ne {c : Nat} (hc : c ≠ 10) {cs f : List Nat} {r : List (List Nat)}
    (h : cs.splitOn 10 = f :: r) : (c :: cs).splitOn 10 = (c :: f) :: r := by
  rw [List.splitOn_cons_eq_ite_modifyHead, if_neg (by simpa using hc), h]
  rfl

private theorem pkR_main (w : Nat) : ∀ (cs d T : List Nat) (ne : Bool) (first : List Nat)
    (rest : List (List Nat)), cs.splitOn 10 = first :: rest →
    (∀ c ∈ cs, c = 32 ∨ c = 10 ∨ (48 ≤ c ∧ c ≤ 57)) →
    (∀ c ∈ d, 48 ≤ c ∧ c ≤ 57) → (∀ t ∈ T, t < 2 ^ w) →
    tkR (2 ^ w) cs (curOf d) = true →
    pkR w cs (curOf d) T.length (encL w T) ne =
      (if (ne || !first.isEmpty) = true then [lineVal w (T ++ tkv (d ++ first))] else []) ++
        lnsV w rest := by
  intro cs
  induction cs with
  | nil =>
    intro d T ne first rest hs _ hd hT _
    rw [List.splitOn_nil] at hs
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    rw [pkR_nil, fin_eq w hT hd]
    cases ne <;> simp [lnsV]
  | cons c cs ih =>
    intro d T ne first rest hs hf hd hT ht
    have hc := hf c List.mem_cons_self
    have hf' : ∀ x ∈ cs, x = 32 ∨ x = 10 ∨ (48 ≤ x ∧ x ≤ 57) :=
      fun x hx => hf x (List.mem_cons_of_mem _ hx)
    obtain ⟨f', r', hs'⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil 10 cs)
    by_cases h10 : c = 10
    · subst h10
      rw [splitOn_cons_self, hs'] at hs
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs
      rw [tkR_sep (Or.inr rfl)] at ht
      have ht' := (Bool.and_eq_true_iff.1 ht).2
      have key := ih [] [] false f' r' hs' hf' (by simp) (by simp) ht'
      rw [curOf_nil, List.length_nil, encL_nil] at key
      rw [pkR_newline, key, fin_eq w hT hd]
      cases ne <;> simp [lnsV_cons]
    · by_cases h32 : c = 32
      · subst h32
        rw [splitOn_cons_ne (by omega) hs'] at hs
        obtain ⟨rfl, rfl⟩ := List.cons.inj hs
        rw [tkR_sep (Or.inl rfl)] at ht
        obtain ⟨ht1, ht2⟩ := Bool.and_eq_true_iff.1 ht
        rw [pkR_space]
        by_cases hd0 : d = []
        · subst hd0
          rw [curOf_nil, if_pos rfl]
          have key := ih [] T true f' r' hs' hf' (by simp) hT ht2
          rw [curOf_nil] at key
          rw [key, tkv_append_space, tkv_nil]
          simp
        · have hcur : curOf d = decVal d + 1 := by simp [curOf, hd0]
          have hv : decVal d < 2 ^ w := by
            rw [hcur] at ht1
            have := Nat.le_of_ble_eq_true ht1
            omega
          have hT' : ∀ t ∈ T ++ [decVal d], t < 2 ^ w := by
            intro t ht
            rcases List.mem_append.1 ht with h | h
            · exact hT t h
            · rw [List.mem_singleton.1 h]; exact hv
          have key := ih [] (T ++ [decVal d]) true f' r' hs' hf' (by simp) hT' ht2
          rw [curOf_nil, encL_append_singleton, List.length_append, List.length_singleton] at key
          have e : encL w T ||| (curOf d - 1) <<< (w * T.length) =
              encL w T + decVal d * 2 ^ (w * T.length) := by
            rw [hcur, Nat.add_sub_cancel]
            exact lor_shiftLeft_eq_add (encL_lt w T hT)
          rw [if_neg (by rw [hcur]; omega), e, key]
          simp [tkv_append_space, tkv_digits hd, hd0, List.append_assoc]
      · have hdig : 48 ≤ c ∧ c ≤ 57 := by omega
        rw [splitOn_cons_ne h10 hs'] at hs
        obtain ⟨rfl, rfl⟩ := List.cons.inj hs
        rw [tkR_digit h10 h32, ← curOf_append_digit] at ht
        rw [pkR_digit h10 h32, ← curOf_append_digit]
        have hd' : ∀ x ∈ d ++ [c], 48 ≤ x ∧ x ≤ 57 := by
          intro x hx
          rcases List.mem_append.1 hx with h | h
          · exact hd x h
          · rw [List.mem_singleton.1 h]; exact hdig
        have key := ih (d ++ [c]) T true f' r' hs' hf' hd' hT ht
        rw [key]
        simp [List.append_assoc]

private theorem parseK_eq_lns {w : Nat} {cs : List Nat} (hf : CFSG.KC.Misc.O73.fmtK cs = true)
    (ht : tokLt (2 ^ w) cs = true) : parseK w cs = lnsV w (cs.splitOn 10) := by
  obtain ⟨f, r, hs⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil 10 cs)
  have key := pkR_main w cs [] [] false f r hs ((fmtK_iff cs).1 hf) (by simp) (by simp) ht
  rw [curOf_nil, List.length_nil, encL_nil] at key
  rw [parseK_eq_pkR, key, hs, lnsV_cons]
  simp

private theorem mem_splitOn_spec (a : Nat) :
    ∀ (cs t : List Nat), t ∈ cs.splitOn a → t.Sublist cs ∧ a ∉ t
  | [], t, h => by
    rw [List.splitOn_nil, List.mem_singleton] at h
    subst h
    simp
  | x :: xs, t, h => by
    obtain ⟨f, r, hs⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil a xs)
    rw [List.splitOn_cons_eq_ite_modifyHead] at h
    by_cases hx : (x == a) = true
    · rw [if_pos hx] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact ⟨List.nil_sublist _, by simp⟩
      · obtain ⟨h1, h2⟩ := mem_splitOn_spec a xs t h'
        exact ⟨h1.cons x, h2⟩
    · rw [if_neg hx, hs] at h
      have hmem : ∀ u ∈ f :: r, u.Sublist xs ∧ a ∉ u :=
        fun u hu => mem_splitOn_spec a xs u (hs ▸ hu)
      simp only [List.modifyHead, List.mem_cons] at h
      rcases h with rfl | h'
      · obtain ⟨h1, h2⟩ := hmem f List.mem_cons_self
        refine ⟨h1.cons₂ x, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hx (by simp [h]), h2⟩
      · obtain ⟨h1, h2⟩ := hmem t (List.mem_cons_of_mem _ h')
        exact ⟨h1.cons x, h2⟩

private theorem length_filter_splitOn_le (a : Nat) : ∀ l : List Nat,
    ((l.splitOn a).filter fun t => !t.isEmpty).length ≤ l.length
  | [] => by simp
  | x :: xs => by
    have ih := length_filter_splitOn_le a xs
    obtain ⟨f, r, hs⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil a xs)
    rw [List.splitOn_cons_eq_ite_modifyHead]
    by_cases hx : (x == a) = true
    · rw [if_pos hx]
      simp only [List.filter_cons, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]
      omega
    · rw [if_neg hx, hs]
      rw [hs] at ih
      have h1 : (r.filter fun t => !t.isEmpty).length ≤
          ((f :: r).filter fun t => !t.isEmpty).length := by
        rw [List.filter_cons]
        split <;> simp
      simp only [List.modifyHead, List.filter_cons, List.isEmpty_cons, Bool.not_false,
        ↓reduceIte, List.length_cons] at ih h1 ⊢
      omega

private theorem lt128 {cs : List Nat} (hf : CFSG.KC.Misc.O73.fmtK cs = true) :
    ∀ c ∈ cs, c < 128 := by
  intro c hc
  have := (fmtK_iff cs).1 hf c hc
  omega

private theorem textLines_strL {cs : List Nat} (hl : ∀ c ∈ cs, c < 128) :
    textLines (strL cs) = ((cs.splitOn 10).filter fun l => !l.isEmpty).map strL := by
  unfold textLines
  rw [splitOn_newline_strL hl, List.filter_map]
  congr 1
  apply List.filter_congr
  intro l _
  simp [isEmpty_strL]

private theorem foldl_parse : ∀ (ts : List (List Nat)), (∀ t ∈ ts, t ≠ [] → IsDigits t) →
    ∀ (a : Array Nat), ((ts.map strL).foldl
        (fun a t => if t.isEmpty then a else a.push t.toNat!) a).toList
      = a.toList ++ ((ts.filter fun t => !t.isEmpty).map decVal)
  | [], _, a => by simp
  | t :: ts, hts, a => by
    have ih := foldl_parse ts (fun u hu => hts u (List.mem_cons_of_mem _ hu))
    by_cases ht : t = []
    · subst ht
      simp only [List.map_cons, List.foldl_cons, isEmpty_strL, List.isEmpty_nil, if_true,
        List.filter_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih a
    · have hd := hts t List.mem_cons_self ht
      have hne : t.isEmpty = false := by simpa using ht
      simp only [List.map_cons, List.foldl_cons, isEmpty_strL, hne, Bool.false_eq_true, ↓reduceIte,
        List.filter_cons, Bool.not_false, toNat!_strL hd]
      rw [ih, Array.toList_push, List.append_assoc]
      rfl

private theorem parseNats_strL {l : List Nat} (hl : ∀ c ∈ l, c = 32 ∨ (48 ≤ c ∧ c ≤ 57)) :
    (parseNats (strL l)).toList = tkv l := by
  have hl128 : ∀ c ∈ l, c < 128 := fun c hc => by have := hl c hc; omega
  unfold parseNats
  rw [splitOn_space_strL hl128, foldl_parse (l.splitOn 32) ?_ #[]]
  · simp [tkv]
  · intro t ht hne
    obtain ⟨hsub, h32⟩ := mem_splitOn_spec 32 l t ht
    refine ⟨hne, fun c hc => ?_⟩
    rcases hl c (hsub.subset hc) with rfl | h
    · exact absurd hc h32
    · exact h

private theorem line_digits {cs : List Nat} (hf : CFSG.KC.Misc.O73.fmtK cs = true) {l : List Nat}
    (hl : l ∈ cs.splitOn 10) : l.Sublist cs ∧ ∀ c ∈ l, c = 32 ∨ (48 ≤ c ∧ c ≤ 57) := by
  obtain ⟨hsub, h10⟩ := mem_splitOn_spec 10 cs l hl
  refine ⟨hsub, fun c hc => ?_⟩
  rcases (fmtK_iff cs).1 hf c (hsub.subset hc) with h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hc) h10
  · exact Or.inr h

theorem parseK_eq {w : Nat} {cs : List Nat} (hf : CFSG.KC.Misc.O73.fmtK cs = true)
    (ht : tokLt (2 ^ w) cs = true) :
    parseK w cs = (textLines (strL cs)).map fun line => lineVal w (parseNats line).toList := by
  rw [parseK_eq_lns hf ht, textLines_strL (lt128 hf), List.map_map]
  unfold lnsV
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply]
  rw [parseNats_strL (line_digits hf (List.mem_filter.1 hl).1).2]

theorem length_parseNats_le {cs : List Nat} (hf : CFSG.KC.Misc.O73.fmtK cs = true) :
    ∀ line ∈ textLines (strL cs), (parseNats line).size ≤ cs.length := by
  intro line hline
  rw [textLines_strL (lt128 hf)] at hline
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hline
  obtain ⟨hsub, hdig⟩ := line_digits hf (List.mem_filter.1 hl).1
  rw [← Array.length_toList, parseNats_strL hdig, tkv, List.length_map]
  exact Nat.le_trans (length_filter_splitOn_le 32 l) hsub.length_le

private theorem tkv_lt_of_ble {B : Nat} {d : List Nat} (hd : ∀ c ∈ d, 48 ≤ c ∧ c ≤ 57)
    (h : Nat.ble (curOf d) B = true) : ∀ x ∈ tkv d, x < B := by
  intro x hx
  rw [tkv_digits hd] at hx
  by_cases hd0 : d = []
  · simp [hd0] at hx
  · rw [if_neg hd0, List.mem_singleton] at hx
    subst hx
    have hcur : curOf d = decVal d + 1 := by simp [curOf, hd0]
    rw [hcur] at h
    have := Nat.le_of_ble_eq_true h
    omega

private theorem tkR_main (B : Nat) : ∀ (cs d first : List Nat) (rest : List (List Nat)),
    cs.splitOn 10 = first :: rest →
    (∀ c ∈ cs, c = 32 ∨ c = 10 ∨ (48 ≤ c ∧ c ≤ 57)) →
    (∀ c ∈ d, 48 ≤ c ∧ c ≤ 57) →
    tkR B cs (curOf d) = true →
    (∀ x ∈ tkv (d ++ first), x < B) ∧ ∀ l ∈ rest, ∀ x ∈ tkv l, x < B := by
  intro cs
  induction cs with
  | nil =>
    intro d first rest hs _ hd ht
    rw [List.splitOn_nil] at hs
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    refine ⟨?_, by simp⟩
    rw [List.append_nil]
    exact tkv_lt_of_ble hd ht
  | cons c cs ih =>
    intro d first rest hs hf hd ht
    have hc := hf c List.mem_cons_self
    have hf' : ∀ x ∈ cs, x = 32 ∨ x = 10 ∨ (48 ≤ x ∧ x ≤ 57) :=
      fun x hx => hf x (List.mem_cons_of_mem _ hx)
    obtain ⟨f', r', hs'⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil 10 cs)
    by_cases h10 : c = 10
    · subst h10
      rw [splitOn_cons_self, hs'] at hs
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs
      rw [tkR_sep (Or.inr rfl)] at ht
      obtain ⟨ht1, ht2⟩ := Bool.and_eq_true_iff.1 ht
      have key := ih [] f' r' hs' hf' (by simp) ht2
      refine ⟨?_, ?_⟩
      · rw [List.append_nil]
        exact tkv_lt_of_ble hd ht1
      · intro l hl
        rcases List.mem_cons.1 hl with rfl | hl
        · simpa using key.1
        · exact key.2 l hl
    · by_cases h32 : c = 32
      · subst h32
        rw [splitOn_cons_ne (by omega) hs'] at hs
        obtain ⟨rfl, rfl⟩ := List.cons.inj hs
        rw [tkR_sep (Or.inl rfl)] at ht
        obtain ⟨ht1, ht2⟩ := Bool.and_eq_true_iff.1 ht
        have key := ih [] f' r' hs' hf' (by simp) ht2
        refine ⟨?_, key.2⟩
        rw [tkv_append_space]
        intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact tkv_lt_of_ble hd ht1 x h
        · exact key.1 x (by simpa using h)
      · have hdig : 48 ≤ c ∧ c ≤ 57 := by omega
        rw [splitOn_cons_ne h10 hs'] at hs
        obtain ⟨rfl, rfl⟩ := List.cons.inj hs
        rw [tkR_digit h10 h32, ← curOf_append_digit] at ht
        have hd' : ∀ x ∈ d ++ [c], 48 ≤ x ∧ x ≤ 57 := by
          intro x hx
          rcases List.mem_append.1 hx with h | h
          · exact hd x h
          · rw [List.mem_singleton.1 h]; exact hdig
        have key := ih (d ++ [c]) f' r' hs' hf' hd' ht
        simpa [List.append_assoc] using key

theorem parseNats_lt_of_tokLt {B : Nat} {cs : List Nat} (hf : CFSG.KC.Misc.O73.fmtK cs = true)
    (ht : CFSG.KC.Misc.O73.tokLt B cs = true) :
    ∀ line ∈ textLines (strL cs), ∀ x ∈ (parseNats line).toList, x < B := by
  intro line hline x hx
  rw [textLines_strL (lt128 hf)] at hline
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hline
  obtain ⟨hsub, hdig⟩ := line_digits hf (List.mem_filter.1 hl).1
  rw [parseNats_strL hdig] at hx
  obtain ⟨f, r, hs⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil 10 cs)
  have key := tkR_main B cs [] f r hs ((fmtK_iff cs).1 hf) (by simp) ht
  have hl' := (List.mem_filter.1 hl).1
  rw [hs] at hl'
  rcases List.mem_cons.1 hl' with rfl | hr
  · exact key.1 x (by simpa using hx)
  · exact key.2 l hr x hx

end CFSG.KS.PK

end
