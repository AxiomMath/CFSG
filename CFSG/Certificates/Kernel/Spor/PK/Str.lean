module

public import Init
import all Init.Data.String.Slice
import all Init.Data.String.Search
import all Init.Data.String.Legacy

public section

namespace CFSG.KS.PK

@[expose] def strL (l : List Nat) : String := String.ofList (l.map Char.ofNat)

@[expose] def decVal (l : List Nat) : Nat := l.foldl (fun a c => 10 * a + (c - 48)) 0

@[expose] def IsDigits (l : List Nat) : Prop := l ≠ [] ∧ ∀ c ∈ l, 48 ≤ c ∧ c ≤ 57

theorem strL_append (a b : List Nat) : strL (a ++ b) = strL a ++ strL b := by
  simp [strL, String.ofList_append]

private theorem toList_strL' (l : List Nat) : (strL l).toList = l.map Char.ofNat := by
  simp [strL]

theorem toList_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) : (strL l).toList = l.map Char.ofNat := by
  clear hl
  exact toList_strL' l

private theorem valid_of_lt {n : Nat} (h : n < 128) : n.isValidChar := Or.inl (by omega)

private theorem toNat_ofNat {n : Nat} (h : n < 128) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dif_pos (valid_of_lt h)]
  rfl

private theorem utf8Size_ofNat {n : Nat} (h : n < 128) : (Char.ofNat n).utf8Size = 1 := by
  rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
  have := toNat_ofNat h
  simp only [Char.toNat] at this
  rw [this]
  simp
  omega

private theorem ofNat_inj {a b : Nat} (ha : a < 128) (hb : b < 128) :
    Char.ofNat a = Char.ofNat b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := congrArg Char.toNat h
  rwa [toNat_ofNat ha, toNat_ofNat hb] at this

theorem strL_inj {a b : List Nat} (ha : ∀ c ∈ a, c < 128) (hb : ∀ c ∈ b, c < 128)
    (h : strL a = strL b) : a = b := by
  have h1 : a.map Char.ofNat = b.map Char.ofNat := String.ofList_injective h
  have e : ∀ l : List Nat, (∀ c ∈ l, c < 128) → (l.map Char.ofNat).map Char.toNat = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro hl
      simp only [List.map_cons]
      rw [toNat_ofNat (hl x List.mem_cons_self), ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))]
  calc a = (a.map Char.ofNat).map Char.toNat := (e a ha).symm
    _ = (b.map Char.ofNat).map Char.toNat := by rw [h1]
    _ = b := e b hb

theorem strL_eq_empty_iff (l : List Nat) : strL l = "" ↔ l = [] := by
  simp [strL]

theorem isEmpty_strL (l : List Nat) : (strL l).isEmpty = l.isEmpty := by
  rw [Bool.eq_iff_iff]
  simp [String.isEmpty_iff, strL_eq_empty_iff]

private theorem utf8ByteSize_strL : ∀ {l : List Nat}, (∀ c ∈ l, c < 128) →
    (strL l).utf8ByteSize = l.length
  | [], _ => by simp [strL]
  | a :: l, hl => by
    have h1 : strL (a :: l) = String.singleton (Char.ofNat a) ++ strL l := by
      rw [String.singleton_eq_ofList]
      exact strL_append [a] l
    rw [h1, String.utf8ByteSize_append, String.utf8ByteSize_singleton,
      utf8ByteSize_strL (fun c hc => hl c (List.mem_cons_of_mem _ hc)),
      utf8Size_ofNat (hl a List.mem_cons_self)]
    simp [Nat.add_comm]

private theorem utf8GetAux_ascii : ∀ (L : List Char) (k i : Nat), (∀ c ∈ L, c.utf8Size = 1) →
    String.Pos.Raw.utf8GetAux L ⟨k⟩ ⟨k + i⟩ = L.getD i default
  | [], _, _, _ => by simp [String.Pos.Raw.utf8GetAux]
  | c :: cs, k, i, h => by
    cases i with
    | zero => simp [String.Pos.Raw.utf8GetAux]
    | succ j =>
      have hc : c.utf8Size = 1 := h c List.mem_cons_self
      have h2 := utf8GetAux_ascii cs (k + 1) j (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [String.Pos.Raw.utf8GetAux]
      rw [if_neg (by simp [String.Pos.Raw.ext_iff])]
      have h3 : (⟨k⟩ : String.Pos.Raw) + c = ⟨k + 1⟩ := by
        simp [String.Pos.Raw.ext_iff, hc]
      rw [h3, show k + (j + 1) = k + 1 + j by omega, h2]
      simp


private theorem get_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) {i : Nat} (hi : i < l.length) :
    String.Pos.Raw.get (strL l) ⟨i⟩ = Char.ofNat l[i] := by
  have h1 : ∀ c ∈ l.map Char.ofNat, c.utf8Size = 1 := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    exact utf8Size_ofNat (hl a ha)
  have := utf8GetAux_ascii (l.map Char.ofNat) 0 i h1
  simp only [Nat.zero_add] at this
  unfold String.Pos.Raw.get
  rw [toList_strL']
  simpa [List.getD_eq_getElem?_getD, hi] using this

private theorem next_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) {i : Nat} (hi : i < l.length) :
    String.Pos.Raw.next (strL l) ⟨i⟩ = ⟨i + 1⟩ := by
  unfold String.Pos.Raw.next
  simp only [get_strL hl hi]
  simp [String.Pos.Raw.ext_iff, utf8Size_ofNat (hl _ (List.getElem_mem hi))]

private theorem atEnd_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) (i : Nat) :
    String.Pos.Raw.atEnd (strL l) ⟨i⟩ = decide (l.length ≤ i) := by
  unfold String.Pos.Raw.atEnd
  simp [utf8ByteSize_strL hl]


private theorem go₂_ascii : ∀ (L : List Char) (k E : Nat), k ≤ E → (∀ c ∈ L, c.utf8Size = 1) →
    String.Pos.Raw.extract.go₂ L ⟨k⟩ ⟨E⟩ = L.take (E - k)
  | [], _, _, _, _ => by simp [String.Pos.Raw.extract.go₂]
  | c :: cs, k, E, hkE, h => by
    have hc : c.utf8Size = 1 := h c List.mem_cons_self
    have h3 : (⟨k⟩ : String.Pos.Raw) + c = ⟨k + 1⟩ := by
      simp [String.Pos.Raw.ext_iff, hc]
    by_cases hE : k = E
    · subst hE
      simp [String.Pos.Raw.extract.go₂]
    · have h2 := go₂_ascii cs (k + 1) E (by omega) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [String.Pos.Raw.extract.go₂]
      rw [if_neg (by simp [String.Pos.Raw.ext_iff]; omega), h3, h2]
      rw [show E - k = (E - (k + 1)) + 1 by omega]
      simp

private theorem go₁_ascii : ∀ (L : List Char) (k B E : Nat), k ≤ B → B ≤ E →
    (∀ c ∈ L, c.utf8Size = 1) →
    String.Pos.Raw.extract.go₁ L ⟨k⟩ ⟨B⟩ ⟨E⟩ = (L.drop (B - k)).take (E - B)
  | [], _, _, _, _, _, _ => by simp [String.Pos.Raw.extract.go₁]
  | c :: cs, k, B, E, hkB, hBE, h => by
    have hc : c.utf8Size = 1 := h c List.mem_cons_self
    have h3 : (⟨k⟩ : String.Pos.Raw) + c = ⟨k + 1⟩ := by
      simp [String.Pos.Raw.ext_iff, hc]
    by_cases hB : k = B
    · subst hB
      simp [String.Pos.Raw.extract.go₁, go₂_ascii _ _ _ hBE h]
    · have h2 := go₁_ascii cs (k + 1) B E (by omega) hBE
        (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [String.Pos.Raw.extract.go₁]
      rw [if_neg (by simp [String.Pos.Raw.ext_iff]; omega), h3, h2]
      rw [show B - k = (B - (k + 1)) + 1 by omega]
      simp

private theorem extract_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) (b e : Nat) :
    String.Pos.Raw.extract (strL l) ⟨b⟩ ⟨e⟩ = strL ((l.drop b).take (e - b)) := by
  have h1 : ∀ c ∈ l.map Char.ofNat, c.utf8Size = 1 := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    exact utf8Size_ofNat (hl a ha)
  unfold String.Pos.Raw.extract
  dsimp only
  by_cases hbe : b ≥ e
  · rw [if_pos hbe]
    rw [show e - b = 0 by omega]
    simp [strL]
  · rw [if_neg hbe, toList_strL']
    have := go₁_ascii (l.map Char.ofNat) 0 b e (by omega) (by omega) h1
    simp only [Nat.sub_zero] at this
    show String.ofList (String.Pos.Raw.extract.go₁ _ ⟨0⟩ ⟨b⟩ ⟨e⟩) = _
    rw [this]
    simp [strL, List.map_drop, List.map_take]


private theorem splitOnAux_strL {k : Nat} (hk : k < 128) :
    ∀ (rest pre c : List Nat) (r : List String),
      (∀ x ∈ pre ++ c ++ rest, x < 128) → (∀ x ∈ c, x ≠ k) →
      String.splitOnAux (strL (pre ++ c ++ rest)) (strL [k]) ⟨pre.length⟩
          ⟨pre.length + c.length⟩ 0 r
        = r.reverse ++ ((c ++ rest).splitOn k).map strL
  | [], pre, c, r, hl, hc => by
    rw [List.append_nil] at hl ⊢
    rw [String.splitOnAux.eq_1, atEnd_strL hl]
    have hk' : k ∉ c := fun h => hc k h rfl
    simp [extract_strL hl, List.splitOn_eq_singleton hk']
  | x :: rest, pre, c, r, hl, hc => by
    have hx : x < 128 := hl x (by simp)
    have hlen : pre.length + c.length < (pre ++ c ++ x :: rest).length := by simp
    have hget : (pre ++ c ++ x :: rest)[pre.length + c.length]'hlen = x := by
      simp [List.getElem_append_right]
    have hsep : String.Pos.Raw.get (strL [k]) 0 = Char.ofNat k :=
      get_strL (l := [k]) (by simpa using hk) (i := 0) (by simp)
    have hsepn : String.Pos.Raw.next (strL [k]) 0 = ⟨1⟩ :=
      next_strL (l := [k]) (by simpa using hk) (i := 0) (by simp)
    have hsepe : String.Pos.Raw.atEnd (strL [k]) ⟨1⟩ = true := by
      rw [atEnd_strL (l := [k]) (by simpa using hk)]
      simp
    rw [String.splitOnAux.eq_1, atEnd_strL hl]
    simp only [show ¬ ((pre ++ c ++ x :: rest).length ≤ pre.length + c.length) from by omega,
      decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [get_strL hl hlen, hsep, hget]
    by_cases hxk : x = k
    · subst hxk
      simp only [beq_self_eq_true, ↓reduceIte, hsepn, next_strL hl hlen, hsepe]
      have hun : (⟨pre.length + c.length + 1⟩ : String.Pos.Raw).unoffsetBy ⟨1⟩
          = ⟨pre.length + c.length⟩ := by
        simp [String.Pos.Raw.ext_iff]
      have hk' : x ∉ c := fun h => hc x h rfl
      rw [hun, extract_strL hl]
      have ih := splitOnAux_strL hk rest (pre ++ c ++ [x]) []
        (strL (((pre ++ c ++ x :: rest).drop pre.length).take
          (pre.length + c.length - pre.length)) :: r)
        (by simpa using hl) (by simp)
      have e1 : pre ++ c ++ [x] ++ [] ++ rest = pre ++ c ++ x :: rest := by simp
      have e2 : (pre ++ c ++ [x]).length = pre.length + c.length + 1 := by
        simp only [List.length_append, List.length_singleton]
      rw [e1, e2] at ih
      simp only [List.length_nil, Nat.add_zero] at ih
      rw [ih]
      simp [List.splitOn_append_cons_self_of_not_mem hk']
    · have hne : (Char.ofNat x == Char.ofNat k) = false := by
        simpa [beq_iff_eq, ofNat_inj hx hk] using hxk
      simp only [hne, Bool.false_eq_true, ↓reduceIte, String.Pos.Raw.unoffsetBy_zero,
        next_strL hl hlen]
      have ih := splitOnAux_strL hk rest pre (c ++ [x]) r (by simpa using hl)
        (by
          intro y hy
          rcases List.mem_append.1 hy with h | h
          · exact hc y h
          · rw [List.mem_singleton.1 h]; exact hxk)
      have e1 : pre ++ (c ++ [x]) ++ rest = pre ++ c ++ x :: rest := by simp
      have e2 : pre.length + (c ++ [x]).length = pre.length + c.length + 1 := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [e1, e2] at ih
      rw [ih]
      simp


private theorem splitOn_strL_gen {l : List Nat} (hl : ∀ c ∈ l, c < 128) {k : Nat} (hk : k < 128) :
    (strL l).splitOn (strL [k]) = (l.splitOn k).map strL := by
  have hne : (strL [k] == "") = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := (strL_eq_empty_iff [k]).1 h
    simp at this
  unfold String.splitOn
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := splitOnAux_strL hk l [] [] [] (by simpa using hl) (by simp)
  simpa using this

theorem splitOn_space_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) :
    (strL l).splitOn " " = (l.splitOn 32).map strL := by
  have : (" " : String) = strL [32] := by
    apply String.toList_injective
    simp [toList_strL']
  rw [this]
  exact splitOn_strL_gen hl (by decide)

theorem splitOn_newline_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) :
    (strL l).splitOn "\n" = (l.splitOn 10).map strL := by
  have : ("\n" : String) = strL [10] := by
    apply String.toList_injective
    simp [toList_strL']
  rw [this]
  exact splitOn_strL_gen hl (by decide)

theorem splitOn_comma_strL {l : List Nat} (hl : ∀ c ∈ l, c < 128) :
    (strL l).splitOn "," = (l.splitOn 44).map strL := by
  have : ("," : String) = strL [44] := by
    apply String.toList_injective
    simp [toList_strL']
  rw [this]
  exact splitOn_strL_gen hl (by decide)

private theorem forIn_digits : ∀ (cs : List Char) (st : Bool), cs ≠ [] →
    (∀ c ∈ cs, c.isDigit = true) →
    (forIn cs ((none : Option Bool), st) (fun (c : Char) (__s : Option Bool × Bool) =>
        if c = '_' then
          if (!__s.snd) = true then pure (ForInStep.done (some false, __s.snd))
          else pure (ForInStep.yield (none, false))
        else
          if c.isDigit = true then pure (ForInStep.yield (none, true))
          else pure (ForInStep.done (some false, __s.snd))) : Id (Option Bool × Bool))
      = (none, true)
  | [], _, h, _ => absurd rfl h
  | c :: cs, st, _, hd => by
    have hc : c.isDigit = true := hd c List.mem_cons_self
    have hne : c ≠ '_' := by
      rintro rfl
      exact absurd hc (by decide)
    cases cs with
    | nil =>
      simp [hne, hc]
      rfl
    | cons d ds =>
      have := forIn_digits (d :: ds) true (by simp) (fun x hx => hd x (List.mem_cons_of_mem _ hx))
      simpa [hne, hc] using this

private theorem isNat_of_toList (t : String.Slice) (cs : List Char) (h : t.copy.toList = cs)
    (hne : cs ≠ []) (hd : ∀ c ∈ cs, c.isDigit = true) : t.isNat = true := by
  unfold String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, h]
  rw [forIn_digits cs false hne hd]
  rfl

private theorem isDigit_ofNat {c : Nat} (hc : c < 128) :
    (Char.ofNat c).isDigit = true ↔ 48 ≤ c ∧ c ≤ 57 := by
  rw [Char.isDigit_iff_toNat, toNat_ofNat hc]
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  rw [h0, h9]

private theorem digits_isDigit {l : List Nat} (hl : IsDigits l) :
    ∀ c ∈ l.map Char.ofNat, c.isDigit = true := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  have := hl.2 a ha
  exact (isDigit_ofNat (by omega)).2 this

private theorem foldl_digits : ∀ (l : List Nat) (a : Nat), (∀ c ∈ l, 48 ≤ c ∧ c ≤ 57) →
    (l.map Char.ofNat).foldl
        (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) a
      = l.foldl (fun a c => 10 * a + (c - 48)) a
  | [], _, _ => rfl
  | x :: xs, a, h => by
    have hx := h x List.mem_cons_self
    have hx' : x < 128 := by omega
    have hne : Char.ofNat x ≠ '_' := by
      intro he
      have := congrArg Char.toNat he
      rw [toNat_ofNat hx'] at this
      have h95 : '_'.toNat = 95 := rfl
      omega
    have h0 : '0'.toNat = 48 := rfl
    simp only [List.map_cons, List.foldl_cons, hne, ↓reduceIte, toNat_ofNat hx', h0]
    rw [Nat.mul_comm a 10]
    exact foldl_digits xs _ (fun c hc => h c (List.mem_cons_of_mem _ hc))

private theorem slice_isNat {t : String.Slice} {l : List Nat} (hl : IsDigits l)
    (ht : t.copy = strL l) : t.isNat = true := by
  have h1 : t.copy.toList = l.map Char.ofNat := by rw [ht, toList_strL']
  exact isNat_of_toList t _ h1 (by simpa using hl.1) (digits_isDigit hl)

private theorem slice_toNat? {t : String.Slice} {l : List Nat} (hl : IsDigits l)
    (ht : t.copy = strL l) : t.toNat? = some (decVal l) := by
  have h1 : t.copy.toList = l.map Char.ofNat := by rw [ht, toList_strL']
  unfold String.Slice.toNat?
  rw [if_pos (slice_isNat hl ht)]
  simp only [String.Slice.foldl_eq_foldl_toList, h1]
  rw [foldl_digits l 0 hl.2]
  rfl

private theorem slice_toNat! {t : String.Slice} {l : List Nat} (hl : IsDigits l)
    (ht : t.copy = strL l) : t.toNat! = decVal l := by
  have h1 : t.copy.toList = l.map Char.ofNat := by rw [ht, toList_strL']
  unfold String.Slice.toNat!
  rw [if_pos (slice_isNat hl ht)]
  simp only [String.Slice.foldl_eq_foldl_toList, h1]
  rw [foldl_digits l 0 hl.2]
  rfl

theorem toNat?_strL {l : List Nat} (hl : IsDigits l) : (strL l).toNat? = some (decVal l) :=
  slice_toNat? hl String.copy_toSlice

theorem toNat!_strL {l : List Nat} (hl : IsDigits l) : (strL l).toNat! = decVal l :=
  slice_toNat! hl String.copy_toSlice

private theorem ofNat_ne_minus {a : Nat} (ha : 48 ≤ a ∧ a ≤ 57) : Char.ofNat a ≠ '-' := by
  intro he
  have := congrArg Char.toNat he
  rw [toNat_ofNat (by omega)] at this
  have h45 : '-'.toNat = 45 := rfl
  omega

private theorem dropPrefix?_none {t : String.Slice} {l : List Nat} (hl : IsDigits l)
    (ht : t.copy = strL l) : t.dropPrefix? '-' = none := by
  rw [String.Slice.dropPrefix?_eq_none_iff, String.Slice.startsWith_char_eq_head?, ht, toList_strL']
  obtain ⟨hne, hd⟩ := hl
  cases l with
  | nil => exact absurd rfl hne
  | cons a l' =>
    have := ofNat_ne_minus (hd a List.mem_cons_self)
    simp [this]

private theorem dropPrefix?_some {t : String.Slice} {l : List Nat}
    (ht : t.copy = strL (45 :: l)) :
    ∃ rest : String.Slice, t.dropPrefix? '-' = some rest ∧ rest.copy = strL l := by
  have h45 : Char.ofNat 45 = '-' := by decide
  have hs : t.startsWith '-' = true := by
    rw [String.Slice.startsWith_char_eq_head?, ht, toList_strL']
    simp [h45]
  cases h : t.dropPrefix? '-' with
  | none =>
    rw [String.Slice.dropPrefix?_eq_none_iff, hs] at h
    exact absurd h (by simp)
  | some rest =>
    refine ⟨rest, rfl, ?_⟩
    have h2 := String.Slice.eq_append_of_dropPrefix?_char_eq_some h
    have e : strL (45 :: l) = String.singleton '-' ++ strL l := by
      rw [show (45 :: l) = [45] ++ l from rfl, strL_append, String.singleton_eq_ofList]
      simp [strL, h45]
    rw [ht, e] at h2
    exact ((String.append_right_inj _).1 h2).symm

private theorem slice_toInt?_pos {t : String.Slice} {l : List Nat} (hl : IsDigits l)
    (ht : t.copy = strL l) : t.toInt? = some (decVal l : Int) := by
  unfold String.Slice.toInt?
  rw [dropPrefix?_none hl ht]
  simp only [slice_toNat? hl ht, Option.map_some]
  rfl

private theorem slice_toInt?_neg {t : String.Slice} {l : List Nat} (hl : IsDigits l)
    (ht : t.copy = strL (45 :: l)) : t.toInt? = some (-(decVal l : Int)) := by
  obtain ⟨rest, h1, h2⟩ := dropPrefix?_some ht
  unfold String.Slice.toInt?
  rw [h1]
  simp only [slice_toNat? hl h2, Option.map_some]
  rfl

theorem toInt?_strL {l : List Nat} (hl : IsDigits l) :
    (strL l).toInt? = some (decVal l : Int) :=
  slice_toInt?_pos hl String.copy_toSlice

theorem toInt?_strL_neg {l : List Nat} (hl : IsDigits l) :
    (strL (45 :: l)).toInt? = some (-(decVal l : Int)) :=
  slice_toInt?_neg hl String.copy_toSlice

theorem toInt!_strL {l : List Nat} (hl : IsDigits l) : (strL l).toInt! = (decVal l : Int) := by
  show (strL l).toSlice.toInt! = _
  unfold String.Slice.toInt!
  rw [slice_toInt?_pos hl String.copy_toSlice]

theorem toInt!_strL_neg {l : List Nat} (hl : IsDigits l) :
    (strL (45 :: l)).toInt! = -(decVal l : Int) := by
  show (strL (45 :: l)).toSlice.toInt! = _
  unfold String.Slice.toInt!
  rw [slice_toInt?_neg hl String.copy_toSlice]

end CFSG.KS.PK

end
