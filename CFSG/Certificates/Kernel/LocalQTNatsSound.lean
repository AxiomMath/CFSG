module

public import Certificates.Data.Kernel.LocalQT.Nats
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Search

public section

namespace CFSG.KC.LQT.NP

open CFSG.KC.Ord

section Split

open String

private theorem sp_get0 : Pos.Raw.get " " 0 = ' ' := rfl
private theorem sp_next0 : Pos.Raw.next " " 0 = ⟨1⟩ := rfl

private theorem splitOnAux_sp (l m r : List Char) (acc : List String) :
    String.splitOnAux (String.ofList (l ++ m ++ r)) " " ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == ' ') r m.reverse).map String.ofList := by
  unfold String.splitOnAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, List.reverse_cons, sp_get0, sp_next0]
  have hend : " ".rawEndPos ≤ (⟨1⟩ : Pos.Raw) := by decide
  have hz : ∀ p : Pos.Raw, p.unoffsetBy 0 = p := fun ⟨n⟩ => by simp [Pos.Raw.unoffsetBy]
  simp only [hend, ↓reduceIte, hz]
  split
  · subst r
    simpa using extract_of_valid l m []
  · obtain ⟨c, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    simp only [by
      simpa [-ofList_append] using
        (⟨get_of_valid (l ++ m) (c :: r), next_of_valid (l ++ m) c r,
            extract_of_valid l m (c :: r)⟩ :
          _ ∧ _ ∧ _)]
    split <;> rename_i h
    · have hc : c = ' ' := by simpa using h
      subst hc
      have hu : utf8Len l + (utf8Len m + ' '.utf8Size) - 1 = utf8Len l + utf8Len m := by
        have : ' '.utf8Size = 1 := rfl
        omega
      have hx := extract_of_valid l m (' ' :: r)
      simp at hx
      simpa [Pos.Raw.unoffsetBy, hu, hx, Nat.add_assoc, List.splitOnPPrepend_cons_eq_ite] using
        splitOnAux_sp (l ++ m ++ [' ']) [] r ((ofList m) :: acc)
    · simpa [Pos.Raw.unoffsetBy, List.splitOnPPrepend_cons_eq_ite, h, Nat.add_assoc] using
        splitOnAux_sp l (m ++ [c]) r acc

private theorem splitOn_sp (cs : List Char) :
    (String.ofList cs).splitOn " " = (List.splitOnPPrepend (· == ' ') cs []).map String.ofList := by
  have h := splitOnAux_sp [] [] cs []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero, List.reverse_nil] at h
  unfold String.splitOn
  have hne : (" " == "") = false := by decide
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact h

end Split

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

private theorem isNat_digits (ds : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (String.ofList ds).toSlice.isNat = !ds.isEmpty := by
  unfold String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, String.copy_toSlice, String.toList_ofList]
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

private noncomputable def nOf (ds : List Char) : Nat :=
  ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

private theorem tokD (ds : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (if (String.ofList ds).isEmpty then none else some (String.ofList ds).toNat!) =
      if ds = [] then none else some (nOf ds) := by
  cases ds with
  | nil => rfl
  | cons c L =>
    have hne : (String.ofList (c :: L)).isEmpty = false := by simp
    rw [hne]
    unfold String.toNat! String.Slice.toNat!
    rw [isNat_digits (c :: L) hd]
    simp only [List.isEmpty_cons, Bool.not_false, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
      String.Slice.foldl_eq_foldl_toList, String.copy_toSlice, String.toList_ofList]
    exact congrArg some (foldl_digits (c :: L) 0 hd)

private theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by
  cases a <;> rfl

private theorem letO_eq (y : Nat) (k : Nat → Option (List Nat)) : letO y k = k y := by
  cases y <;> rfl

private theorem revN_eq (l : List Nat) : revN l = l.reverse := by
  suffices h : ∀ acc, List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons x acc)) l acc = l.reverse ++ acc by
    have e := h []
    rw [List.append_nil] at e
    exact e
  induction l with
  | nil => intro acc; rfl
  | cons x l ih =>
    intro acc
    change List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons x acc)) l (x :: acc) = _
    rw [ih]
    simp

private theorem eqL_eq {l m : List ℕ} (h : CFSG.KC.LQT.L.eqL l m = true) : l = m := by
  induction l generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [CFSG.KC.LQT.L.eqL])
  | cons x l ih => cases m with
    | nil => exact absurd h (by simp [CFSG.KC.LQT.L.eqL])
    | cons y m =>
      change CFSG.KC.Ord.andB (Nat.beq x y) (CFSG.KC.LQT.L.eqL l m) = true at h
      cases hxy : Nat.beq x y
      · rw [hxy] at h
        exact absurd h (by simp [CFSG.KC.Ord.andB])
      · rw [hxy] at h
        rw [Nat.eq_of_beq_eq_true hxy, ih h]

private noncomputable def natsR (cs : List Char) : List Nat → Nat → Bool → Option (List Nat) :=
  List.rec (motive := fun _ => List Nat → Nat → Bool → Option (List Nat))
    (fun acc cur t =>
      some (revN (Bool.rec (motive := fun _ => List Nat) acc (List.cons cur acc) t)))
    (fun c _ ih acc cur t => letO (Char.toNat c) fun k =>
      Bool.rec (motive := fun _ => Option (List Nat))
        (Bool.rec (motive := fun _ => Option (List Nat)) none
          (letO (Nat.add (Nat.mul cur 10) (Nat.sub k 48)) fun v => ih acc v true)
          (CFSG.KC.Ord.andB (Nat.ble 48 k) (Nat.ble k 57)))
        (ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons cur acc) t) 0 false)
        (Nat.beq k 32))
    cs

private noncomputable def tokOf (p : List Char) : Option Nat :=
  if (String.ofList p).isEmpty then none else some (String.ofList p).toNat!

private theorem emit_eq (acc : List Nat) (cur : List Char) (hd : ∀ c ∈ cur, c.isDigit = true) :
    (Bool.rec (motive := fun _ => List Nat) acc (List.cons (nOf cur) acc) (!cur.isEmpty)).reverse =
      acc.reverse ++ [cur].filterMap tokOf := by
  unfold tokOf
  rw [List.filterMap_cons, List.filterMap_nil, tokD cur hd]
  cases cur with
  | nil => simp
  | cons c L => simp

private theorem isDigit_of {c : Char} (h : CFSG.KC.Ord.andB (Nat.ble 48 c.toNat) (Nat.ble c.toNat 57) = true) :
    c.isDigit = true := by
  rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  unfold Char.isDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt32.le_iff_toNat_le]
  exact h

private theorem space_of {c : Char} (h : Nat.beq c.toNat 32 = true) : c = ' ' :=
  Char.ext (UInt32.toNat_inj.mp (by simpa using Nat.eq_of_beq_eq_true h))

private theorem natsR_sound : ∀ (cs : List Char) (acc : List Nat) (cur : List Char) (l : List Nat),
    (∀ c ∈ cur, c.isDigit = true) → natsR cs acc (nOf cur) (!cur.isEmpty) = some l →
    l = acc.reverse ++ (List.splitOnPPrepend (· == ' ') cs cur.reverse).filterMap tokOf
  | [], acc, cur, l, hd, h => by
    have e : some (revN (Bool.rec (motive := fun _ => List Nat) acc (List.cons (nOf cur) acc)
        (!cur.isEmpty))) = some l := h
    rw [List.splitOnPPrepend_nil, List.reverse_reverse, ← emit_eq acc cur hd, ← revN_eq]
    exact (Option.some.inj e).symm
  | c :: cs, acc, cur, l, hd, h => by
    change letO (Char.toNat c) (fun k =>
      Bool.rec (motive := fun _ => Option (List Nat))
        (Bool.rec (motive := fun _ => Option (List Nat)) none
          (letO (Nat.add (Nat.mul (nOf cur) 10) (Nat.sub k 48)) fun v => natsR cs acc v true)
          (CFSG.KC.Ord.andB (Nat.ble 48 k) (Nat.ble k 57)))
        (natsR cs (Bool.rec (motive := fun _ => List Nat) acc (List.cons (nOf cur) acc)
          (!cur.isEmpty)) 0 false)
        (Nat.beq k 32)) = some l at h
    rw [letO_eq] at h
    rw [List.splitOnPPrepend_cons_eq_ite]
    cases hs : Nat.beq c.toNat 32
    · rw [hs] at h
      change Bool.rec (motive := fun _ => Option (List Nat)) none
        (letO (Nat.add (Nat.mul (nOf cur) 10) (Nat.sub c.toNat 48)) fun v => natsR cs acc v true)
        (CFSG.KC.Ord.andB (Nat.ble 48 c.toNat) (Nat.ble c.toNat 57)) = some l at h
      have hc : (c == ' ') = false := by
        cases e : (c == ' ')
        · rfl
        · rw [beq_iff_eq] at e
          subst e
          exact absurd hs (by decide)
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      cases hg : CFSG.KC.Ord.andB (Nat.ble 48 c.toNat) (Nat.ble c.toNat 57)
      · rw [hg] at h
        exact absurd h (by simp)
      · rw [hg] at h
        change letO (Nat.add (Nat.mul (nOf cur) 10) (Nat.sub c.toNat 48))
          (fun v => natsR cs acc v true) = some l at h
        rw [letO_eq] at h
        have hdc := isDigit_of hg
        have hd' : ∀ x ∈ cur ++ [c], x.isDigit = true := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hd x hx
          · rw [List.mem_singleton.mp hx]
            exact hdc
        have e1 : Nat.add (Nat.mul (nOf cur) 10) (Nat.sub c.toNat 48) = nOf (cur ++ [c]) := by
          unfold nOf
          rw [List.foldl_append]
          rfl
        have e2 : (!(cur ++ [c]).isEmpty) = true := by simp
        have h' : natsR cs acc (nOf (cur ++ [c])) (!(cur ++ [c]).isEmpty) = some l := by
          rw [e2, ← e1]
          exact h
        have := natsR_sound cs acc (cur ++ [c]) l hd' h'
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at this
        exact this
    · rw [hs] at h
      have h' : natsR cs (Bool.rec (motive := fun _ => List Nat) acc (List.cons (nOf cur) acc)
          (!cur.isEmpty)) (nOf []) (!([] : List Char).isEmpty) = some l := h
      have hc : (c == ' ') = true := by rw [space_of hs]; rfl
      simp only [hc, ↓reduceIte]
      have := natsR_sound cs _ [] l (fun x hx => absurd hx List.not_mem_nil) h'
      rw [this, emit_eq acc cur hd, List.append_assoc, List.reverse_reverse, List.reverse_nil,
        List.splitOnP_eq_splitOnPPrepend, ← List.filterMap_append, List.singleton_append]

theorem nats_sound (cs : List Char) (L : List Nat) (h : natsOK cs L = true) :
    CFSG.QuasithinUnique.A5.Kc3Cert.parseNats (String.ofList cs) = L := by
  unfold natsOK at h
  cases hk : natsK cs with
  | none =>
    rw [hk] at h
    exact absurd h Bool.false_ne_true
  | some l =>
    rw [hk] at h
    have hl := natsR_sound cs [] [] l (fun x hx => absurd hx List.not_mem_nil) hk
    unfold CFSG.QuasithinUnique.A5.Kc3Cert.parseNats
    rw [splitOn_sp, List.filterMap_map, ← eqL_eq h, hl]
    rfl

end CFSG.KC.LQT.NP

end
