module

public import Certificates.Data.Kernel.SporSch.PairSyl
public import CFSG.Certificates.Kernel.SporSch.PairJ3CertSound
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch.PSylEnc

open CFSG.Sporadic.Schreier.PairText CFSG.KS.Raw CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.PJ3Enc

@[expose] noncomputable def toChain (n w : Nat) (c : ChainP) : ChainRec :=
  { gens := (c.gens.map (unpack n w)).toArray, base := c.base,
    strong := (c.strong.map (unpack n w)).toArray, words := c.words.toArray }

@[expose] noncomputable def toRec (n w : Nat) (r : RecP) : NGRec :=
  { rep := unpack n w r.rep, conj := r.conj.toArray, chain := toChain n w r.chain }

@[expose] noncomputable def toSyl (n w : Nat) (s : SylP) : SylowRec :=
  { prime := s.prime, gens := (s.gens.map (unpack n w)).toArray,
    records := (s.records.map (toRec n w)).toArray }

theorem fldI_eq (w P k : Nat) : ∀ (s : Nat) (tl : List Int),
    fldI w P k s tl = (List.range' s k).map (fun j => Int.ofNat (pg w (mask w) P j)) ++ tl := by
  induction k with
  | zero => intro s tl; rfl
  | succ k ih =>
    intro s tl
    change Int.ofNat (pg w (mask w) P s) :: fldI w P k (Nat.succ s) tl = _
    rw [ih, List.range'_succ]
    rfl

theorem fldI_length (w P k : Nat) : (fldI w P k 0 []).length = k := by
  rw [fldI_eq]
  simp

theorem permsI_cons (n w P : Nat) (Ps : List Nat) (tl : List Int) :
    permsI n w (P :: Ps) tl = fldI w P n 0 [] ++ permsI n w Ps tl := by
  change fldI w P n 0 (permsI n w Ps tl) = _
  rw [fldI_eq, fldI_eq]
  simp

theorem permsI_eq (n w : Nat) (Ps : List Nat) (tl : List Int) :
    permsI n w Ps tl = permsI n w Ps [] ++ tl := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih => rw [permsI_cons, permsI_cons, ih, List.append_assoc]

theorem permsI_length (n w : Nat) (Ps : List Nat) : (permsI n w Ps []).length = n * Ps.length := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
    rw [permsI_cons, List.length_append, fldI_length, ih, List.length_cons]
    ring

theorem permsI_append (n w : Nat) (l₁ l₂ : List Nat) :
    permsI n w (l₁ ++ l₂) [] = permsI n w l₁ [] ++ permsI n w l₂ [] := by
  induction l₁ with
  | nil => rfl
  | cons P l ih => rw [List.cons_append, permsI_cons, permsI_cons, ih, List.append_assoc]

theorem intsI_eq (l tl : List Int) : intsI l tl = l ++ tl := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (x :: ·) ih

theorem wordsI_cons (x : List Int) (ws : List (List Int)) (tl : List Int) :
    wordsI (x :: ws) tl = (Int.ofNat x.length :: x) ++ wordsI ws tl := by
  change Int.ofNat (lenK x) :: intsI x (wordsI ws tl) = _
  rw [lenK_eq, intsI_eq]
  rfl

theorem wordsI_eq (ws : List (List Int)) (tl : List Int) : wordsI ws tl = wordsI ws [] ++ tl := by
  induction ws with
  | nil => rfl
  | cons x ws ih => rw [wordsI_cons, wordsI_cons, ih, List.append_assoc]

theorem natsI_nil (l : List Nat) (tl : List Int) : natsI l tl = natsI l [] ++ tl := by
  rw [natsI_eq, natsI_eq, List.append_nil]

theorem chainI_eq (n w : Nat) (c : ChainP) (tl : List Int) :
    chainI n w c tl = [Int.ofNat c.gens.length, Int.ofNat c.base.length,
      Int.ofNat c.strong.length, Int.ofNat c.words.length] ++ permsI n w c.gens [] ++
      natsI c.base [] ++ permsI n w c.strong [] ++ wordsI c.words [] ++ tl := by
  obtain ⟨g, b, s, wd⟩ := c
  change Int.ofNat (lenK g) :: Int.ofNat (lenK b) :: Int.ofNat (lenK s) :: Int.ofNat (lenK wd) ::
    permsI n w g (natsI b (permsI n w s (wordsI wd tl))) = _
  rw [lenK_eq, lenK_eq, lenK_eq, lenK_eq, wordsI_eq, permsI_eq n w s, natsI_nil, permsI_eq n w g]
  simp

theorem chainI_tl (n w : Nat) (c : ChainP) (tl : List Int) : chainI n w c tl = chainI n w c [] ++ tl := by
  rw [chainI_eq, chainI_eq n w c []]
  simp

theorem recI_eq (n w : Nat) (r : RecP) (tl : List Int) :
    recI n w r tl = fldI w r.rep n 0 [] ++ [Int.ofNat r.conj.length] ++ wordsI r.conj [] ++
      chainI n w r.chain [] ++ tl := by
  obtain ⟨rp, cj, ch⟩ := r
  change fldI w rp n 0 (Int.ofNat (lenK cj) :: wordsI cj (chainI n w ch tl)) = _
  rw [lenK_eq, fldI_eq, fldI_eq, wordsI_eq, chainI_eq, chainI_eq n w ch []]
  simp

theorem recsI_cons (n w : Nat) (r : RecP) (rs : List RecP) (tl : List Int) :
    recsI n w (r :: rs) tl = recI n w r [] ++ recsI n w rs tl := by
  change recI n w r (recsI n w rs tl) = _
  rw [recI_eq, recI_eq n w r []]
  simp

theorem recsI_eq (n w : Nat) (rs : List RecP) (tl : List Int) : recsI n w rs tl = recsI n w rs [] ++ tl := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [recsI_cons, recsI_cons, ih, List.append_assoc]

theorem sylI_eq (n w : Nat) (s : SylP) (tl : List Int) :
    sylI n w s tl = [Int.ofNat s.prime, Int.ofNat s.gens.length] ++ permsI n w s.gens [] ++
      [Int.ofNat s.records.length] ++ recsI n w s.records [] ++ tl := by
  obtain ⟨p, g, rs⟩ := s
  change Int.ofNat p :: Int.ofNat (lenK g) :: permsI n w g (Int.ofNat (lenK rs) :: recsI n w rs tl) = _
  rw [lenK_eq, lenK_eq, permsI_eq, recsI_eq]
  simp

theorem sylsI_cons (n w : Nat) (s : SylP) (ss : List SylP) (tl : List Int) :
    sylsI n w (s :: ss) tl = sylI n w s [] ++ sylsI n w ss tl := by
  change sylI n w s (sylsI n w ss tl) = _
  rw [sylI_eq, sylI_eq n w s []]
  simp

theorem tok_at (A R : List Int) (x : Int) : (A ++ x :: R).toArray[A.length]! = x := by
  rw [get_toArray, getD_mid]

theorem read_fld (n w P : Nat) (A tl : List Int) :
    tokNats (A ++ fldI w P n 0 tl).toArray A.length n = unpack n w P := by
  rw [fldI_eq]
  unfold tokNats unpack
  apply Array.ext (by simp)
  intro j h1 h2
  have hj : j < n := by simpa using h1
  simp only [Array.getElem_ofFn, get_toArray]
  rw [getD_mid' _ _ _ (by simp; omega), List.getElem_append_left (by simpa using hj)]
  simp

theorem read_perms (n w : Nat) (Ps : List Nat) (A tl : List Int) :
    tokPerms n (A ++ permsI n w Ps tl).toArray A.length Ps.length =
      ((Ps.map (unpack n w)).toArray, (A ++ permsI n w Ps []).length) := by
  have key : ∀ j (hj : j < Ps.length),
      tokNats (A ++ permsI n w Ps tl).toArray (A.length + n * j) n = unpack n w Ps[j] := by
    intro j hj
    have e : Ps = Ps.take j ++ Ps[j] :: Ps.drop (j + 1) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hs : A ++ permsI n w Ps tl =
        (A ++ permsI n w (Ps.take j) []) ++ fldI w Ps[j] n 0 (permsI n w (Ps.drop (j + 1)) tl) := by
      have h := congrArg (fun l => permsI n w l []) e
      rw [permsI_eq n w Ps tl, h, permsI_append, permsI_cons, fldI_eq, fldI_eq,
        permsI_eq n w (Ps.drop (j + 1)) tl]
      simp only [List.append_assoc, List.append_nil]
    have hl : (A ++ permsI n w (Ps.take j) []).length = A.length + n * j := by
      rw [List.length_append, permsI_length, List.length_take, Nat.min_eq_left (by omega)]
    rw [hs, ← hl]
    exact read_fld n w Ps[j] _ _
  unfold tokPerms
  refine Prod.ext ?_ (by simp [permsI_length])
  apply Array.ext (by simp)
  intro j h1 h2
  have hj : j < Ps.length := by simpa using h1
  simp only [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map]
  exact key j hj

theorem read_word (x : List Int) (A tl : List Int) :
    tokWord (A ++ (Int.ofNat x.length :: x) ++ tl).toArray A.length =
      (x, (A ++ (Int.ofNat x.length :: x)).length) := by
  unfold tokWord
  have h0 : (A ++ (Int.ofNat x.length :: x) ++ tl).toArray[A.length]! = Int.ofNat x.length := by
    rw [List.append_assoc, List.cons_append, tok_at]
  rw [h0]
  have e : (Int.ofNat x.length).toNat = x.length := rfl
  rw [e]
  refine Prod.ext ?_ (by simp; omega)
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < x.length := by simpa using h1
  have ea : A ++ (Int.ofNat x.length :: x) ++ tl = (A ++ [Int.ofNat x.length]) ++ (x ++ tl) := by simp
  have ei : A.length + 1 + j = (A ++ [Int.ofNat x.length]).length + j := by simp
  rw [List.getElem_map, List.getElem_range, get_toArray, ea, ei, getD_app _ _ _ _ hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

@[expose] def stW (t : Array Int) (b : Nat × Array (List Int)) (_ : Nat) : Nat × Array (List Int) :=
  ((tokWord t b.1).2, b.2.push (tokWord t b.1).1)

theorem words_fold (ws : List (List Int)) (A tl : List Int) (acc : Array (List Int)) (xs : List Nat)
    (hx : xs.length = ws.length) :
    xs.foldl (stW (A ++ wordsI ws tl).toArray) (A.length, acc) =
      ((A ++ wordsI ws []).length, acc ++ ws.toArray) := by
  induction ws generalizing A acc xs with
  | nil =>
    rw [List.length_eq_zero_iff.1 hx]
    simp [wordsI]
  | cons x ws ih =>
    obtain ⟨a, xs, rfl⟩ : ∃ a xs', xs = a :: xs' := by
      cases xs with
      | nil => simp at hx
      | cons a xs' => exact ⟨a, xs', rfl⟩
    have hP : A ++ wordsI (x :: ws) tl = (A ++ (Int.ofNat x.length :: x)) ++ wordsI ws tl := by
      rw [wordsI_cons, List.append_assoc]
    have hP0 : A ++ wordsI (x :: ws) [] = (A ++ (Int.ofNat x.length :: x)) ++ wordsI ws [] := by
      rw [wordsI_cons, List.append_assoc]
    have hs : stW (A ++ wordsI (x :: ws) tl).toArray (A.length, acc) a =
        ((A ++ (Int.ofNat x.length :: x)).length, acc.push x) := by
      unfold stW
      rw [hP, read_word]
    rw [List.foldl_cons, hs, hP, hP0, ih _ _ _ (by simpa using hx)]
    simp

theorem read_words (ws : List (List Int)) (A tl : List Int) :
    tokWords (A ++ wordsI ws tl).toArray A.length ws.length =
      (ws.toArray, (A ++ wordsI ws []).length) := by
  have h := words_fold ws A tl #[] (List.range' 0 ws.length) (by simp)
  unfold tokWords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  unfold stW at h
  rw [h]
  simp only [List.length_append, Array.empty_append]
  rfl

theorem read_nats (l : List Nat) (A tl : List Int) :
    (tokNats (A ++ natsI l tl).toArray A.length l.length).toList = l := by
  rw [natsI_eq]
  apply List.ext_getElem (by simp [tokNats])
  intro j h1 h2
  simp only [tokNats, Array.toList_ofFn, List.getElem_ofFn, get_toArray]
  rw [getD_mid' _ _ _ (by simp; omega), List.getElem_append_left (by simpa using h2)]
  simp

theorem tok_at' (A B R : List Int) (x : Int) (k : Nat) (hk : (A ++ B).length = k) :
    (A ++ B ++ x :: R).toArray[k]! = x := by
  rw [← hk, tok_at]

theorem read_chain (n w : Nat) (c : ChainP) (A tl : List Int) :
    tokChain n (A ++ chainI n w c tl).toArray A.length =
      (toChain n w c, (A ++ chainI n w c []).length) := by
  obtain ⟨g, b, s, wd⟩ := c
  have hc := chainI_eq n w ⟨g, b, s, wd⟩ tl
  simp only at hc
  have L0 : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A ++ [] ++ Int.ofNat g.length ::
      (Int.ofNat b.length :: Int.ofNat s.length :: Int.ofNat wd.length ::
        (permsI n w g [] ++ natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl)) := by
    rw [hc]
    simp
  have L1 : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A ++ [Int.ofNat g.length] ++ Int.ofNat b.length ::
      (Int.ofNat s.length :: Int.ofNat wd.length ::
        (permsI n w g [] ++ natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl)) := by
    rw [hc]
    simp
  have L2 : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A ++ [Int.ofNat g.length, Int.ofNat b.length] ++
      Int.ofNat s.length :: (Int.ofNat wd.length ::
        (permsI n w g [] ++ natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl)) := by
    rw [hc]
    simp
  have L3 : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A ++ [Int.ofNat g.length, Int.ofNat b.length,
      Int.ofNat s.length] ++ Int.ofNat wd.length ::
        (permsI n w g [] ++ natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl) := by
    rw [hc]
    simp
  set H : List Int := [Int.ofNat g.length, Int.ofNat b.length, Int.ofNat s.length,
    Int.ofNat wd.length] with hH
  have Lg : A ++ chainI n w ⟨g, b, s, wd⟩ tl =
      (A ++ H) ++ permsI n w g (natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl) := by
    rw [hc, permsI_eq n w g (natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl)]
    simp only [List.append_assoc]
  set A1 := A ++ H ++ permsI n w g [] with hA1
  have Lb : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A1 ++ natsI b (permsI n w s [] ++ wordsI wd [] ++ tl) := by
    rw [hc, hA1, natsI_nil b (permsI n w s [] ++ wordsI wd [] ++ tl)]
    simp only [List.append_assoc]
  set A2 := A1 ++ natsI b [] with hA2
  have Ls : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A2 ++ permsI n w s (wordsI wd [] ++ tl) := by
    rw [hc, hA2, hA1, permsI_eq n w s (wordsI wd [] ++ tl)]
    simp only [List.append_assoc]
  set A3 := A2 ++ permsI n w s [] with hA3
  have Lw : A ++ chainI n w ⟨g, b, s, wd⟩ tl = A3 ++ wordsI wd tl := by
    rw [hc, hA3, hA2, hA1, wordsI_eq wd tl]
    simp only [List.append_assoc]
  set t := (A ++ chainI n w ⟨g, b, s, wd⟩ tl).toArray with ht
  have h0 : t[A.length]! = Int.ofNat g.length := by
    rw [ht, L0]
    exact tok_at' _ _ _ _ _ (by simp)
  have h1 : t[A.length + 1]! = Int.ofNat b.length := by
    rw [ht, L1]
    exact tok_at' _ _ _ _ _ (by simp)
  have h2 : t[A.length + 2]! = Int.ofNat s.length := by
    rw [ht, L2]
    exact tok_at' _ _ _ _ _ (by simp)
  have h3 : t[A.length + 3]! = Int.ofNat wd.length := by
    rw [ht, L3]
    exact tok_at' _ _ _ _ _ (by simp)
  have hg : tokPerms n t (A.length + 4) g.length = ((g.map (unpack n w)).toArray, A1.length) := by
    have := read_perms n w g (A ++ H) (natsI b [] ++ permsI n w s [] ++ wordsI wd [] ++ tl)
    rw [← Lg] at this
    have e : (A ++ H).length = A.length + 4 := by simp [hH]
    rw [e] at this
    rw [ht, this]
  have hb : (tokNats t A1.length b.length).toList = b := by
    have := read_nats b A1 (permsI n w s [] ++ wordsI wd [] ++ tl)
    rw [← Lb] at this
    exact this
  have hs : tokPerms n t (A1.length + b.length) s.length =
      ((s.map (unpack n w)).toArray, A3.length) := by
    have := read_perms n w s A2 (wordsI wd [] ++ tl)
    rw [← Ls] at this
    have e : A2.length = A1.length + b.length := by simp [hA2, natsI_eq]
    rw [e] at this
    rw [ht, this]
  have hw : tokWords t A3.length wd.length = (wd.toArray, (A3 ++ wordsI wd []).length) := by
    have := read_words wd A3 tl
    rw [← Lw] at this
    exact this
  have hend : (A3 ++ wordsI wd []).length = (A ++ chainI n w ⟨g, b, s, wd⟩ []).length := by
    rw [chainI_eq]
    simp [hA3, hA2, hA1, hH, natsI_eq]
  unfold tokChain
  simp only
  rw [h0, h1, h2, h3]
  have e : ∀ x : Nat, (Int.ofNat x).toNat = x := fun _ => rfl
  simp only [e]
  rw [hg]
  simp only
  rw [hb, hs]
  simp only
  rw [hw]
  simp only
  rw [hend]
  rfl

theorem toNat_ofNat (x : Nat) : (Int.ofNat x).toNat = x := rfl

theorem read_rec (n w : Nat) (r : RecP) (A tl : List Int) :
    tokRecord n (A ++ recI n w r tl).toArray A.length =
      (toRec n w r, (A ++ recI n w r []).length) := by
  obtain ⟨rp, cj, ch⟩ := r
  have hr := recI_eq n w ⟨rp, cj, ch⟩ tl
  have hr0 := recI_eq n w ⟨rp, cj, ch⟩ []
  simp only at hr hr0
  have Lf : A ++ recI n w ⟨rp, cj, ch⟩ tl =
      A ++ fldI w rp n 0 ([Int.ofNat cj.length] ++ wordsI cj [] ++ chainI n w ch [] ++ tl) := by
    rw [hr, fldI_eq w rp n 0 ([Int.ofNat cj.length] ++ wordsI cj [] ++ chainI n w ch [] ++ tl),
      fldI_eq]
    simp only [List.append_assoc, List.append_nil]
  have Lc : A ++ recI n w ⟨rp, cj, ch⟩ tl =
      (A ++ fldI w rp n 0 []) ++ Int.ofNat cj.length :: (wordsI cj [] ++ chainI n w ch [] ++ tl) := by
    rw [hr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have Lw : A ++ recI n w ⟨rp, cj, ch⟩ tl =
      (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length]) ++ wordsI cj (chainI n w ch [] ++ tl) := by
    rw [hr, wordsI_eq cj (chainI n w ch [] ++ tl)]
    simp only [List.append_assoc]
  have Lch : A ++ recI n w ⟨rp, cj, ch⟩ tl =
      (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length] ++ wordsI cj []) ++ chainI n w ch tl := by
    rw [hr, chainI_tl n w ch tl]
    simp only [List.append_assoc]
  have hl1 : (A ++ fldI w rp n 0 []).length = A.length + n := by simp [fldI_length]
  have hl2 : (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length]).length = A.length + n + 1 := by
    rw [List.length_append, List.length_append, fldI_length]
    rfl
  have hrep : tokNats (A ++ recI n w ⟨rp, cj, ch⟩ tl).toArray A.length n = unpack n w rp := by
    rw [Lf]
    exact read_fld n w rp A _
  have hc0 : (A ++ recI n w ⟨rp, cj, ch⟩ tl).toArray[A.length + n]! = Int.ofNat cj.length := by
    rw [Lc, ← hl1, tok_at]
  have hcw : tokWords (A ++ recI n w ⟨rp, cj, ch⟩ tl).toArray (A.length + n + 1) cj.length =
      (cj.toArray, (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length] ++ wordsI cj []).length) := by
    rw [Lw, ← hl2]
    exact read_words cj _ _
  have hch : tokChain n (A ++ recI n w ⟨rp, cj, ch⟩ tl).toArray
      (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length] ++ wordsI cj []).length =
      (toChain n w ch, (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length] ++ wordsI cj [] ++
        chainI n w ch []).length) := by
    rw [Lch]
    exact read_chain n w ch _ _
  have hend : (A ++ fldI w rp n 0 [] ++ [Int.ofNat cj.length] ++ wordsI cj [] ++
      chainI n w ch []).length = (A ++ recI n w ⟨rp, cj, ch⟩ []).length := by
    rw [hr0]
    simp
  unfold tokRecord
  simp only
  rw [hrep, hc0, toNat_ofNat, hcw]
  simp only
  rw [hch]
  simp only
  rw [hend]
  rfl

@[expose] def stR (n : Nat) (t : Array Int) (b : Nat × Array NGRec) (_ : Nat) : Nat × Array NGRec :=
  ((tokRecord n t b.1).2, b.2.push (tokRecord n t b.1).1)

theorem recs_fold (n w : Nat) (rs : List RecP) (A tl : List Int) (acc : Array NGRec)
    (xs : List Nat) (hx : xs.length = rs.length) :
    xs.foldl (stR n (A ++ recsI n w rs tl).toArray) (A.length, acc) =
      ((A ++ recsI n w rs []).length, acc ++ (rs.map (toRec n w)).toArray) := by
  induction rs generalizing A acc xs with
  | nil =>
    rw [List.length_eq_zero_iff.1 hx]
    simp [recsI]
  | cons r rs ih =>
    obtain ⟨a, xs, rfl⟩ : ∃ a xs', xs = a :: xs' := by
      cases xs with
      | nil => simp at hx
      | cons a xs' => exact ⟨a, xs', rfl⟩
    have hP : A ++ recsI n w (r :: rs) tl = (A ++ recI n w r []) ++ recsI n w rs tl := by
      rw [recsI_cons, List.append_assoc]
    have hP0 : A ++ recsI n w (r :: rs) [] = (A ++ recI n w r []) ++ recsI n w rs [] := by
      rw [recsI_cons, List.append_assoc]
    have hs : stR n (A ++ recsI n w (r :: rs) tl).toArray (A.length, acc) a =
        ((A ++ recI n w r []).length, acc.push (toRec n w r)) := by
      unfold stR
      have e : A ++ recsI n w (r :: rs) tl = A ++ recI n w r (recsI n w rs tl) := rfl
      rw [e, read_rec]
    rw [List.foldl_cons, hs, hP, hP0, ih _ _ _ (by simpa using hx)]
    simp

theorem read_syl (n w : Nat) (s : SylP) (A tl : List Int) :
    tokSylow n (A ++ sylI n w s tl).toArray A.length =
      (toSyl n w s, (A ++ sylI n w s []).length) := by
  obtain ⟨p, g, rs⟩ := s
  have hs := sylI_eq n w ⟨p, g, rs⟩ tl
  have hs0 := sylI_eq n w ⟨p, g, rs⟩ []
  simp only at hs hs0
  have L0 : A ++ sylI n w ⟨p, g, rs⟩ tl = A ++ Int.ofNat p :: (Int.ofNat g.length ::
      (permsI n w g [] ++ [Int.ofNat rs.length] ++ recsI n w rs [] ++ tl)) := by
    rw [hs]
    simp
  have L1 : A ++ sylI n w ⟨p, g, rs⟩ tl = A ++ [Int.ofNat p] ++ Int.ofNat g.length ::
      (permsI n w g [] ++ [Int.ofNat rs.length] ++ recsI n w rs [] ++ tl) := by
    rw [hs]
    simp
  have Lg : A ++ sylI n w ⟨p, g, rs⟩ tl = (A ++ [Int.ofNat p, Int.ofNat g.length]) ++
      permsI n w g ([Int.ofNat rs.length] ++ recsI n w rs [] ++ tl) := by
    rw [hs, permsI_eq n w g ([Int.ofNat rs.length] ++ recsI n w rs [] ++ tl)]
    simp only [List.append_assoc]
  have Ln : A ++ sylI n w ⟨p, g, rs⟩ tl = (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g []) ++
      Int.ofNat rs.length :: (recsI n w rs [] ++ tl) := by
    rw [hs]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have Lr : A ++ sylI n w ⟨p, g, rs⟩ tl = (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g [] ++
      [Int.ofNat rs.length]) ++ recsI n w rs tl := by
    rw [hs, recsI_eq n w rs tl]
    simp only [List.append_assoc]
  have h0 : (A ++ sylI n w ⟨p, g, rs⟩ tl).toArray[A.length]! = Int.ofNat p := by
    rw [L0, tok_at]
  have h1 : (A ++ sylI n w ⟨p, g, rs⟩ tl).toArray[A.length + 1]! = Int.ofNat g.length := by
    rw [L1]
    exact tok_at' _ _ _ _ _ (by simp)
  have hg : tokPerms n (A ++ sylI n w ⟨p, g, rs⟩ tl).toArray (A.length + 2) g.length =
      ((g.map (unpack n w)).toArray, (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g []).length) := by
    have e : (A ++ [Int.ofNat p, Int.ofNat g.length]).length = A.length + 2 := by simp
    rw [Lg, ← e]
    exact read_perms n w g _ _
  have hn : (A ++ sylI n w ⟨p, g, rs⟩ tl).toArray[(A ++ [Int.ofNat p, Int.ofNat g.length] ++
      permsI n w g []).length]! = Int.ofNat rs.length := by
    rw [Ln, tok_at]
  have hl : (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g []).length + 1 =
      (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g [] ++ [Int.ofNat rs.length]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hR := recs_fold n w rs (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g [] ++
    [Int.ofNat rs.length]) tl #[] (List.range' 0 rs.length) (by simp)
  rw [← Lr] at hR
  have hend : (A ++ [Int.ofNat p, Int.ofNat g.length] ++ permsI n w g [] ++ [Int.ofNat rs.length] ++
      recsI n w rs []).length = (A ++ sylI n w ⟨p, g, rs⟩ []).length := by
    rw [hs0]
    simp
  unfold tokSylow
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind]
  rw [h0, h1]
  simp only [toNat_ofNat]
  rw [hg]
  simp only
  rw [hn]
  simp only [toNat_ofNat]
  rw [hl]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  unfold stR at hR
  rw [hR, hend]
  simp only [Array.empty_append]
  rfl

@[expose] def stS (n : Nat) (t : Array Int) (b : Nat × Array SylowRec) (_ : Nat) :
    Nat × Array SylowRec :=
  ((tokSylow n t b.1).2, b.2.push (tokSylow n t b.1).1)

theorem syls_fold (n w : Nat) (ss : List SylP) (A tl : List Int) (acc : Array SylowRec)
    (xs : List Nat) (hx : xs.length = ss.length) :
    xs.foldl (stS n (A ++ sylsI n w ss tl).toArray) (A.length, acc) =
      ((A ++ sylsI n w ss []).length, acc ++ (ss.map (toSyl n w)).toArray) := by
  induction ss generalizing A acc xs with
  | nil =>
    rw [List.length_eq_zero_iff.1 hx]
    simp [sylsI]
  | cons s ss ih =>
    obtain ⟨a, xs, rfl⟩ : ∃ a xs', xs = a :: xs' := by
      cases xs with
      | nil => simp at hx
      | cons a xs' => exact ⟨a, xs', rfl⟩
    have hP : A ++ sylsI n w (s :: ss) tl = (A ++ sylI n w s []) ++ sylsI n w ss tl := by
      rw [sylsI_cons, List.append_assoc]
    have hP0 : A ++ sylsI n w (s :: ss) [] = (A ++ sylI n w s []) ++ sylsI n w ss [] := by
      rw [sylsI_cons, List.append_assoc]
    have hs : stS n (A ++ sylsI n w (s :: ss) tl).toArray (A.length, acc) a =
        ((A ++ sylI n w s []).length, acc.push (toSyl n w s)) := by
      unfold stS
      have e : A ++ sylsI n w (s :: ss) tl = A ++ sylI n w s (sylsI n w ss tl) := rfl
      rw [e, read_syl]
    rw [List.foldl_cons, hs, hP, hP0, ih _ _ _ (by simpa using hx)]
    simp

theorem parse_encSyl (n w : Nat) (ss : List SylP) :
    parseSylows n (encSyl n w ss).toArray = (ss.map (toSyl n w)).toArray := by
  have hE : encSyl n w ss = [Int.ofNat ss.length] ++ sylsI n w ss [] := by
    change Int.ofNat (lenK ss) :: sylsI n w ss [] = _
    rw [lenK_eq]
    rfl
  have h0 : (encSyl n w ss).toArray[0]! = Int.ofNat ss.length := by
    rw [hE]
    rfl
  have hS := syls_fold n w ss [Int.ofNat ss.length] [] #[] (List.range' 0 ss.length) (by simp)
  rw [← hE] at hS
  unfold parseSylows
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind]
  rw [h0, toNat_ofNat]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  unfold stS at hS
  have e1 : [Int.ofNat ss.length].length = 1 := rfl
  rw [e1] at hS
  rw [hS]
  simp only [Array.empty_append]
  rfl

theorem bAnd_tt {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem permsK_mem {n w : Nat} {Ps : List Nat} (h : permsK n w Ps = true) :
    ∀ P ∈ Ps, permK n w P = true := by
  induction Ps with
  | nil => simp
  | cons P Ps ih =>
    obtain ⟨h1, h2⟩ := bAnd_tt h
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · exact ih h2 Q hQ

theorem letterK_sound {x : Int} (h : letterK x = true) :
    (x == 1 || x == -1 || x == 2 || x == -2) = true := by
  cases x with
  | ofNat k =>
    change Bool.rec (motive := fun _ => Bool) (Nat.beq k 2) true (Nat.beq k 1) = true at h
    cases h1 : Nat.beq k 1
    · rw [h1] at h
      rw [Nat.eq_of_beq_eq_true h]
      decide
    · rw [Nat.eq_of_beq_eq_true h1]
      decide
  | negSucc k =>
    change Bool.rec (motive := fun _ => Bool) (Nat.beq k 1) true (Nat.beq k 0) = true at h
    cases h1 : Nat.beq k 0
    · rw [h1] at h
      rw [Nat.eq_of_beq_eq_true h]
      decide
    · rw [Nat.eq_of_beq_eq_true h1]
      decide

theorem letters1_sound {x : List Int}
    (h : List.rec (motive := fun _ => Bool) true (fun a _ ih2 => bAnd(letterK a, ih2)) x = true) :
    ∀ a ∈ x, (a == 1 || a == -1 || a == 2 || a == -2) = true := by
  induction x with
  | nil => simp
  | cons a y ih =>
    obtain ⟨g1, g2⟩ := bAnd_tt h
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact letterK_sound g1
    · exact ih g2 b hb

theorem lettersK_sound {ws : List (List Int)} (h : lettersK ws = true) :
    ∀ x ∈ ws, ∀ a ∈ x, (a == 1 || a == -1 || a == 2 || a == -2) = true := by
  induction ws with
  | nil => simp
  | cons x ws ih =>
    obtain ⟨h1, h2⟩ := bAnd_tt h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact letters1_sound h1
    · exact ih h2 y hy

theorem ltL_sound {n : Nat} {bs : List Nat} (h : ltL n bs = true) : ∀ b ∈ bs, b < n := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨h1, h2⟩ := bAnd_tt h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.blt_eq.mp h1
    · exact ih h2 c hc

theorem notMemK_sound {x : Nat} {l : List Nat} (h : notMemK x l = true) : x ∉ l := by
  induction l with
  | nil => simp
  | cons y l ih =>
    obtain ⟨h1, h2⟩ := bAnd_tt h
    intro hm
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [Nat.beq_refl] at h1
      exact Bool.noConfusion h1
    · exact ih h2 hm

theorem nodupK_sound {l : List Nat} (h : nodupK l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := bAnd_tt h
    exact List.nodup_cons.2 ⟨notMemK_sound h1, ih h2⟩

theorem prefK_sound : ∀ {g s : List Nat}, prefK g s = true →
    g.length ≤ s.length ∧ ∀ k (h1 : k < g.length) (h2 : k < s.length), g[k] = s[k]
  | [], s, _ => ⟨Nat.zero_le _, fun k h1 => absurd h1 (Nat.not_lt_zero k)⟩
  | a :: g, [], h => Bool.noConfusion h
  | a :: g, b :: s, h => by
    obtain ⟨h1, h2⟩ := bAnd_tt h
    obtain ⟨l, e⟩ := prefK_sound h2
    refine ⟨by simpa using l, fun k k1 k2 => ?_⟩
    rcases k with _ | k
    · exact Nat.eq_of_beq_eq_true h1
    · exact e k (by simpa using k1) (by simpa using k2)

end CFSG.KS.SporSch.PSylEnc

end
