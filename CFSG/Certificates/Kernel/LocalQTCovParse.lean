module

public import Certificates.Data.Kernel.LocalQT.Cov
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck
import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.LQT.Cov.Parse

open CFSG.KC.Ord CFSG.KC.LQT.Syl CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.M22Cover

theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq' (a : Bool) : notB a = !a := by cases a <;> rfl

theorem lenK_length {α : Type} : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenK_length l)

theorem getK_getD {α : Type} : ∀ (l : List α) (i : Nat) (d : α), getK l i d = l.getD i d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, d => getK_getD l i d

theorem orec_some {α β : Type} {o : Option α} {f : α → Option β} {y : β}
    (h : Option.rec (motive := fun _ => Option β) none f o = some y) :
    ∃ x, o = some x ∧ f x = some y := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

theorem brec_some {β : Type} {b : Bool} {x y : β}
    (h : Bool.rec (motive := fun _ => Option β) none (some x) b = some y) : x = y := by
  cases b with
  | false => cases h
  | true => exact Option.some.inj h

private theorem beq_nat (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

private theorem splitRec_eq (q : Char → Bool) : ∀ (cs cur : List Char),
    List.rec (motive := fun _ => List Char → List (List Char)) (fun cur => [List.reverse cur])
      (fun c _ ih cur => Bool.rec (motive := fun _ => List (List Char)) (ih (List.cons c cur))
        (List.cons (List.reverse cur) (ih [])) (q c)) cs cur =
    List.splitOnPPrepend q cs cur
  | [], _ => List.splitOnPPrepend_nil.symm
  | c :: cs, cur => by
    rw [List.splitOnPPrepend_cons_eq_ite]
    dsimp only
    cases q c with
    | false =>
      rw [if_neg Bool.false_ne_true]
      exact splitRec_eq q cs (c :: cur)
    | true =>
      rw [if_pos rfl, List.splitOnP_eq_splitOnPPrepend]
      exact congrArg (List.cons cur.reverse) (splitRec_eq q cs [])

private theorem nl_beq (c : Char) : Nat.beq c.toNat 10 = (c == '\n') := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq, ← Char.toNat_inj]
  exact Iff.rfl

private theorem sp_beq (c : Char) : Nat.beq c.toNat 32 = (c == ' ') := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq, ← Char.toNat_inj]
  exact Iff.rfl

theorem linesK_eq (cs : List Char) : linesK cs = cs.splitOn '\n' := by
  have e := splitRec_eq (fun c => Nat.beq c.toNat 10) cs []
  rw [show (fun c : Char => Nat.beq c.toNat 10) = (· == '\n') from funext nl_beq] at e
  rw [List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]
  exact e

theorem tokK_eq (l : List Char) : tokK l = l.splitOn ' ' := by
  have e := splitRec_eq (fun c => Nat.beq c.toNat 32) l []
  rw [show (fun c : Char => Nat.beq c.toNat 32) = (· == ' ') from funext sp_beq] at e
  rw [List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]
  exact e

theorem sp_eq : (" " : String) = String.singleton ' ' := by decide

theorem nl_eq : ("\n" : String) = String.singleton '\n' := by decide

theorem getElem!_lines (Ls : List (List Char)) (i : Nat) :
    (Ls.map String.ofList).toArray[i]! = String.ofList (getK Ls i []) := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map, getK_getD,
    List.getD_eq_getElem?_getD]
  cases Ls[i]? with
  | none => exact String.ofList_nil.symm
  | some l => rfl

private theorem digK_eq (c : Char) : digK c = c.isDigit := by
  rw [Bool.eq_iff_iff, digK, andB_eq', Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq,
    Char.isDigit_iff_toNat]
  exact Iff.rfl

private theorem allDig_eq : ∀ l : List Char,
    List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (digK c) ih) l =
      l.all fun c => c.isDigit
  | [] => rfl
  | c :: l => by
    rw [List.all_cons, ← allDig_eq l, ← digK_eq, ← andB_eq']

private theorem valRec_eq : ∀ (l : List Char) (acc : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun c _ ih acc => ih (Nat.add (Nat.mul 10 acc) (Nat.sub (Char.toNat c) 48))) l acc =
      Nat.ofDigitChars 10 l acc
  | [], _ => Nat.ofDigitChars_nil.symm
  | c :: l, acc => by
    rw [Nat.ofDigitChars_cons]
    exact valRec_eq l _

private theorem ofDigitChars_decVal (l : List Char) :
    Nat.ofDigitChars 10 l 0 = CFSG.KC.Str.decVal l := by
  rw [Nat.ofDigitChars_eq_foldl]
  exact CFSG.KC.Str.foldl_congr _ _ l 0 fun c _ n => by rw [Nat.mul_comm]; rfl

theorem natK_spec {l : List Char} {v : Nat} (h : natK l = some v) :
    l ≠ [] ∧ (∀ c ∈ l, c.isDigit = true) ∧ Nat.ofDigitChars 10 l 0 = v := by
  unfold natK at h
  cases hb : andB (notB (Nat.beq (lenK l) 0))
      (List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (digK c) ih) l) with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    rw [andB_eq', notB_eq', allDig_eq, lenK_length, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at hb
    refine ⟨fun hl => ?_, hb.2, ?_⟩
    · subst hl
      exact absurd hb.1 (by decide)
    · rw [← valRec_eq]
      exact Option.some.inj h

theorem toNat?_natK {l : List Char} {v : Nat} (h : natK l = some v) :
    (String.ofList l).toNat? = some v := by
  obtain ⟨hne, hd, rfl⟩ := natK_spec h
  have hn : (String.ofList l).isNat = true :=
    String.isNat_of_isDigit (by simpa using hne) (by simpa using hd)
  rw [String.toNat?_eq_some_ofDigitChars hn, String.toList_ofList,
    List.filter_eq_self.2 fun c hc => by simpa using CFSG.KC.Str.ne_underscore (hd c hc)]

theorem toNat!_natK {l : List Char} {v : Nat} (h : natK l = some v) :
    (String.ofList l).toNat! = v := by
  obtain ⟨hne, hd, rfl⟩ := natK_spec h
  rw [CFSG.KC.Str.toNat!_ofList hne hd, ofDigitChars_decVal]

private theorem toNat?_nil : (String.ofList []).toNat? = none :=
  String.toNat?_eq_none (Bool.eq_false_iff.2 fun h => (String.isNat_iff.1 h).1 String.ofList_nil)

private theorem natsRec_sound : ∀ (ts : List (List Char)) (xs : List Nat),
    List.rec (motive := fun _ => Option (List Nat)) (some [])
      (fun t _ ih => Option.rec (motive := fun _ => Option (List Nat)) none
        (fun x => Option.rec (motive := fun _ => Option (List Nat)) none
          (fun xs => some (List.cons x xs)) ih) (natK t)) ts = some xs →
    ts.filterMap (fun t => (String.ofList t).toNat?) = xs
  | [], _, h => Option.some.inj h
  | t :: ts, xs, h => by
    obtain ⟨x, hx, h⟩ := orec_some h
    obtain ⟨ys, hys, h⟩ := orec_some h
    rw [← Option.some.inj h, List.filterMap_cons, toNat?_natK hx, natsRec_sound ts ys hys]

theorem natsK_sound {l : List Char} {xs : List Nat} (h : natsK l = some xs) :
    parseNats (String.ofList l) = xs := by
  unfold parseNats
  rw [sp_eq, CFSG.KC.Str.splitOn_ofList, List.filterMap_map]
  cases l with
  | nil =>
    rw [← Option.some.inj h, List.splitOn_nil, List.filterMap_cons, Function.comp_apply,
      toNat?_nil, List.filterMap_nil]
  | cons c l =>
    rw [← tokK_eq]
    exact natsRec_sound _ xs h

theorem rhoK_sound {l : List Char} {r : List (Nat × Bool)} (h : rhoK l = some r) :
    (parseNats (String.ofList l)).map (fun m => (m / 2, m % 2 == 0)) = r := by
  obtain ⟨xs, hxs, h⟩ := orec_some h
  rw [natsK_sound hxs, ← Option.some.inj h]
  exact List.map_congr_left fun m _ => by rw [beq_nat]; rfl

private theorem letter_eq {c : Char} (h1 : 48 ≤ c.toNat) (h2 : c.toNat ≤ 50) :
    (if c = '0' then some 0 else if c = '1' then some 1 else if c = '2' then some 2 else none) =
      some (c.toNat - 48) := by
  rcases (by omega : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50) with e | e | e
  · rw [show c = '0' from Char.toNat_inj.1 e]
    rfl
  · rw [show c = '1' from Char.toNat_inj.1 e]
    rfl
  · rw [show c = '2' from Char.toNat_inj.1 e]
    rfl

theorem wordK_sound : ∀ {l : List Char} {w : List Nat}, wordK l = some w →
    parseWord (String.ofList l) = w ∧ ∀ x ∈ w, x < 3
  | [], _, h => by
    rw [← Option.some.inj h]
    exact ⟨rfl, fun _ hx => absurd hx List.not_mem_nil⟩
  | c :: l, w, h => by
    have h' : Bool.rec (motive := fun _ => Option (List Nat)) none
        (Option.rec (motive := fun _ => Option (List Nat)) none
          (fun xs => some (List.cons (Nat.sub (Char.toNat c) 48) xs)) (wordK l))
        (andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 50)) = some w := h
    cases hb : andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 50) with
    | false =>
      rw [hb] at h'
      cases h'
    | true =>
      rw [hb] at h'
      obtain ⟨xs, hxs, h'⟩ := orec_some h'
      obtain ⟨ih1, ih2⟩ := wordK_sound hxs
      rw [andB_eq', Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hb
      rw [← Option.some.inj h']
      unfold parseWord at ih1 ⊢
      rw [String.toList_ofList] at ih1 ⊢
      refine ⟨?_, fun x hx => ?_⟩
      · rw [List.filterMap_cons, letter_eq hb.1 hb.2, ih1]
        rfl
      · rcases List.mem_cons.1 hx with rfl | hx
        · change c.toNat - 48 < 3
          omega
        · exact ih2 x hx

private theorem manyK_succ {α : Type} (L : List (List Char)) (f : List Char → Option α)
    (a k : Nat) :
    manyK L f a (k + 1) = Option.rec (motive := fun _ => Option (List α)) none
      (fun x => Option.rec (motive := fun _ => Option (List α)) none
        (fun xs => some (x :: xs)) (manyK L f (a + 1) k)) (f (getK L a [])) := rfl

theorem manyK_spec {α : Type} (L : List (List Char)) (f : List Char → Option α)
    (g : List Char → α) (hfg : ∀ l x, f l = some x → g l = x) :
    ∀ (k a : Nat) (xs : List α), manyK L f a k = some xs →
      (List.range' a k).map (fun i => g (getK L i [])) = xs ∧ ∀ x ∈ xs, ∃ l, f l = some x
  | 0, _, _, h => by
    rw [← Option.some.inj h]
    exact ⟨rfl, fun _ hx => absurd hx List.not_mem_nil⟩
  | k + 1, a, xs, h => by
    rw [manyK_succ] at h
    obtain ⟨x, hx, h⟩ := orec_some h
    obtain ⟨ys, hys, h⟩ := orec_some h
    obtain ⟨ih1, ih2⟩ := manyK_spec L f g hfg k (a + 1) ys hys
    rw [← Option.some.inj h, List.range'_succ, List.map_cons, ih1, hfg _ _ hx]
    refine ⟨rfl, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, hx⟩
    · exact ih2 y hy

theorem range'_shift (a n : Nat) :
    List.range' a n = (List.range' 0 n).map (a + ·) := by
  rw [List.range'_eq_map_range, List.range_eq_range']

theorem foldl_push_toList {α β : Type} (g : α → β) : ∀ (l : List α) (acc : Array β),
    (l.foldl (fun r a => r.push (g a)) acc).toList = acc.toList ++ l.map g
  | [], acc => by simp
  | a :: l, acc => by
    rw [List.foldl_cons, foldl_push_toList g l, Array.toList_push, List.map_cons,
      List.append_assoc]
    rfl

private noncomputable def stepB (Ls : List (List Char)) (b : Nat × Array Blk) (_ : Nat) :
    Nat × Array Blk :=
  (b.1 + 4 + (String.ofList (getK Ls (b.1 + 3) [])).toNat!,
    b.2.push
      { gw := parseNats (String.ofList (getK Ls b.1 [])),
        va := parseNats (String.ofList (getK Ls (b.1 + 1) [])),
        vb := parseNats (String.ofList (getK Ls (b.1 + 2) [])),
        rhos := (List.foldl (fun r a => r.push (List.map (fun m => (m / 2, m % 2 == 0))
            (parseNats (String.ofList (getK Ls (b.1 + 4 + a) []))))) #[]
            (List.range' 0 (String.ofList (getK Ls (b.1 + 3) [])).toNat!)).toList })

private theorem blocks_loop (Ls : List (List Char)) : ∀ (nb s : Nat) (st : Nat × Array Blk)
    (bs : List (List Nat × List Nat × List Nat × List (List (Nat × Bool)))),
    blocksK Ls nb st.1 = some bs →
    (List.foldl (stepB Ls) st (List.range' s nb)).2.toList =
      st.2.toList ++ bs.map fun b => { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 }
  | 0, _, _, _, h => by
    rw [← Option.some.inj h]
    simp
  | nb + 1, s, (p, acc), bs, h => by
    obtain ⟨gw, hgw, h⟩ := orec_some h
    obtain ⟨va, hva, h⟩ := orec_some h
    obtain ⟨vb, hvb, h⟩ := orec_some h
    obtain ⟨neq, hneq, h⟩ := orec_some h
    obtain ⟨rhos, hrhos, h⟩ := orec_some h
    obtain ⟨rest, hrest, h⟩ := orec_some h
    simp only [Nat.add_eq] at hgw hva hvb hneq hrhos hrest
    have hr := (manyK_spec Ls rhoK _ (fun _ _ h => rhoK_sound h) neq (p + 4) rhos hrhos).1
    have hr' : (List.range' 0 neq).map (fun a => List.map (fun m => (m / 2, m % 2 == 0))
        (parseNats (String.ofList (getK Ls (p + 4 + a) [])))) = rhos := by
      rw [← hr, range'_shift (p + 4), List.map_map]
      rfl
    have hst : stepB Ls (p, acc) s = (p + 4 + neq,
        acc.push { gw := gw, va := va, vb := vb, rhos := rhos }) := by
      simp only [stepB, toNat!_natK hneq, natsK_sound hgw, natsK_sound hva, natsK_sound hvb,
        foldl_push_toList, hr']
      simp
    have hrest' : blocksK Ls nb (stepB Ls (p, acc) s).1 = some rest := by
      rw [hst, Nat.add_assoc]
      exact hrest
    rw [← Option.some.inj h, List.range'_succ, List.foldl_cons,
      blocks_loop Ls nb (s + 1) _ rest hrest', hst]
    simp

theorem parseCov_sound {cs : List Char} {D : CD} (h : parseCov cs = some D) :
    D.xw.length = 3 ∧ D.words.length = D.nV ∧ (∀ w ∈ D.words, ∀ l ∈ w, l < 3) ∧
    parseData (String.ofList cs) =
      { xw0 := D.xw.getD 0 [], xw1 := D.xw.getD 1 [], xw2 := D.xw.getD 2 [], nV := D.nV,
        words := D.words.toArray, tgtA := D.tgt.toArray, backA := D.back.toArray,
        free := D.free,
        blocks := D.blocks.map fun b =>
          { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 } } := by
  unfold parseCov at h
  obtain ⟨xw, hxw, h⟩ := orec_some h
  obtain ⟨nV, hnV, h⟩ := orec_some h
  obtain ⟨words, hwords, h⟩ := orec_some h
  obtain ⟨tgt, htgt, h⟩ := orec_some h
  obtain ⟨back, hback, h⟩ := orec_some h
  obtain ⟨free, hfree, h⟩ := orec_some h
  obtain ⟨nb, hnb, h⟩ := orec_some h
  obtain ⟨blocks, hblocks, h⟩ := orec_some h
  obtain rfl := brec_some h
  simp only [Nat.add_eq] at htgt hback hfree hnb hblocks
  have hX := (manyK_spec (linesK cs) natsK (fun l => parseNats (String.ofList l))
    (fun _ _ h => natsK_sound h) 3 0 xw hxw).1
  have hW := manyK_spec (linesK cs) wordK (fun l => parseWord (String.ofList l))
    (fun _ _ h => (wordK_sound h).1) nV 4 words hwords
  have hB := blocks_loop (linesK cs) nb 0 (8 + nV, #[]) blocks hblocks
  have hL : (String.ofList cs).splitOn "\n" = (linesK cs).map String.ofList := by
    rw [nl_eq, CFSG.KC.Str.splitOn_ofList, linesK_eq]
  refine ⟨by rw [← hX]; simp, by rw [← hW.1]; simp, fun w hw x hx => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := hW.2 w hw
    exact (wordK_sound hl).2 x hx
  have hx0 : parseNats (String.ofList (getK (linesK cs) 0 [])) = xw.getD 0 [] := by
    rw [← hX]
    rfl
  have hx1 : parseNats (String.ofList (getK (linesK cs) 1 [])) = xw.getD 1 [] := by
    rw [← hX]
    rfl
  have hx2 : parseNats (String.ofList (getK (linesK cs) 2 [])) = xw.getD 2 [] := by
    rw [← hX]
    rfl
  have hw : Array.map (fun v => parseWord (String.ofList (getK (linesK cs) (4 + v) [])))
      (Array.range nV) = words.toArray := by
    rw [← hW.1, range'_shift 4, List.map_map]
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_range, List.range_eq_range']
    rfl
  have hb : List.map (fun b => { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 }) blocks
      = (List.foldl (stepB (linesK cs)) (8 + nV, #[]) (List.range' 0 nb)).2.toList := by
    rw [hB]
    simp
  simp only [parseData, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, pure_bind, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Id.run_pure, hL, getElem!_lines, toNat!_natK hnV,
    toNat!_natK hnb, natsK_sound htgt, natsK_sound hback, natsK_sound hfree, hx0, hx1, hx2, hw,
    hb]
  rfl

end CFSG.KC.LQT.Cov.Parse

end
