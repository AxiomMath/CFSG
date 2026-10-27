module

public import Certificates.Data.Kernel.LocalQT.CovT
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCheck
public import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

public section

namespace CFSG.KC.LQT.Cov.T

open CFSG.KC.LQT.Cov CFSG.KC.LQT.Cov.Parse CFSG.KC.Ord CFSG.KC.LQT.Syl
open CFSG.QuasithinUnique.Ch1.TitsCover

@[expose] def ofCT (d : CT) : CovData :=
  { xw0 := d.xw.getD 0 [], xw1 := d.xw.getD 1 [], nV := d.nV,
    words := d.words.toArray, tgtA := d.tgt.toArray, backA := d.back.toArray,
    blocks := d.blocks.map fun b => { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 } }

theorem parseNats_eq (s : String) :
    parseNats s = CFSG.QuasithinUnique.Ch1.M22Cover.parseNats s := rfl

theorem natsK_sound {l : List Char} {xs : List Nat} (h : natsK l = some xs) :
    parseNats (String.ofList l) = xs := by
  rw [parseNats_eq]
  exact CFSG.KC.LQT.Cov.Parse.natsK_sound h

theorem rhoK_sound {l : List Char} {r : List (Nat × Bool)} (h : rhoK l = some r) :
    (parseNats (String.ofList l)).map (fun m => (m / 2, m % 2 == 0)) = r := by
  rw [parseNats_eq]
  exact CFSG.KC.LQT.Cov.Parse.rhoK_sound h

theorem intK_sound {l : List Char} {z : Int} (h : intK l = some z) :
    (String.ofList l).toInt? = some z := by
  cases l with
  | nil => simp [intK] at h
  | cons c cs =>
    unfold intK at h
    change Bool.rec (motive := fun _ => Option Int)
      (Option.rec (motive := fun _ => Option Int) none
        (fun m => some (Int.ofNat m)) (natK (c :: cs)))
      (Option.rec (motive := fun _ => Option Int) none
        (fun m => some (Int.neg (Int.ofNat m))) (natK cs))
      (Nat.beq (Char.toNat c) 45) = some z at h
    cases hb : Nat.beq (Char.toNat c) 45 with
    | false =>
      rw [hb] at h
      obtain ⟨m, hm, hz⟩ := orec_some h
      obtain ⟨hne, hd, hval⟩ := natK_spec hm
      have hz' : z = Int.ofNat m := (Option.some.inj hz).symm
      subst hz'
      rw [← hval]
      exact CFSG.KS.SporSch.LyTxt.tv_pos hd hne
    | true =>
      rw [hb] at h
      obtain ⟨m, hm, hz⟩ := orec_some h
      obtain ⟨hne, hd, hval⟩ := natK_spec hm
      have hc : c = '-' := by
        have e := Nat.eq_of_beq_eq_true hb
        exact Char.toNat_inj.mp (by rw [e]; rfl)
      subst hc
      have hz' : z = Int.neg (Int.ofNat m) := (Option.some.inj hz).symm
      subst hz'
      rw [← hval]
      exact CFSG.KS.SporSch.LyTxt.tv_neg hd hne

private theorem intsRec_sound : ∀ (ts : List (List Char)) (xs : List Int),
    List.rec (motive := fun _ => Option (List Int)) (some [])
      (fun t _ ih => Option.rec (motive := fun _ => Option (List Int)) none
        (fun x => Option.rec (motive := fun _ => Option (List Int)) none
          (fun xs => some (List.cons x xs)) ih) (intK t)) ts = some xs →
    ts.filterMap (fun t => (String.ofList t).toInt?) = xs
  | [], _, h => Option.some.inj h
  | t :: ts, xs, h => by
    obtain ⟨x, hx, h⟩ := orec_some h
    obtain ⟨ys, hys, h⟩ := orec_some h
    rw [← Option.some.inj h, List.filterMap_cons, intK_sound hx, intsRec_sound ts ys hys]

private theorem toInt?_nil : (String.ofList []).toInt? = none := by
  rw [String.toInt?_eq_none_iff]
  apply Bool.eq_false_iff.2
  intro h
  rw [String.isInt_iff] at h
  rcases h with h | ⟨t, ht, -⟩
  · rw [String.isNat_iff] at h
    exact h.1 rfl
  · have e := congrArg String.length ht
    have h1 : ("-" : String).length = 1 := by decide
    have h0 : (String.ofList []).length = 0 := by decide
    simp only [String.length_append, h1, h0] at e
    omega

theorem intsK_sound {l : List Char} {xs : List Int} (h : intsK l = some xs) :
    parseInts (String.ofList l) = xs := by
  unfold parseInts
  rw [sp_eq, CFSG.KC.Str.splitOn_ofList, List.filterMap_map]
  cases l with
  | nil =>
    rw [← Option.some.inj h, List.splitOn_nil, List.filterMap_cons, Function.comp_apply,
      toInt?_nil, List.filterMap_nil]
  | cons c l =>
    rw [← tokK_eq]
    exact intsRec_sound _ xs h

theorem wordTK_sound : ∀ {l : List Char} {w : List Nat}, wordTK l = some w →
    parseWord (String.ofList l) = w ∧ ∀ x ∈ w, x < 2
  | [], _, h => by
    rw [← Option.some.inj h]
    exact ⟨rfl, fun _ hx => absurd hx List.not_mem_nil⟩
  | c :: l, w, h => by
    have h' : Bool.rec (motive := fun _ => Option (List Nat)) none
        (Option.rec (motive := fun _ => Option (List Nat)) none
          (fun xs => some (List.cons (Nat.sub (Char.toNat c) 48) xs)) (wordTK l))
        (CFSG.KC.Ord.andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 49)) = some w := h
    cases hb : CFSG.KC.Ord.andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 49) with
    | false =>
      rw [hb] at h'
      cases h'
    | true =>
      rw [hb] at h'
      obtain ⟨xs, hxs, h'⟩ := orec_some h'
      obtain ⟨ih1, ih2⟩ := wordTK_sound hxs
      rw [andB_eq', Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hb
      rw [← Option.some.inj h']
      unfold parseWord at ih1 ⊢
      rw [String.toList_ofList] at ih1 ⊢
      refine ⟨?_, fun x hx => ?_⟩
      · rw [List.filterMap_cons, ih1]
        congr 1
        rcases (by omega : c.toNat = 48 ∨ c.toNat = 49) with e | e
        · rw [show c = '0' from Char.toNat_inj.1 e]
          rfl
        · rw [show c = '1' from Char.toNat_inj.1 e]
          rfl
      · rcases List.mem_cons.1 hx with rfl | hx
        · change c.toNat - 48 < 2
          omega
        · exact ih2 x hx

private noncomputable def stepBT (Ls : List (List Char)) (b : Nat × Array Blk) (_ : Nat) :
    Nat × Array Blk :=
  (b.1 + 4 + (String.ofList (getK Ls (b.1 + 3) [])).toNat!,
    b.2.push
      { gw := parseInts (String.ofList (getK Ls b.1 [])),
        va := parseNats (String.ofList (getK Ls (b.1 + 1) [])),
        vb := parseNats (String.ofList (getK Ls (b.1 + 2) [])),
        rhos := (List.foldl (fun r a => r.push (List.map (fun m => (m / 2, m % 2 == 0))
            (parseNats (String.ofList (getK Ls (b.1 + 4 + a) []))))) #[]
            (List.range' 0 (String.ofList (getK Ls (b.1 + 3) [])).toNat!)).toList })

private theorem blocksT_loop (Ls : List (List Char)) : ∀ (nb s : Nat) (st : Nat × Array Blk)
    (bs : List (List Int × List Nat × List Nat × List (List (Nat × Bool)))),
    blocksT Ls nb st.1 = some bs →
    (List.foldl (stepBT Ls) st (List.range' s nb)).2.toList =
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
    have hst : stepBT Ls (p, acc) s = (p + 4 + neq,
        acc.push { gw := gw, va := va, vb := vb, rhos := rhos }) := by
      simp only [stepBT, toNat!_natK hneq, intsK_sound hgw, natsK_sound hva, natsK_sound hvb,
        foldl_push_toList, hr']
      simp
    have hrest' : blocksT Ls nb (stepBT Ls (p, acc) s).1 = some rest := by
      rw [hst, Nat.add_assoc]
      exact hrest
    rw [← Option.some.inj h, List.range'_succ, List.foldl_cons,
      blocksT_loop Ls nb (s + 1) _ rest hrest', hst]
    simp

theorem parseT_sound {cs : List Char} {D : CT} (h : parseT cs = some D) :
    D.xw.length = 2 ∧ D.words.length = D.nV ∧ (∀ w ∈ D.words, ∀ l ∈ w, l < 2) ∧
    parseData (String.ofList cs) = ofCT D := by
  unfold parseT at h
  obtain ⟨xw, hxw, h⟩ := orec_some h
  obtain ⟨nV, hnV, h⟩ := orec_some h
  obtain ⟨words, hwords, h⟩ := orec_some h
  obtain ⟨tgt, htgt, h⟩ := orec_some h
  obtain ⟨back, hback, h⟩ := orec_some h
  obtain ⟨nb, hnb, h⟩ := orec_some h
  obtain ⟨blocks, hblocks, h⟩ := orec_some h
  obtain rfl := Option.some.inj h
  simp only [Nat.add_eq] at htgt hback hnb hblocks
  have hX := (manyK_spec (linesK cs) intsK (fun l => parseInts (String.ofList l))
    (fun _ _ h => intsK_sound h) 2 0 xw hxw).1
  have hW := manyK_spec (linesK cs) wordTK (fun l => parseWord (String.ofList l))
    (fun _ _ h => (wordTK_sound h).1) nV 3 words hwords
  have hB := blocksT_loop (linesK cs) nb 0 (6 + nV, #[]) blocks hblocks
  have hL : (String.ofList cs).splitOn "\n" = (linesK cs).map String.ofList := by
    rw [nl_eq, CFSG.KC.Str.splitOn_ofList, linesK_eq]
  refine ⟨by rw [← hX]; simp, by rw [← hW.1]; simp, fun w hw x hx => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := hW.2 w hw
    exact (wordTK_sound hl).2 x hx
  have hx0 : parseInts (String.ofList (getK (linesK cs) 0 [])) = xw.getD 0 [] := by
    rw [← hX]
    rfl
  have hx1 : parseInts (String.ofList (getK (linesK cs) 1 [])) = xw.getD 1 [] := by
    rw [← hX]
    rfl
  have hw : Array.map (fun v => parseWord (String.ofList (getK (linesK cs) (3 + v) [])))
      (Array.range nV) = words.toArray := by
    rw [← hW.1, range'_shift 3, List.map_map]
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_range, List.range_eq_range']
    rfl
  have hb : List.map (fun b => { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 }) blocks
      = (List.foldl (stepBT (linesK cs)) (6 + nV, #[]) (List.range' 0 nb)).2.toList := by
    rw [hB]
    simp
  simp only [parseData, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, pure_bind, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Id.run_pure, hL, getElem!_lines, toNat!_natK hnV,
    toNat!_natK hnb, natsK_sound htgt, natsK_sound hback, hx0, hx1, hw, hb, ofCT]
  rfl

private noncomputable def rowGo {α : Type} (l : List α) (k : Nat) (cur : List α) :
    List (List α) :=
  List.rec (motive := fun _ => Nat → List α → List (List α))
    (fun _ cur => [List.reverse cur])
    (fun x _ ih k cur => Bool.rec (motive := fun _ => List (List α))
      (ih (Nat.succ k) (List.cons x cur))
      (List.cons (List.reverse (List.cons x cur)) (ih 0 [])) (Nat.beq k 63)) l k cur

private theorem rowsG_eq_rowGo {α : Type} (l : List α) : rowsG l = rowGo l 0 [] := rfl

private theorem rowGo_short {α : Type} :
    ∀ (l : List α) (k : Nat) (cur : List α),
      k = cur.length → k + l.length < 64 → rowGo l k cur = [List.reverse cur ++ l]
  | [], k, cur, _, _ => by
    simp [rowGo]
  | x :: l, k, cur, hk, h => by
    simp only [List.length_cons] at h
    have hk63 : k ≠ 63 := by omega
    have hb : Nat.beq k 63 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hk63 (Nat.eq_of_beq_eq_true h)
    have e : rowGo (x :: l) k cur = rowGo l (k + 1) (x :: cur) := by
      change Bool.rec (motive := fun _ => List (List α))
        (rowGo l (k + 1) (x :: cur))
        (List.reverse (x :: cur) :: rowGo l 0 []) (Nat.beq k 63) = _
      rw [hb]
    rw [e, rowGo_short l (k + 1) (x :: cur) (by simp [hk]) (by omega)]
    simp [List.reverse_cons, List.append_assoc]

private theorem rowGo_prefix {α : Type} :
    ∀ (a b : List α) (k : Nat) (cur : List α),
      k + a.length = 64 → k < 64 →
        rowGo (a ++ b) k cur = [List.reverse cur ++ a] ++ rowGo b 0 []
  | [], b, k, cur, hk, hklt => by simp at hk; omega
  | x :: a, b, k, cur, hk, hklt => by
    by_cases hk63 : k = 63
    · obtain rfl : a = [] := by
        cases a with
        | nil => rfl
        | cons y ys => simp only [List.length_cons] at hk; omega
      subst hk63
      have e : rowGo (x :: b) 63 cur =
          List.reverse (x :: cur) :: rowGo b 0 [] := by
        change Bool.rec (motive := fun _ => List (List α))
          (rowGo b 64 (x :: cur))
          (List.reverse (x :: cur) :: rowGo b 0 []) (Nat.beq 63 63) = _
        rfl
      rw [List.singleton_append, e]
      simp [List.reverse_cons, List.append_assoc]
    · have hklt' : k < 63 := by omega
      have hb : Nat.beq k 63 = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact hk63 (Nat.eq_of_beq_eq_true h)
      have hk' : k + 1 + a.length = 64 := by
        simp only [List.length_cons] at hk
        omega
      have e : rowGo ((x :: a) ++ b) k cur = rowGo (a ++ b) (k + 1) (x :: cur) := by
        rw [List.cons_append]
        change Bool.rec (motive := fun _ => List (List α))
          (rowGo (a ++ b) (k + 1) (x :: cur))
          (List.reverse (x :: cur) :: rowGo (a ++ b) 0 []) (Nat.beq k 63) = _
        rw [hb]
      rw [e, rowGo_prefix a b (k + 1) (x :: cur) hk' (by omega)]
      simp [List.reverse_cons, List.append_assoc]

private theorem rowsG_eq_short {α : Type} (l : List α) (h : l.length < 64) :
    rowsG l = [l] := by
  rw [rowsG_eq_rowGo]
  have := rowGo_short l 0 [] rfl (by simpa using h)
  simpa using this

private theorem rowsG_eq_long {α : Type} (l : List α) (h : 64 ≤ l.length) :
    rowsG l = l.take 64 :: rowsG (l.drop 64) := by
  have htake : (l.take 64).length = 64 := by
    rw [List.length_take]
    omega
  have hp := rowGo_prefix (l.take 64) (l.drop 64) 0 [] (by simp [htake]) (by omega)
  rw [List.take_append_drop] at hp
  rw [rowsG_eq_rowGo, rowsG_eq_rowGo]
  simpa [htake] using hp

theorem getRG_rowsG_lt {α : Type} (l : List α) (i : Nat) (d : α) (hi : i < l.length) :
    getRG (rowsG l) i d = l.getD i d := by
  revert l d
  refine Nat.strong_induction_on i ?_
  intro i ih l d hi
  by_cases hshort : l.length < 64
  · have hrow := rowsG_eq_short l hshort
    have hi64 : i < 64 := by omega
    have hdiv : Nat.div i 64 = 0 := Nat.div_eq_of_lt hi64
    have hmod : Nat.mod i 64 = i := Nat.mod_eq_of_lt hi64
    rw [getRG, hrow, hdiv, hmod]
    simp [getK_getD]
  · have hlong : 64 ≤ l.length := by omega
    have hrow := rowsG_eq_long l hlong
    by_cases hi64 : i < 64
    · rw [getRG, hrow, show Nat.div i 64 = 0 from Nat.div_eq_of_lt hi64,
        show Nat.mod i 64 = i from Nat.mod_eq_of_lt hi64]
      simp only [getK_getD, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        Option.getD_some, List.getElem?_take, if_pos hi64]
    · have hi64' : 64 ≤ i := by omega
      let j := i - 64
      have hji : i = j + 64 := by omega
      have hjlt : j < (l.drop 64).length := by
        rw [List.length_drop]
        omega
      have hdiv : Nat.div i 64 = Nat.div j 64 + 1 :=
        Nat.div_eq_sub_div (by omega : 0 < 64) (by omega : 64 ≤ i)
      have hmod : Nat.mod i 64 = Nat.mod j 64 := by
        have := Nat.add_mul_mod_self_left (i - 64) 64 1
        rw [Nat.mul_one] at this
        rw [show i = (i - 64) + 64 by omega]
        exact this
      rw [getRG, hrow, hdiv, hmod]
      have e : getK (getK (l.take 64 :: rowsG (l.drop 64)) (Nat.div j 64 + 1) [])
          (Nat.mod j 64) d = getRG (rowsG (l.drop 64)) j d := by
        rw [getK_getD, getK_getD, List.getD_cons_succ, getRG, getK_getD, getK_getD]
      rw [e, ih j (by omega) (l.drop 64) d hjlt]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [show 64 + j = i by omega]



private theorem getK_singleton_ne {α : Type} (x : α) (d : α) {q : Nat} (hq : q ≠ 0) :
    getK [x] q d = d := by
  rw [getK_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
  rfl

theorem getRG_rowsG {α : Type} (l : List α) (i : Nat) (d : α) :
    getRG (rowsG l) i d = l.getD i d := by
  revert l d
  refine Nat.strong_induction_on i ?_
  intro i ih l d
  by_cases hshort : l.length < 64
  · have hrow := rowsG_eq_short l hshort
    rw [getRG, hrow]
    by_cases hq : Nat.div i 64 = 0
    · rw [hq, show Nat.mod i 64 = i from by
        have : i < 64 := by
          by_contra h
          have : 1 ≤ Nat.div i 64 := Nat.div_pos (by omega) (by omega)
          omega
        exact Nat.mod_eq_of_lt this]
      have h0 : getK [l] 0 [] = l := by rw [getK_getD]; rfl
      rw [h0, getK_getD]
    · have hq0 : Nat.div i 64 ≠ 0 := hq
      rw [getK_singleton_ne _ _ hq0]
      have hlen : l.length ≤ i := by
        by_contra h
        have : i < 64 := by omega
        exact hq (Nat.div_eq_of_lt this)
      show d = l.getD i d
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
  · have hlong : 64 ≤ l.length := by omega
    have hrow := rowsG_eq_long l hlong
    by_cases hi64 : i < 64
    · rw [getRG, hrow, show Nat.div i 64 = 0 from Nat.div_eq_of_lt hi64,
        show Nat.mod i 64 = i from Nat.mod_eq_of_lt hi64]
      simp only [getK_getD, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        Option.getD_some, List.getElem?_take, if_pos hi64]
    · have hi64' : 64 ≤ i := by omega
      let j := i - 64
      have hji : i = j + 64 := by omega
      have hdiv : Nat.div i 64 = Nat.div j 64 + 1 :=
        Nat.div_eq_sub_div (by omega : 0 < 64) (by omega : 64 ≤ i)
      have hmod : Nat.mod i 64 = Nat.mod j 64 := by
        have := Nat.add_mul_mod_self_left (i - 64) 64 1
        rw [Nat.mul_one] at this
        rw [show i = (i - 64) + 64 by omega]
        exact this
      rw [getRG, hrow, hdiv, hmod]
      have e : getK (getK (l.take 64 :: rowsG (l.drop 64)) (Nat.div j 64 + 1) [])
          (Nat.mod j 64) d = getRG (rowsG (l.drop 64)) j d := by
        rw [getK_getD, getK_getD, List.getD_cons_succ, getRG, getK_getD, getK_getD]
      rw [e, ih j (by omega) (l.drop 64) d]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [show 64 + j = i by omega]

end CFSG.KC.LQT.Cov.T

end
