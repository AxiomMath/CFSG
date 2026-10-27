module

public import Certificates.Data.Kernel.M24G.StmtB
public import CFSG.Certificates.Kernel.M24G.GeomFacts
public import Mathlib.Algebra.Order.Ring.Nat

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem getD_evensL {α : Type} (d : α) : ∀ (l : List α) (k : Nat),
    (evensL l).getD k d = l.getD (2 * k) d
  | [], k => by simp [evensL]
  | [x], 0 => by simp [evensL]
  | [x], k + 1 => by simp [evensL, Nat.mul_succ]
  | x :: y :: l, 0 => by simp [evensL]
  | x :: y :: l, k + 1 => by
    rw [evensL, Nat.mul_succ, List.getD_cons_succ, getD_evensL d l k]
    simp

theorem getD_oddsL {α : Type} (d : α) : ∀ (l : List α) (k : Nat),
    (oddsL l).getD k d = l.getD (2 * k + 1) d
  | [], k => by simp [oddsL]
  | [x], k => by simp [oddsL]
  | x :: y :: l, 0 => by simp [oddsL]
  | x :: y :: l, k + 1 => by
    rw [oddsL, List.getD_cons_succ, getD_oddsL d l k, Nat.mul_succ]
    simp

theorem length_evensL {α : Type} : ∀ l : List α, (evensL l).length ≤ (l.length + 1) / 2
  | [] => by simp [evensL]
  | [x] => by simp [evensL]
  | x :: y :: l => by
    have := length_evensL l
    simp only [evensL, List.length_cons]
    omega

theorem length_oddsL {α : Type} : ∀ l : List α, (oddsL l).length ≤ l.length / 2
  | [] => by simp [oddsL]
  | [x] => by simp [oddsL]
  | x :: y :: l => by
    have := length_oddsL l
    simp only [oddsL, List.length_cons]
    omega

theorem getT_ofListT {α : Type} [Inhabited α] : ∀ (n : Nat) (L : List α), L.length ≤ n →
    ∀ i, getT (ofListT n L) i = L.getD i default
  | 0, L, h, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]
    simp [ofListT, getT]
  | n + 1, [], _, i => by simp [ofListT, getT]
  | n + 1, x :: l, h, 0 => by simp [ofListT, getT]
  | n + 1, x :: l, h, i + 1 => by
    simp only [List.length_cons] at h
    have he := length_evensL l
    have ho := length_oddsL l
    simp only [ofListT, getT, List.getD_cons_succ]
    split
    · rw [getT_ofListT n _ (by omega), getD_evensL]
      congr 1
      omega
    · rw [getT_ofListT n _ (by omega), getD_oddsL]
      congr 1
      omega

theorem getT_treeOf {α : Type} [Inhabited α] (L : List α) (i : Nat) :
    getT (treeOf L) i = L.getD i default :=
  getT_ofListT L.length L (Nat.le_refl _) i

theorem trK_eq (TL : List (Nat × Nat × Nat)) (p : Nat) : trK TL p = TL.getD p default :=
  getT_treeOf TL p

theorem tsK_eq (TS : List (List Nat)) (p : Nat) : tsK TS p = TS.getD p default :=
  getT_treeOf TS p

theorem slK_eq (SL : List (List Nat)) (q : Nat) : slK SL q = SL.getD q default :=
  getT_treeOf SL q

theorem piCheck_eq_piG (Ts : Array (List Nat)) (l m : Nat) :
    Native.piCheck Ts l m = piG (fun i => Ts[i]!) (fun i => (Native.trioList ())[i]!)
      Native.oneIn Native.octIn
      (fun l m => (List.range Native.nTrio).filter fun k =>
        Native.coplanar Ts l k && Native.coplanar Ts m k)
      (fun π y => (List.range Native.nTrio).filter fun k =>
        Ts[k]!.contains π && (Native.octsT (Native.trioList ())[k]!).contains y)
      (fun x y => Native.trioIdx (Native.sort3 x y (Native.full ^^^ x ^^^ y))) l m :=
  rfl

theorem piG_ix_congr {ts : Nat → List Nat} {tr : Nat → Nat × Nat × Nat} {oi : Nat → Nat → Bool}
    {oc : Nat → Nat → Nat} {co : Nat → Nat → List Nat} {pen : Nat → Nat → List Nat}
    {ix ix' : Nat → Nat → Nat} {l m : Nat} (h : ∀ a b, ix (oc l a) (oc m b) = ix' (oc l a) (oc m b)) :
    piG ts tr oi oc co pen ix l m = piG ts tr oi oc co pen ix' l m := by
  unfold piG
  split
  · simp only [h]
  · rfl

theorem stmt313Check_eq_G : Native.stmt313Check () =
    stmt313G (fun i => (Native.trioList ())[i]!) Native.oneIn
      (Native.sextTrios (Native.trioSexts ()) 0)
      (fun m => (List.range Native.nTrio).any fun k =>
        (!(Native.meets (Native.trioList ())[0]! (Native.trioList ())[k]!) &&
          Native.coplanar (Native.trioSexts ()) 0 k) &&
        (!(Native.meets (Native.trioList ())[m]! (Native.trioList ())[k]!) &&
          Native.coplanar (Native.trioSexts ()) m k)) :=
  rfl

section Rec

variable {TL : List (Nat × Nat × Nat)} {TS SL : List (List Nat)}
  (hT : Native.trioList () = TL.toArray) (hTS : Native.trioSexts () = TS.toArray)
  (hS : Native.sextList () = SL.toArray) (hTl : TL.length = Native.nTrio)
  (hpos : posOK Native.key3 TL (posTree Native.key3 TL) = true)
  (hlt : TL.all (fun t => (Native.octsT t).all (· < 2 ^ 24)) = true)

include hT in
theorem trioList_lookup : (fun i => (Native.trioList ())[i]!) = trK TL := by
  funext i
  rw [hT, toArray_getElem!_eq_getD, trK_eq]

theorem trioSexts_lookup : (fun i => TS.toArray[i]!) = tsK TS := by
  funext i
  rw [toArray_getElem!_eq_getD, tsK_eq]

include hT hS in
theorem oneIn_eq : Native.oneIn = oiK TL SL := by
  funext p q
  unfold Native.oneIn oiK octsInK
  rw [hT, hS, toArray_getElem!_eq_getD, toArray_getElem!_eq_getD, trK_eq, slK_eq]

include hT hS in
theorem octIn_eq : Native.octIn = ocK TL SL := by
  funext p q
  unfold Native.octIn ocK octsInK
  rw [hT, hS, toArray_getElem!_eq_getD, toArray_getElem!_eq_getD, trK_eq, slK_eq]

theorem coplanar_eq (l k : Nat) : Native.coplanar TS.toArray l k = copG (tsK TS) l k := by
  unfold Native.coplanar copG
  rw [toArray_getElem!_eq_getD, toArray_getElem!_eq_getD, tsK_eq, tsK_eq]

theorem co_eq : (fun l m => (List.range Native.nTrio).filter fun k =>
    Native.coplanar TS.toArray l k && Native.coplanar TS.toArray m k) = coK TS := by
  funext l m
  unfold coK
  rw [List.filter_filter]
  refine List.filter_congr fun k _ => ?_
  rw [coplanar_eq, coplanar_eq, Bool.and_comm]

include hT in
theorem pen_eq : (fun π y => (List.range Native.nTrio).filter fun k =>
    TS.toArray[k]!.contains π && (Native.octsT (Native.trioList ())[k]!).contains y) =
    penK TL TS := by
  funext π y
  unfold penK
  rw [List.filter_filter]
  refine List.filter_congr fun k _ => ?_
  rw [hT, toArray_getElem!_eq_getD, toArray_getElem!_eq_getD, Bool.and_comm, tsK_eq, trK_eq]

include hlt in
theorem trK_lt (p : Nat) : ∀ x ∈ Native.octsT (trK TL p), x < 2 ^ 24 := by
  rw [trK_eq]
  by_cases hp : p < TL.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    have := List.all_eq_true.1 hlt _ (List.getElem_mem hp)
    exact fun x hx => of_decide_eq_true (List.all_eq_true.1 this x hx)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    decide

include hlt in
theorem ocK_lt (p q : Nat) : ocK TL SL p q < 2 ^ 24 := by
  unfold ocK octsInK
  cases h : (Native.octsT (trK TL p)).filter fun o =>
      (Native.octsS (slK SL q)).contains o with
  | nil => simp
  | cons a l =>
    have ha : a ∈ (Native.octsT (trK TL p)).filter fun o =>
        (Native.octsS (slK SL q)).contains o := by rw [h]; exact List.mem_cons_self
    exact trK_lt hlt p a (List.mem_filter.1 ha).1

include hT hTl hpos hlt in
theorem ix_eq {x y : Nat} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24) :
    Native.trioIdx (Native.sort3 x y (Native.full ^^^ x ^^^ y)) = ixK TL x y := by
  have hz : Native.full ^^^ x ^^^ y < 2 ^ 24 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by decide) hx) hy
  have ht : ∀ m ∈ Native.octsT (Native.sort3 x y (Native.full ^^^ x ^^^ y)), m < 2 ^ 24 := by
    intro m hm
    rcases mem_sort3 hm with rfl | rfl | rfl <;> assumption
  rw [trioIdx_eq_idxNat, hT]
  refine idxNat_eq_idxK hpos hTl fun t htm e => key3_inj ?_ ht e
  have := List.all_eq_true.1 hlt t htm
  exact fun x hx => of_decide_eq_true (List.all_eq_true.1 this x hx)

include hT hS hTl hpos hlt in
theorem piCheck_eq (m : Nat) :
    Native.piCheck TS.toArray 0 m =
      piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m := by
  rw [piCheck_eq_piG, trioSexts_lookup, co_eq, pen_eq hT, trioList_lookup hT, oneIn_eq hT hS,
    octIn_eq hT hS]
  exact piG_ix_congr fun a b => ix_eq hT hTl hpos hlt (ocK_lt hlt 0 a) (ocK_lt hlt m b)

include hT hTS hS hTl hpos hlt in
theorem stmt310Check_eq : Native.stmt310Check () = stmt310K TL TS SL := by
  unfold Native.stmt310Check stmt310K
  simp only [hTS, hT, piCheck_eq hT hS hTl hpos hlt, toArray_getElem!_eq_getD, trK_eq]

include hT hTS hS in
theorem stmt313Check_eq : Native.stmt313Check () = stmt313K TL TS SL := by
  have hLU : Native.sextTrios TS.toArray 0 =
      (List.range Native.nTrio).filter fun p => (tsK TS p).contains 0 := by
    unfold Native.sextTrios
    refine List.filter_congr fun p _ => ?_
    rw [toArray_getElem!_eq_getD, tsK_eq]
  have hd : ∀ l k, (!(Native.meets (Native.trioList ())[l]! (Native.trioList ())[k]!) &&
      Native.coplanar TS.toArray l k) = d2K TL TS l k := by
    intro l k
    rw [coplanar_eq, hT, toArray_getElem!_eq_getD, toArray_getElem!_eq_getD, d2K, trK_eq, trK_eq]
  rw [stmt313Check_eq_G, hTS, hLU, oneIn_eq hT hS]
  simp only [hd, ← List.any_filter]
  rw [trioList_lookup hT]
  rfl

end Rec

end CFSG.KC.M24G
