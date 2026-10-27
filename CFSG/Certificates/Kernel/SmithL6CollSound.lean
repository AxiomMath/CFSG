module

public import Certificates.Data.Kernel.SmithL6Coll
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SmithL6.CollK

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

theorem foldl_xor (P : Nat → Bool) (g : Nat → Nat) (xs : List Nat) (a : Nat) :
    xs.foldl (fun acc m => if P m then acc ^^^ g m else acc) a =
      a ^^^ xs.foldl (fun acc m => if P m then acc ^^^ g m else acc) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons m xs ih =>
    simp only [List.foldl_cons]
    rw [ih (if P m then a ^^^ g m else a), ih (if P m then 0 ^^^ g m else 0)]
    cases h : P m <;> simp [Nat.xor_assoc]

theorem apK_eq (l : List Nat) (x : Nat) : apK l x =
    (List.range l.length).foldl (fun acc m => if x.testBit m then acc ^^^ l.getD m 0 else acc) 0 := by
  induction l generalizing x with
  | nil => simp [apK]
  | cons c l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have e : (fun acc m => if x.testBit (Nat.succ m) then acc ^^^ (c :: l).getD (Nat.succ m) 0
        else acc) = (fun acc m => if (x / 2).testBit m then acc ^^^ l.getD m 0 else acc) := by
      funext acc m
      rw [Nat.testBit_succ, List.getD_cons_succ]
    rw [e, foldl_xor, ← ih, apK, Nat.testBit_zero, List.getD_cons_zero]
    by_cases h : x % 2 = 1 <;> simp [h]

theorem toArray_get (l : List Nat) (m : Nat) : l.toArray[m]! = l.getD m 0 := by
  rw [List.getElem!_toArray]
  by_cases hm : m < l.length
  · rw [getElem!_pos l m hm]
    simp [List.getD_eq_getElem?_getD, hm]
  · rw [getElem!_neg l m hm]
    simp [List.getD_eq_getElem?_getD, show l.length ≤ m by omega]

theorem applyCols_toArray (l : List Nat) (x : Nat) : applyCols l.toArray x = apK l x := by
  rw [apK_eq]
  unfold applyCols
  simp only [List.size_toArray, toArray_get]

theorem apK_zero (l : List Nat) : apK l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [apK, ih]

theorem apK_append (l : List Nat) (p x : Nat) : apK (l ++ [p]) x = apN l p x := by
  unfold apN
  induction l generalizing x with
  | nil =>
    simp only [List.nil_append, apK, List.length_nil, Nat.pow_zero, Nat.mod_one, Nat.testBit_zero]
    by_cases h : x % 2 = 1 <;> simp [h]
  | cons c l ih =>
    simp only [List.cons_append, List.length_cons, apK]
    rw [ih (x / 2)]
    have h3 : x.testBit (l.length + 1) = (x / 2).testBit l.length := Nat.testBit_succ x _
    simp only [h3]
    have h1 : x % 2 ^ (l.length + 1) % 2 = x % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    have h2 : x % 2 ^ (l.length + 1) / 2 = x / 2 % 2 ^ l.length := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    rw [h1, h2]
    by_cases h : x % 2 = 1 <;> simp [h, Nat.xor_assoc]

theorem apK_take (x : List Nat) (j y : Nat) (hy : y < 2 ^ j) : apK (x.take j) y = apK x y := by
  induction x generalizing j y with
  | nil => simp
  | cons c x ih =>
    cases j with
    | zero =>
      have : y = 0 := by simpa using hy
      subst this
      simp [apK_zero]
    | succ j =>
      have hy2 : y / 2 < 2 ^ j := by
        rw [Nat.pow_succ] at hy
        omega
      simp only [List.take_succ_cons, apK, ih j (y / 2) hy2]

theorem apK_lt {l : List Nat} (h : ∀ c ∈ l, c < 512) (x : Nat) : apK l x < 512 := by
  induction l generalizing x with
  | nil => simp [apK]
  | cons c l ih =>
    have hc : c < 2 ^ 9 := h c (by simp)
    have ih' : apK l (x / 2) < 2 ^ 9 := ih (fun d hd => h d (by simp [hd])) (x / 2)
    unfold apK
    split
    · exact Nat.xor_lt_two_pow hc ih'
    · exact ih'

@[expose] def QO (l : List Nat) (p : Nat) : Bool :=
  (collNewPts l.length).all (fun q => collPtTab[applyCols (l.toArray.push p) q]!) &&
    !collInSpan l.toArray p

theorem collGo_eq : ∀ (n : Nat) (cols : Array Nat),
    collGo n cols = (goG QO n cols.toList).map List.toArray
  | 0, cols => by simp [collGo, goG]
  | n + 1, cols => by
    simp only [collGo, goG, List.map_flatMap]
    have e : (uco.toList.filter fun p => (collNewPts cols.size).all
        (fun q => collPtTab[applyCols (cols.push p) q]!) && !collInSpan cols p) =
        uco.toList.filter (QO cols.toList) := by
      congr 1
    rw [e]
    congr 1
    funext p
    rw [collGo_eq n (cols.push p), Array.toList_push]

theorem ptTab_eq (x : Nat) : collPtTab[x]! = ptMask.testBit x := by
  by_cases hx : x < 512
  · have h : ∀ y < 512, collPtTab[y]! = ptMask.testBit y := by decide +kernel
    exact h x hx
  · have hs : collPtTab.size = 512 := by simp [collPtTab]
    rw [getElem!_neg collPtTab x (by omega)]
    have hm : ptMask >>> 512 = 0 := by decide +kernel
    have e : ptMask.testBit x = (ptMask >>> 512).testBit (x - 512) := by
      rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' (by omega)]
    rw [e, hm, Nat.zero_testBit]
    rfl

theorem QK_eq (l : List Nat) (p : Nat) : QK l p = (QO l p && pruneK l p) := by
  unfold QK QO collInSpan
  have e1 : (collNewPts l.length).all (fun q => collPtTab[applyCols (l.toArray.push p) q]!) =
      (collNewPts l.length).all (fun q => ptMask.testBit (apN l p q)) :=
    List.all_congr rfl fun q => by
      rw [ptTab_eq, List.push_toArray, applyCols_toArray, apK_append]
  have e2 : (List.range (2 ^ l.toArray.size)).any (fun s => applyCols l.toArray s == p) =
      (List.range (2 ^ l.length)).any (fun s => apK l s == p) := by
    simp only [List.size_toArray, applyCols_toArray]
  rw [e1, e2]
  cases (collNewPts l.length).all (fun q => ptMask.testBit (apN l p q)) <;>
    cases pruneK l p <;> simp

theorem goG_mem (Q : List Nat → Nat → Bool) : ∀ (n : Nat) (l x : List Nat), x ∈ goG Q n l →
    x.length = l.length + n ∧ x.take l.length = l
  | 0, l, x, h => by
    simp only [goG, List.mem_singleton] at h
    subst h
    simp
  | n + 1, l, x, h => by
    simp only [goG, List.mem_flatMap, List.mem_filter] at h
    obtain ⟨p, -, hx⟩ := h
    obtain ⟨h1, h2⟩ := goG_mem Q n (l ++ [p]) x hx
    simp only [List.length_append, List.length_singleton] at h1 h2
    refine ⟨by omega, ?_⟩
    have e : (x.take (l.length + 1)).take l.length = l := by rw [h2]; simp
    rwa [List.take_take, Nat.min_eq_left (by omega)] at e

theorem getD_of_take {x l : List Nat} {p : Nat} (h : x.take (l.length + 1) = l ++ [p]) :
    x.getD l.length 0 = p := by
  have e : (x.take (l.length + 1))[l.length]? = some p := by rw [h]; simp
  rw [List.getElem?_take_of_lt (by omega)] at e
  simp [List.getD_eq_getElem?_getD, e]

theorem filter_flatMap_eq (f : List Nat → Bool) (g : Nat → List (List Nat)) (xs : List Nat) :
    (xs.flatMap g).filter f = xs.flatMap fun p => (g p).filter f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem flatMap_filter_and (A B : Nat → Bool) (g : Nat → List (List Nat)) (xs : List Nat)
    (hg : ∀ p ∈ xs, A p = true → B p = false → g p = []) :
    (xs.filter A).flatMap g = (xs.filter fun p => A p && B p).flatMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ih' := ih (fun p hp => hg p (by simp [hp]))
    cases hA : A a <;> cases hB : B a <;>
      simp [List.filter_cons, hA, hB, ih', hg a (by simp)]

theorem goG_filter (Q R : List Nat → Nat → Bool) (f : List Nat → Bool) (N : Nat)
    (hR : ∀ x : List Nat, x.length = N → f x = true → ∀ k < N, R (x.take k) (x.getD k 0) = true) :
    ∀ (n : Nat) (l : List Nat), l.length + n = N →
      (goG Q n l).filter f = (goG (fun l p => Q l p && R l p) n l).filter f
  | 0, _, _ => rfl
  | n + 1, l, hl => by
    simp only [goG, filter_flatMap_eq]
    have ih : ∀ p, (goG Q n (l ++ [p])).filter f =
        (goG (fun l p => Q l p && R l p) n (l ++ [p])).filter f := fun p =>
      goG_filter Q R f N hR n (l ++ [p]) (by simp; omega)
    simp only [ih]
    apply flatMap_filter_and
    intro p _ _ hRp
    rw [List.filter_eq_nil_iff]
    intro x hx hfx
    obtain ⟨h1, h2⟩ := goG_mem _ n (l ++ [p]) x hx
    simp only [List.length_append, List.length_singleton] at h1 h2
    have hlen : x.length = N := by omega
    have e1 : x.take l.length = l := by
      have e : (x.take (l.length + 1)).take l.length = l := by rw [h2]; simp
      rwa [List.take_take, Nat.min_eq_left (by omega)] at e
    have e2 := getD_of_take h2
    have := hR x hlen hfx l.length (by omega)
    rw [e1, e2, hRp] at this
    exact absurd this (by simp)

theorem invK_eq (x : List Nat) : invK x = collInvB x.toArray := by
  simp only [invK, collInvB, toArray_get, applyCols_toArray]

theorem pruneK_of_inv (x : List Nat) (hx : x.length = 9) (hinv : invK x = true) (k : Nat)
    (hk : k < 9) : pruneK (x.take k) (x.getD k 0) = true := by
  have hm : ∀ m < 9, apK x (x.getD m 0) = 2 ^ m := by
    intro m hm
    simp only [invK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hinv
    exact hinv.1 m hm
  have hlen : (x.take k).length = k := by simp [hx]; omega
  have hap : ∀ y < 2 ^ (k + 1), apN (x.take k) (x.getD k 0) y = apK x y := by
    intro y hy
    rw [← apK_append]
    have e : x.take k ++ [x.getD k 0] = x.take (k + 1) := by
      rw [List.take_succ]
      have : x[k]? = some (x.getD k 0) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < x.length)]
      rw [this]
      rfl
    rw [e, apK_take x (k + 1) y hy]
  unfold pruneK
  rw [hlen]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt, beq_iff_eq]
  refine ⟨fun m hmk => ?_, ?_⟩
  · have e : (x.take k).getD m 0 = x.getD m 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hmk]
    rw [e]
    by_cases hlt : x.getD m 0 < 2 ^ (k + 1)
    · exact Or.inr (by rw [hap _ hlt, hm m (by omega)])
    · exact Or.inl (by omega)
  · by_cases hlt : x.getD k 0 < 2 ^ (k + 1)
    · exact Or.inr (by rw [hap _ hlt, hm k hk])
    · exact Or.inl (by omega)

theorem collL_eq_goG : collL = (((goG QK 9 []).filter invK).map List.toArray).toArray := by
  have hf : (fun x : List Nat => collInvB x.toArray) = invK := by
    funext x
    rw [invK_eq]
  have hQ : (fun l p => QO l p && pruneK l p) = QK := by
    funext l p
    rw [QK_eq]
  have hg := goG_filter QO pruneK invK 9
    (fun x hx hinv k hk => pruneK_of_inv x hx hinv k hk) 9 [] (by simp)
  rw [hQ] at hg
  unfold collL collLeaves
  rw [collGo_eq, List.filter_map]
  have e : (collInvB ∘ List.toArray) = invK := hf
  rw [e]
  simp only [Array.toList_empty]
  rw [hg]

theorem fld_eq (T s : Nat) : fld T s = T / 2 ^ (9 * s) % 512 := by
  rw [fld, Nat.shiftRight_eq_div_pow]

theorem fld_packF : ∀ (xs : List Nat), (∀ a ∈ xs, a < 512) → ∀ s, fld (packF xs) s = xs.getD s 0
  | [], _, s => by simp [fld_eq, packF]
  | a :: r, h, s => by
    have ha : a < 512 := h a (by simp)
    cases s with
    | zero =>
      simp only [fld_eq, packF, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    | succ s =>
      rw [List.getD_cons_succ, ← fld_packF r (fun b hb => h b (by simp [hb])) s, fld_eq, fld_eq,
        packF]
      have e : 2 ^ (9 * (s + 1)) = 512 * 2 ^ (9 * s) := by
        rw [Nat.mul_succ, Nat.pow_add]
        ring
      rw [e, ← Nat.div_div_eq_div_mul]
      congr 2
      omega

theorem packF_append (xs ys : List Nat) :
    packF (xs ++ ys) = packF xs + packF ys * 2 ^ (9 * xs.length) := by
  induction xs with
  | nil => simp [packF]
  | cons a xs ih =>
    simp only [List.cons_append, packF, ih, List.length_cons]
    rw [Nat.mul_succ, Nat.pow_add]
    ring

theorem xor_pack (a b c d : Nat) (ha : a < 512) (hc : c < 512) :
    (a + 512 * b) ^^^ (c + 512 * d) = (a ^^^ c) + 512 * (b ^^^ d) := by
  have h512 : (512 : Nat) = 2 ^ 9 := rfl
  have hac : a ^^^ c < 512 := by rw [h512] at ha hc ⊢; exact Nat.xor_lt_two_pow ha hc
  have m1 : (a + 512 * b) % 512 = a := by omega
  have m2 : (c + 512 * d) % 512 = c := by omega
  have d1 : (a + 512 * b) / 512 = b := by omega
  have d2 : (c + 512 * d) / 512 = d := by omega
  have hm : ((a + 512 * b) ^^^ (c + 512 * d)) % 512 = a ^^^ c := by
    rw [h512, Nat.xor_mod_two_pow, ← h512, m1, m2]
  have hd : ((a + 512 * b) ^^^ (c + 512 * d)) / 512 = b ^^^ d := by
    rw [h512, Nat.xor_div_two_pow, ← h512, d1, d2]
  have := Nat.mod_add_div ((a + 512 * b) ^^^ (c + 512 * d)) 512
  rw [hm, hd] at this
  exact this.symm

theorem packF_xor : ∀ (xs ys : List Nat), (∀ a ∈ xs, a < 512) → (∀ a ∈ ys, a < 512) →
    xs.length = ys.length → packF (List.zipWith (· ^^^ ·) xs ys) = packF xs ^^^ packF ys
  | [], [], _, _, _ => by simp [packF]
  | a :: xs, c :: ys, hx, hy, hl => by
    simp only [List.zipWith_cons_cons, packF]
    rw [packF_xor xs ys (fun b hb => hx b (by simp [hb])) (fun b hb => hy b (by simp [hb]))
      (by simpa using hl), xor_pack a _ c _ (hx a (by simp)) (hy c (by simp))]
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl

theorem rep_eq (n : Nat) : rep n = packF (List.replicate n 1) := by
  have h : ∀ n, 511 * packF (List.replicate n 1) + 1 = 2 ^ (9 * n) := by
    intro n
    induction n with
    | zero => simp [packF]
    | succ n ih =>
      simp only [List.replicate_succ, packF]
      rw [Nat.mul_succ, Nat.pow_add, ← ih]
      ring
  unfold rep
  rw [← h n, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by omega)]

theorem mul_rep (p n : Nat) : p * rep n = packF (List.replicate n p) := by
  rw [rep_eq]
  induction n with
  | zero => simp [packF]
  | succ n ih =>
    simp only [List.replicate_succ, packF]
    rw [← ih]
    ring

theorem packF_map_xor (xs : List Nat) (p : Nat) (hx : ∀ a ∈ xs, a < 512) (hp : p < 512) :
    packF (xs.map (· ^^^ p)) = packF xs ^^^ p * rep xs.length := by
  rw [mul_rep, ← packF_xor xs _ hx (fun a ha => by rw [List.eq_of_mem_replicate ha]; exact hp)
    (by simp)]
  congr 1
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
    rw [ih (fun b hb => hx b (by simp [hb]))]

theorem fld_tab {l : List Nat} (hl : ∀ c ∈ l, c < 512) {s : Nat} (hs : s < 2 ^ l.length) :
    fld (tab l) s = apK l s := by
  unfold tab
  rw [fld_packF _ (fun a ha => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
    exact apK_lt hl t)]
  simp [List.getD_eq_getElem?_getD, hs]

theorem tab_append {l : List Nat} (hl : ∀ c ∈ l, c < 512) {p : Nat} (hp : p < 512) :
    tab (l ++ [p]) = tabStep (tab l) l.length p := by
  have hlt : ∀ a ∈ (List.range (2 ^ l.length)).map (apK l), a < 512 := fun a ha => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
    exact apK_lt hl t
  unfold tab tabStep
  have e : (List.range (2 ^ (l ++ [p]).length)).map (apK (l ++ [p])) =
      (List.range (2 ^ l.length)).map (apK l) ++
        ((List.range (2 ^ l.length)).map (apK l)).map (· ^^^ p) := by
    rw [List.length_append, List.length_singleton, Nat.pow_succ, Nat.mul_two, List.range_add,
      List.map_append, List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun s hs => ?_
      have hs' : s < 2 ^ l.length := List.mem_range.mp hs
      rw [apK_append]
      unfold apN
      rw [Nat.mod_eq_of_lt hs', Nat.testBit_lt_two_pow hs']
      simp
    · refine List.map_congr_left fun s hs => ?_
      have hs' : s < 2 ^ l.length := List.mem_range.mp hs
      simp only [Function.comp]
      rw [apK_append]
      unfold apN
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hs', Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hs']
      simp
  rw [e, packF_append, packF_map_xor _ p hlt hp]
  simp

theorem any_congr' {l : List Nat} {f g : Nat → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem flatMap_congr' {l : List Nat} {f g : Nat → List (List Nat)} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem apNT_eq {l : List Nat} (hl : ∀ c ∈ l, c < 512) (p x : Nat) :
    apNT (tab l) l.length p x = apN l p x := by
  unfold apNT apN
  rw [fld_tab hl (Nat.mod_lt _ (Nat.two_pow_pos _))]

theorem QT_eq {l : List Nat} (hl : ∀ c ∈ l, c < 512) (p : Nat) :
    QT (collNewPts l.length) l (tab l) l.length p = QK l p := by
  unfold QT QK pruneT pruneK
  simp only [apNT_eq hl]
  rw [any_congr' (fun s hs => by rw [fld_tab hl (List.mem_range.mp hs)])]

theorem invT_eq {x : List Nat} (hx : x.length = 9) (hl : ∀ c ∈ x, c < 512) :
    invT x (tab x) = invK x := by
  unfold invT invK
  have e : ∀ m, fld (tab x) (x.getD m 0) = apK x (x.getD m 0) := by
    intro m
    refine fld_tab hl ?_
    rw [hx]
    by_cases h : m < x.length
    · have := hl (x.getD m 0) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        exact List.getElem_mem h)
      exact lt_of_lt_of_eq this rfl
    · simp [List.getD_eq_getElem?_getD, show x.length ≤ m by omega]
  simp only [e]

theorem uco_lt : ∀ p ∈ uco.toList, p < 512 := by decide +kernel

theorem goT_eq : ∀ (n : Nat) (l : List Nat), (∀ c ∈ l, c < 512) → l.length + n = 9 →
    goT ((List.range' l.length n).map collNewPts) l (tab l) = (goG QK n l).filter invK
  | 0, l, hl, hn => by
    simp only [List.range'_zero, List.map_nil, goT, goG]
    rw [invT_eq (by omega) hl]
    cases h : invK l <;> simp [List.filter, h]
  | n + 1, l, hl, hn => by
    simp only [List.range'_succ, List.map_cons, goT, goG, filter_flatMap_eq]
    have hf : uco.toList.filter (QT (collNewPts l.length) l (tab l) l.length) =
        uco.toList.filter (QK l) :=
      List.filter_congr fun p _ => QT_eq hl p
    rw [hf]
    refine flatMap_congr' fun p hp => ?_
    have hp' : p < 512 := uco_lt p (List.mem_filter.mp hp).1
    have hl' : ∀ c ∈ l ++ [p], c < 512 := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hl c hc
      · rw [List.mem_singleton.mp hc]
        exact hp'
    rw [← tab_append hl hp']
    have := goT_eq n (l ++ [p]) hl' (by simp; omega)
    rw [show (l ++ [p]).length = l.length + 1 by simp] at this
    exact this

theorem tab_single (c : Nat) : tab [c] = 512 * c := by
  simp [tab, List.range_succ, packF, apK]

theorem top_eq {c : Nat} (hc : c < 512) :
    (goG QK 8 [c]).filter invK = goT ((List.range' 1 8).map collNewPts) [c] (512 * c) := by
  have := goT_eq 8 [c] (by simpa using hc) (by simp)
  rw [List.length_singleton, tab_single] at this
  exact this.symm

theorem flatMap_idx : ∀ {xs : List Nat} {R : List (List (List Nat))} {h : Nat → List (List Nat)},
    R.length = xs.length → (∀ i < xs.length, h (xs.getD i 0) = R.getD i []) →
      xs.flatMap h = R.flatten
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | a :: xs, r :: R, h, hl, hR => by
    have h0 : h a = r := by simpa using hR 0 (by simp)
    simp only [List.flatMap_cons, List.flatten_cons, h0]
    congr 1
    exact flatMap_idx (by simpa using hl) fun i hi => by
      simpa using hR (i + 1) (by simp; omega)

theorem collL_eq (R : List (List (List Nat))) (hlen : R.length = 49)
    (h : ∀ i < 49, topT R i = true) : collL = (R.flatten.map List.toArray).toArray := by
  rw [collL_eq_goG]
  have e0 : uco.toList.filter (QK []) = uco.toList := by decide +kernel
  have e1 : goG QK 9 [] = (uco.toList.filter (QK [])).flatMap fun p => goG QK 8 ([] ++ [p]) := rfl
  have hu : uco.toList.length = 49 := by decide +kernel
  have e2 : (goG QK 9 []).filter invK = R.flatten := by
    rw [e1, e0, filter_flatMap_eq]
    simp only [List.nil_append]
    refine flatMap_idx (by rw [hlen, hu]) fun i hi => ?_
    have hc : uco.toList.getD i 0 < 512 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact uco_lt _ (List.getElem_mem hi)
    rw [top_eq hc]
    have := h i (by omega)
    unfold topT at this
    exact beq_iff_eq.mp this
  rw [e2]

private theorem testBit_bitsOf {β : Type} (f : β → Bool) :
    ∀ (l : List β) (t : Nat), (bitsOf f l).testBit t = true ↔ ∃ h : t < l.length, f l[t] = true
  | [], t => by simp [bitsOf]
  | a :: l, 0 => by
    unfold bitsOf
    rw [Nat.testBit_zero]
    cases h : f a <;> simp [h, Nat.add_mul_mod_self_left]
  | a :: l, t + 1 => by
    unfold bitsOf
    have e : ((if f a = true then 1 else 0) + 2 * bitsOf f l) / 2 = bitsOf f l := by
      split <;> omega
    rw [Nat.testBit_succ, e, testBit_bitsOf f l t]
    simp

private theorem land_sub_one_two_mul (y : Nat) (hy : y ≠ 0) :
    (2 * y) &&& (2 * y - 1) = 2 * (y &&& (y - 1)) := by
  have e : 2 * y - 1 = 2 * (y - 1) + 1 := by omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases i with
  | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
  | succ i =>
    have h1 : 2 * y / 2 = y := by omega
    have h2 : (2 * (y - 1) + 1) / 2 = y - 1 := by omega
    have h3 : 2 * (y &&& (y - 1)) / 2 = (y &&& (y - 1)) := by omega
    simp only [Nat.testBit_succ, h1, h2, h3, Nat.testBit_and]

private theorem testBit_land_sub_one : ∀ x : Nat, x ≠ 0 →
    ∃ i₀, x.testBit i₀ = true ∧ ∀ i, (x &&& (x - 1)).testBit i = (x.testBit i && i != i₀) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases Nat.even_or_odd x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have hy : y ≠ 0 := by omega
      obtain ⟨j, hj, hjb⟩ := ih y (by omega) hy
      refine ⟨j + 1, ?_, fun i => ?_⟩
      · rw [show y + y = 2 * y by omega, Nat.testBit_succ]
        simpa using hj
      · rw [show y + y = 2 * y by omega, land_sub_one_two_mul y hy]
        cases i with
        | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
        | succ i =>
          have h1 : 2 * y / 2 = y := by omega
          have h3 : 2 * (y &&& (y - 1)) / 2 = (y &&& (y - 1)) := by omega
          simp only [Nat.testBit_succ, h1, h3, hjb i]
          simp
    · refine ⟨0, by simp [Nat.testBit_zero], fun i => ?_⟩
      have e : (2 * y + 1) &&& (2 * y + 1 - 1) = 2 * y := by
        rw [show 2 * y + 1 - 1 = 2 * y by omega]
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        cases i with
        | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
        | succ i =>
          have h1 : (2 * y + 1) / 2 = y := by omega
          have h2 : 2 * y / 2 = y := by omega
          simp only [Nat.testBit_succ, h1, h2, Bool.and_self]
      rw [e]
      cases i with
      | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
      | succ i =>
        have h1 : (2 * y + 1) / 2 = y := by omega
        have h2 : 2 * y / 2 = y := by omega
        simp only [Nat.testBit_succ, h1, h2]
        simp

private theorem length_le_of_atMost : ∀ (k x : Nat), atMost k x = true →
    ∀ l : List Nat, l.Nodup → (∀ i ∈ l, x.testBit i = true) → l.length ≤ k
  | 0, x, h, l, _, hl => by
    have hx : x = 0 := by simpa [atMost] using h
    cases l with
    | nil => simp
    | cons i l => simpa [hx] using hl i (by simp)
  | k + 1, x, h, l, hnd, hl => by
    by_cases hx : x = 0
    · cases l with
      | nil => simp
      | cons i l => simpa [hx] using hl i (by simp)
    · have h' : atMost k (x &&& (x - 1)) = true := by
        simpa [atMost, hx] using h
      obtain ⟨i₀, -, hb⟩ := testBit_land_sub_one x hx
      have := length_le_of_atMost k _ h' (l.erase i₀) (hnd.erase i₀) fun i hi => by
        rw [hb, hl i (List.mem_of_mem_erase hi), Bool.true_and]
        simpa using (hnd.mem_erase_iff.mp hi).1
      by_cases hm : i₀ ∈ l
      · rw [List.length_erase_of_mem hm] at this
        have := List.length_pos_of_mem hm
        omega
      · rw [List.erase_of_not_mem hm] at this
        omega


private theorem tab_nil : tab [] = 0 := by
  simp [tab, packF, apK_zero]

private theorem tab9_eq_tab {A : List Nat} (hA : A.length = 9) (hlt : ∀ c ∈ A, c < 512) :
    tab9 A = tab A := by
  have key : ∀ j ≤ 9,
      (List.range j).foldl (fun T j => tabStep T j (A.getD j 0)) 0 = tab (A.take j) := by
    intro j hj
    induction j with
    | zero => simp [tab_nil]
    | succ j ih =>
      have hjA : j < A.length := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
        List.take_succ, List.getElem?_eq_getElem hjA, Option.toList_some,
        tab_append (fun c hc => hlt c (List.mem_of_mem_take hc)) (hlt _ (List.getElem_mem hjA)),
        List.length_take, min_eq_left (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hjA, Option.getD_some]
  unfold tab9
  rw [key 9 le_rfl, List.take_of_length_le (by omega)]

private theorem fld_tab9 {A : List Nat} (hA : A.length = 9) (hlt : ∀ c ∈ A, c < 512) {v : Nat}
    (hv : v < 512) : fld (tab9 A) v = apK A v := by
  rw [tab9_eq_tab hA hlt, fld_tab hlt (by rw [hA]; exact hv)]

section Rows

variable {LM : List (List Nat × Nat × Nat × Nat)}

private theorem size_of_eq {C : Array (Array Nat)}
    (hC : C = ((LM.map (·.1)).map List.toArray).toArray) : C.size = LM.length := by
  subst hC
  simp

private theorem get_of_eq {C : Array (Array Nat)}
    (hC : C = ((LM.map (·.1)).map List.toArray).toArray) {b : Nat} (hb : b < LM.length) :
    C[b]! = (LM.getD b ([], 0, 0, 0)).1.toArray := by
  subst hC
  rw [getElem!_pos _ b (by simpa using hb)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]

private theorem get_map_ofFn (C : Array (Array Nat)) (g : Array Nat → Nat → Bool) {a v : Nat}
    (ha : a < C.size) (hv : v < 512) :
    (C.map fun A => Array.ofFn (n := 512) fun w => g A w.val)[a]![v]! = g C[a]! v := by
  rw [getElem!_pos _ a (by simpa using ha)]
  rw [getElem!_pos _ v (by simpa using hv)]
  simp [getElem!_pos C a ha]

private theorem get_map_map (C : Array (Array Nat)) (g : Array Nat → Array Nat → Bool)
    {a b : Nat} (ha : a < C.size) (hb : b < C.size) :
    (C.map fun A => C.map fun B => g A B)[a]![b]! = g C[a]! C[b]! := by
  rw [getElem!_pos _ a (by simpa using ha)]
  rw [getElem!_pos _ b (by simpa using hb)]
  simp [getElem!_pos C a ha, getElem!_pos C b hb]

private theorem get_toArray_map_range (N : Nat) (f : Nat → List Nat) {a : Nat} (ha : a < N) :
    ((List.range N).map f).toArray[a]! = f a := by
  rw [getElem!_pos _ a (by simpa using ha)]
  simp

private theorem collFixTab_get {a v : Nat} (ha : a < collL.size) (hv : v < 512) :
    collFixTab[a]![v]! = (applyCols collL[a]! v == v) := by
  rw [collFixTab]
  exact get_map_ofFn collL (fun A w => applyCols A w == w) ha hv

private theorem collCommTab_get {a b : Nat} (ha : a < collL.size) (hb : b < collL.size) :
    collCommTab[a]![b]! = collComm collL[a]! collL[b]! := by
  rw [collCommTab]
  exact get_map_map collL collComm ha hb

private theorem collFixList_get {a : Nat} (ha : a < collL.size) :
    collFixList[a]! = (List.range 512).filter fun v => collFixTab[a]![v]! := by
  rw [collFixList]
  exact get_toArray_map_range _ (fun a => (List.range 512).filter fun v => collFixTab[a]![v]!) ha

private theorem collCommList_get {a : Nat} (ha : a < collL.size) :
    collCommList[a]! = (List.range collL.size).filter fun m => collCommTab[a]![m]! := by
  rw [collCommList]
  exact get_toArray_map_range _
    (fun a => (List.range collL.size).filter fun m => collCommTab[a]![m]!) ha

end Rows

private theorem length_filter_range_le {N k X : Nat} {p : Nat → Bool} (hX : atMost k X = true)
    (hp : ∀ v < N, p v = true → X.testBit v = true) : ((List.range N).filter p).length ≤ k :=
  length_le_of_atMost k X hX _ ((List.nodup_range).filter p) fun v hv =>
    hp v (List.mem_range.mp (List.mem_filter.mp hv).1) (List.mem_filter.mp hv).2

private theorem collMul_toArray {A B : List Nat} (hB : B.length = 9) :
    collMul A.toArray B.toArray = (B.map (apK A)).toArray := by
  unfold collMul
  apply Array.ext
  · simp [hB]
  · intro m h1 h2
    simp only [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map]
    rw [applyCols_toArray]
    change apK A (B.toArray[m]!) = _
    rw [toArray_get, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [hB] using h1), Option.getD_some]

private theorem mem_filter_zipIdx {LM : List (List Nat × Nat × Nat × Nat)} {M b : Nat}
    (hb : b < LM.length) (hM : M.testBit b = true) :
    (LM.getD b ([], 0, 0, 0), b) ∈ LM.zipIdx.filter fun s => M.testBit s.2 := by
  refine List.mem_filter.mpr ⟨?_, by simpa using hM⟩
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hb]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]

private theorem rowFacts {LM : List (List Nat × Nat × Nat × Nat)} {a : Nat}
    (h : rowK LM a = true) :
    (LM.getD a ([], 0, 0, 0)).1.length = 9 ∧ (∀ c ∈ (LM.getD a ([], 0, 0, 0)).1, c < 512) ∧
      (LM.getD a ([], 0, 0, 0)).2.1 = tab9 (LM.getD a ([], 0, 0, 0)).1 ∧
      (LM.getD a ([], 0, 0, 0)).2.2.1 =
        bitsOf (fun v => fld (LM.getD a ([], 0, 0, 0)).2.1 v == v) (List.range 512) ∧
      (LM.getD a ([], 0, 0, 0)).2.2.2 = bitsOf (fun s => commT (LM.getD a ([], 0, 0, 0)).1
        (LM.getD a ([], 0, 0, 0)).2.1 s.1 s.2.1) LM ∧
      atMost 64 (LM.getD a ([], 0, 0, 0)).2.2.1 = true ∧
      ∀ s ∈ LM.zipIdx.filter (fun s => (LM.getD a ([], 0, 0, 0)).2.2.2.testBit s.2),
        s.2 = a ∨ (atMost 16 ((LM.getD a ([], 0, 0, 0)).2.2.1 &&& s.1.2.2.1) = true ∧
          atMost 23 ((LM.getD a ([], 0, 0, 0)).2.2.2 &&& s.1.2.2.2) = true) ∨
          tripK (LM.zipIdx.filter fun s => (LM.getD a ([], 0, 0, 0)).2.2.2.testBit s.2) a s.2
            ((LM.getD a ([], 0, 0, 0)).2.2.1 &&& s.1.2.2.1)
            ((LM.getD a ([], 0, 0, 0)).2.2.2 &&& s.1.2.2.2)
            (s.1.1.map (fld (LM.getD a ([], 0, 0, 0)).2.1)) = true := by
  unfold rowK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun s hs => ?_⟩
  rcases h7 s hs with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by simpa using h))
  · exact Or.inr (Or.inr h)

section RowFacts

variable {LM : List (List Nat × Nat × Nat × Nat)}

private theorem fld_row {a : Nat} (h : rowK LM a = true) {v : Nat} (hv : v < 512) :
    fld (LM.getD a ([], 0, 0, 0)).2.1 v = apK (LM.getD a ([], 0, 0, 0)).1 v := by
  obtain ⟨h1, h2, h3, -⟩ := rowFacts h
  rw [h3, fld_tab9 h1 h2 hv]

private theorem testBit_F {a : Nat} (h : rowK LM a = true) (v : Nat) :
    (LM.getD a ([], 0, 0, 0)).2.2.1.testBit v = true ↔
      v < 512 ∧ apK (LM.getD a ([], 0, 0, 0)).1 v = v := by
  obtain ⟨-, -, -, h4, -⟩ := rowFacts h
  rw [h4, testBit_bitsOf]
  constructor
  · rintro ⟨hv, hf⟩
    have hv' : v < 512 := by simpa using hv
    simp only [List.getElem_range, beq_iff_eq] at hf
    exact ⟨hv', by rw [← fld_row h hv']; exact hf⟩
  · rintro ⟨hv, hf⟩
    refine ⟨by simpa using hv, ?_⟩
    simp only [List.getElem_range, beq_iff_eq]
    rw [fld_row h hv]
    exact hf

private theorem getD_mem_lt {A : List Nat} (hlt : ∀ c ∈ A, c < 512) (m : Nat) :
    A.getD m 0 < 512 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : A[m]? with
  | none => simp
  | some c => simpa using hlt c (List.mem_of_getElem? h)

private theorem commT_row {a b : Nat} (ha : rowK LM a = true) (hb : rowK LM b = true) :
    commT (LM.getD a ([], 0, 0, 0)).1 (LM.getD a ([], 0, 0, 0)).2.1
        (LM.getD b ([], 0, 0, 0)).1 (LM.getD b ([], 0, 0, 0)).2.1 =
      collComm (LM.getD a ([], 0, 0, 0)).1.toArray (LM.getD b ([], 0, 0, 0)).1.toArray := by
  obtain ⟨-, ha2, -⟩ := rowFacts ha
  obtain ⟨-, hb2, -⟩ := rowFacts hb
  unfold commT collComm
  congr 1
  funext m
  rw [fld_row ha (getD_mem_lt hb2 m), fld_row hb (getD_mem_lt ha2 m), applyCols_toArray,
    applyCols_toArray, toArray_get, toArray_get]

private theorem testBit_M (h : ∀ a < LM.length, rowK LM a = true) {a : Nat}
    (ha : a < LM.length) (b : Nat) :
    (LM.getD a ([], 0, 0, 0)).2.2.2.testBit b = true ↔ b < LM.length ∧
      collComm (LM.getD a ([], 0, 0, 0)).1.toArray (LM.getD b ([], 0, 0, 0)).1.toArray = true := by
  obtain ⟨-, -, -, -, h5, -⟩ := rowFacts (h a ha)
  rw [h5, testBit_bitsOf]
  constructor
  · rintro ⟨hb, hf⟩
    refine ⟨hb, ?_⟩
    have e : LM[b] = LM.getD b ([], 0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
    rw [e, commT_row (h a ha) (h b hb)] at hf
    exact hf
  · rintro ⟨hb, hf⟩
    refine ⟨hb, ?_⟩
    have e : LM[b] = LM.getD b ([], 0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
    rw [e, commT_row (h a ha) (h b hb)]
    exact hf

end RowFacts

private theorem bool_guard {x y z w u q : Bool}
    (H : x = true → y = true → z = true → w = true → u = true → q = true) :
    (!(x && y && z && w && u) || q) = true := by
  cases x <;> cases y <;> cases z <;> cases w <;> cases u <;> simp_all

theorem chkColl_of_rowK (LM : List (List Nat × Nat × Nat × Nat))
    (hL : collL = ((LM.map (·.1)).map List.toArray).toArray)
    (h : ∀ a < LM.length, rowK LM a = true) : chkColl = true := by
  have hsz : collL.size = LM.length := size_of_eq hL
  have hget : ∀ b < LM.length, collL[b]! = (LM.getD b ([], 0, 0, 0)).1.toArray :=
    fun b hb => get_of_eq hL hb
  have hFix : ∀ a < LM.length, ∀ v < 512,
      (collFixTab[a]![v]! = true ↔ (LM.getD a ([], 0, 0, 0)).2.2.1.testBit v = true) := by
    intro a ha v hv
    rw [collFixTab_get (hsz ▸ ha) hv, hget a ha, applyCols_toArray, beq_iff_eq,
      testBit_F (h a ha)]
    exact ⟨fun e => ⟨hv, e⟩, fun e => e.2⟩
  have hComm : ∀ a < LM.length, ∀ b < LM.length,
      (collCommTab[a]![b]! = true ↔ (LM.getD a ([], 0, 0, 0)).2.2.2.testBit b = true) := by
    intro a ha b hb
    rw [collCommTab_get (hsz ▸ ha) (hsz ▸ hb), hget a ha, hget b hb, testBit_M h ha]
    exact ⟨fun e => ⟨hb, e⟩, fun e => e.2⟩
  have hCL : ∀ a < LM.length, ∀ b, b ∈ collCommList[a]! ↔
      b < LM.length ∧ (LM.getD a ([], 0, 0, 0)).2.2.2.testBit b = true := by
    intro a ha b
    rw [collCommList_get (hsz ▸ ha), List.mem_filter, List.mem_range, hsz]
    exact ⟨fun ⟨hb, e⟩ => ⟨hb, (hComm a ha b hb).mp e⟩,
      fun ⟨hb, e⟩ => ⟨hb, (hComm a ha b hb).mpr e⟩⟩
  have hfix3 : ∀ a < LM.length, ∀ b < LM.length, ∀ c < LM.length, ∀ {k X : Nat},
      atMost k X = true → (∀ v < 512, (LM.getD a ([], 0, 0, 0)).2.2.1.testBit v = true →
        (LM.getD b ([], 0, 0, 0)).2.2.1.testBit v = true →
        (LM.getD c ([], 0, 0, 0)).2.2.1.testBit v = true → X.testBit v = true) →
      collFix3 a b c ≤ k := by
    intro a ha b hb c hc k X hk hX
    unfold collFix3
    rw [collFixList_get (hsz ▸ ha), List.countP_eq_length_filter, List.filter_filter]
    refine length_filter_range_le hk fun v hv hpv => ?_
    simp only [Bool.and_eq_true] at hpv
    exact hX v hv ((hFix a ha v hv).mp hpv.2) ((hFix b hb v hv).mp hpv.1.1)
      ((hFix c hc v hv).mp hpv.1.2)
  have hcomm3 : ∀ a < LM.length, ∀ b < LM.length, ∀ c < LM.length, ∀ {k X : Nat},
      atMost k X = true → (∀ m < LM.length, (LM.getD a ([], 0, 0, 0)).2.2.2.testBit m = true →
        (LM.getD b ([], 0, 0, 0)).2.2.2.testBit m = true →
        (LM.getD c ([], 0, 0, 0)).2.2.2.testBit m = true → X.testBit m = true) →
      collComm3 a b c ≤ k := by
    intro a ha b hb c hc k X hk hX
    unfold collComm3
    rw [collCommList_get (hsz ▸ ha), List.countP_eq_length_filter, List.filter_filter, hsz]
    refine length_filter_range_le hk fun m hm hpm => ?_
    simp only [Bool.and_eq_true] at hpm
    exact hX m hm ((hComm a ha m hm).mp hpm.2) ((hComm b hb m hm).mp hpm.1.1)
      ((hComm c hc m hm).mp hpm.1.2)
  unfold chkColl
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun a ha' => ?_, fun a ha' => ?_⟩
  · have ha : a < LM.length := by rw [← hsz]; exact List.mem_range.mp ha'
    obtain ⟨h1, -, -, -, -, h6, -⟩ := rowFacts (h a ha)
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hget a ha]
    refine ⟨by simpa using h1, ?_⟩
    unfold collFixCount
    rw [collFixList_get (hsz ▸ ha)]
    exact length_filter_range_le h6 fun v hv hpv => (hFix a ha v hv).mp hpv
  · have ha : a < LM.length := by rw [← hsz]; exact List.mem_range.mp ha'
    rw [List.all_eq_true]
    intro b hbm
    rw [List.all_eq_true]
    intro c hcm
    obtain ⟨hb, hab⟩ := (hCL a ha b).mp hbm
    obtain ⟨hc, hac⟩ := (hCL a ha c).mp hcm
    refine bool_guard fun h1 h2 h3 h4 h5 => ?_
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    have hbc : (LM.getD b ([], 0, 0, 0)).2.2.2.testBit c = true := (hComm b hb c hc).mp h1
    have hne_ab : b ≠ a := fun e => (bne_iff_ne.mp h2) (by rw [e])
    have hne_ca : c ≠ a := fun e => (bne_iff_ne.mp h3) (by rw [e])
    have hne_cb : c ≠ b := fun e => (bne_iff_ne.mp h4) (by rw [e])
    have hmul : (LM.getD c ([], 0, 0, 0)).1 ≠
        (LM.getD b ([], 0, 0, 0)).1.map (fld (LM.getD a ([], 0, 0, 0)).2.1) := by
      intro e
      apply bne_iff_ne.mp h5
      rw [hget a ha, hget b hb, hget c hc, collMul_toArray (rowFacts (h b hb)).1, e]
      exact congrArg List.toArray (List.map_congr_left fun x hx =>
        (fld_row (h a ha) ((rowFacts (h b hb)).2.1 x hx)).symm)
    obtain ⟨-, -, -, -, -, -, h7⟩ := rowFacts (h a ha)
    rcases h7 _ (mem_filter_zipIdx hb hab) with hs | ⟨hf, hm⟩ | ht
    · exact absurd hs hne_ab
    · refine ⟨hfix3 a ha b hb c hc hf fun v _ ha' hb' _ => ?_,
        hcomm3 a ha b hb c hc hm fun m _ ha' hb' _ => ?_⟩
      · rw [Nat.testBit_and, ha', hb']
        rfl
      · rw [Nat.testBit_and, ha', hb']
        rfl
    · unfold tripK at ht
      rw [List.all_eq_true] at ht
      have hr := ht _ (mem_filter_zipIdx hc hac)
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.and_eq_true] at hr
      rcases hr with (((hr | hr) | hr) | hr) | ⟨hf, hm⟩
      · rw [Nat.testBit_and, hac, hbc] at hr
        exact absurd hr (by decide)
      · exact absurd hr hne_ca
      · exact absurd hr hne_cb
      · exact absurd hr hmul
      · refine ⟨hfix3 a ha b hb c hc hf fun v _ ha' hb' hc' => ?_,
          hcomm3 a ha b hb c hc hm fun m _ ha' hb' hc' => ?_⟩
        · rw [Nat.testBit_and, Nat.testBit_and, ha', hb', hc']
          rfl
        · rw [Nat.testBit_and, Nat.testBit_and, ha', hb', hc']
          rfl

end CFSG.SmithL6.CollK
