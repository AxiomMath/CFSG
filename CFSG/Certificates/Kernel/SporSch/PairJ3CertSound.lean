module

public import Certificates.Data.Kernel.SporSch.PairJ3Cert
public import CFSG.Sporadic.Schreier.PairText
public import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.Sporadic.Schreier.PairF2Quad
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.SporSch.HexLe70Sound

public section

namespace CFSG.KS.SporSch

open CFSG.Monster.B.Co2.Native

theorem hexAt_lt_of_le70 {cs : List Char} (h : le70K cs = true) (o d : Nat) :
    hexAt (String.ofList cs).toUTF8 o d < 2 ^ (4 * d) :=
  hexAt_lt_le70 h o d

theorem le70K_append (a b : List Char) : le70K (a ++ b) = (le70K a && le70K b) := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    change Bool.rec (motive := fun _ => Bool) false (le70K (a ++ b)) (Nat.ble (Char.toNat c) 70) =
      (Bool.rec (motive := fun _ => Bool) false (le70K a) (Nat.ble (Char.toNat c) 70) && le70K b)
    rw [ih]
    cases Nat.ble (Char.toNat c) 70 <;> rfl

@[expose] def Le70Str (s : String) : Prop := ∃ cs : List Char, s = String.ofList cs ∧ le70K cs = true

theorem Le70Str.append {s t : String} (hs : Le70Str s) (ht : Le70Str t) : Le70Str (s ++ t) := by
  obtain ⟨a, rfl, ha⟩ := hs
  obtain ⟨b, rfl, hb⟩ := ht
  exact ⟨a ++ b, String.ofList_append.symm, by rw [le70K_append, ha, hb]; rfl⟩

theorem Le70Str.hexAt_lt {s : String} (h : Le70Str s) (o d : Nat) :
    hexAt s.toUTF8 o d < 2 ^ (4 * d) := by
  obtain ⟨cs, rfl, hc⟩ := h
  exact hexAt_lt_of_le70 hc o d

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

open CFSG.Sporadic.Schreier.PairNative in
theorem incK_sound {n : Nat} : ∀ {o : List Nat} {lo : Nat}, incK n o lo = true →
    strictInc o = true ∧ ∀ x ∈ o, lo ≤ x ∧ x < n := by
  intro o
  induction o with
  | nil => intro _ _; exact ⟨rfl, by simp⟩
  | cons x o ih =>
    intro lo h
    change bAnd(Nat.ble lo x, bAnd(Nat.blt x n, incK n o (Nat.succ x))) = true at h
    rw [bAnd_iff, bAnd_iff, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨hs, hb⟩ := ih h3
    refine ⟨?_, ?_⟩
    · cases o with
      | nil => rfl
      | cons y o =>
        have hy := (hb y (List.mem_cons_self ..)).1
        simp only [strictInc, hs, Bool.and_true, decide_eq_true_eq]
        omega
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨h1, h2⟩
      · have := hb y hy
        omega

theorem nilLK_sound {α : Type} {l : List α} (h : nilLK l = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => exact absurd h Bool.false_ne_true

open CFSG.Sporadic.Schreier.PairNative in
theorem orbsK_sound {n : Nat} : ∀ {os : List (List Nat)} {ls : List Nat}, orbsK n os ls = true →
    os.map List.length = ls ∧ ∀ o ∈ os, strictInc o = true ∧ ∀ x ∈ o, x < n := by
  intro os
  induction os with
  | nil => intro ls h; exact ⟨(nilLK_sound h).symm, by simp⟩
  | cons o os ih =>
    intro ls h
    cases ls with
    | nil => exact absurd h Bool.false_ne_true
    | cons l ls =>
      change bAnd(Nat.beq (lenK o) l, bAnd(incK n o 0, orbsK n os ls)) = true at h
      rw [bAnd_iff, bAnd_iff, Nat.beq_eq, lenK_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨hm, ha⟩ := ih h3
      obtain ⟨hs, hb⟩ := incK_sound h2
      refine ⟨by rw [List.map_cons, h1, hm], ?_⟩
      intro o' ho
      rcases List.mem_cons.1 ho with rfl | ho
      · exact ⟨hs, fun x hx => (hb x hx).2⟩
      · exact ha o' ho

theorem trisK_sound {n : Nat} : ∀ {ts : List (Nat × Nat × Nat)}, trisK n ts = true →
    ∀ t ∈ ts, t.1 < 2 ∧ t.2.1 < n ∧ t.2.2 < n := by
  intro ts
  induction ts with
  | nil => intro _ t ht; simp at ht
  | cons t ts ih =>
    intro h
    obtain ⟨i, u, v⟩ := t
    change bAnd(Nat.blt i 2, bAnd(Nat.blt u n, bAnd(Nat.blt v n, trisK n ts))) = true at h
    rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨h1, h2, h3⟩
    · exact ih h4 t ht

theorem msK_sound {n c : Nat} : ∀ {ms : List (Nat × List (Nat × Nat × Nat))} {rs : List Nat},
    msK n c ms rs = true → ms.map Prod.fst = rs ∧
      ∀ m ∈ ms, m.2.length = c ∧ ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < n ∧ t.2.2 < n := by
  intro ms
  induction ms with
  | nil => intro rs h; exact ⟨(nilLK_sound h).symm, by simp⟩
  | cons m ms ih =>
    intro rs h
    cases rs with
    | nil => exact absurd h Bool.false_ne_true
    | cons r rs =>
      obtain ⟨a, ts⟩ := m
      change bAnd(Nat.beq a r, bAnd(Nat.beq (lenK ts) c, bAnd(trisK n ts, msK n c ms rs))) = true
        at h
      rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.beq_eq, Nat.beq_eq, lenK_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨hm, ha⟩ := ih h4
      refine ⟨by rw [List.map_cons, h1, hm], ?_⟩
      intro m hm'
      rcases List.mem_cons.1 hm' with rfl | hm'
      · exact ⟨h2, trisK_sound h3⟩
      · exact ha m hm'

theorem stabK_sound {n c : Nat} {ls rs : List Nat}
    {R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))} (h : stabK n c ls rs R = true) :
    (R.1.map List.length = ls ∧
      ∀ o ∈ R.1, CFSG.Sporadic.Schreier.PairNative.strictInc o = true ∧ ∀ x ∈ o, x < n) ∧
      R.2.map Prod.fst = rs ∧
      ∀ m ∈ R.2, m.2.length = c ∧ ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < n ∧ t.2.2 < n := by
  obtain ⟨os, ms⟩ := R
  change bAnd(orbsK n os ls, msK n c ms rs) = true at h
  rw [bAnd_iff] at h
  exact ⟨orbsK_sound h.1, msK_sound h.2⟩

open CFSG.Sporadic.Schreier.PairNative in
theorem stab_checks {R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))}
    (h : stabK 6156 6154 [1, 1360, 2040, 1360, 510, 680, 120, 85] [1, 4, 7, 8, 26, 47, 205] R =
      true) :
    (R.1.length == 8) = true ∧
      R.1.all (fun o => strictInc o && o.all (· < 6156)) = true ∧
      (R.1.map List.length == [1, 1360, 2040, 1360, 510, 680, 120, 85]) = true ∧
      (R.2.map Prod.fst == [1, 4, 7, 8, 26, 47, 205]) = true ∧
      (R.2.map (fun m => m.2.length) == [6154, 6154, 6154, 6154, 6154, 6154, 6154]) = true ∧
      R.2.all (fun m => m.2.all fun t => decide (t.1 < 2) && decide (t.2.1 < 6156) &&
        decide (t.2.2 < 6156)) = true := by
  obtain ⟨⟨hl, ho⟩, hr, hm⟩ := stabK_sound h
  refine ⟨?_, ?_, by rw [hl]; rfl, by rw [hr]; rfl, ?_, ?_⟩
  · have := congrArg List.length hl
    rw [List.length_map] at this
    rw [this]
    rfl
  · rw [List.all_eq_true]
    intro o h'
    obtain ⟨h1, h2⟩ := ho o h'
    simp only [h1, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    exact h2
  · have e : R.2.map (fun m => m.2.length) = R.2.map (fun _ => 6154) :=
      List.map_congr_left fun m h' => (hm m h').1
    rw [e, List.map_const', ← List.length_map Prod.fst, hr]
    rfl
  · rw [List.all_eq_true]
    intro m h'
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact fun t ht => ⟨⟨(((hm m h').2 t ht).1), ((hm m h').2 t ht).2.1⟩, ((hm m h').2 t ht).2.2⟩

open CFSG.Sporadic.Schreier.PairF2

theorem tri_succ (i : Nat) : (i + 1) * (i + 1 - 1) / 2 = i * (i - 1) / 2 + i := by
  cases i with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num)]

theorem flat_len (d : Nat) : ∀ i, i ≤ d →
    ((List.range i).flatMap fun a => (List.range (d - a)).map fun k => (a, a + k)).length +
      i * (i - 1) / 2 = d * i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_map, List.length_range, tri_succ,
      Nat.mul_succ]
    generalize d * i = D at h ⊢
    generalize i * (i - 1) / 2 = T at h ⊢
    omega

theorem monomials_length (d : Nat) : (monomials d).length + d * (d - 1) / 2 = d * d :=
  flat_len d d le_rfl

theorem monomials_get (d i j : Nat) (hij : i ≤ j) (hj : j < d) :
    (monomials d)[pairIdx d i j]? = some (i, j) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = i + (m + 1) := ⟨d - i - 1, by omega⟩
  have hP := flat_len (i + (m + 1)) i (by omega)
  have hidx : pairIdx (i + (m + 1)) i j =
      ((List.range i).flatMap fun a => (List.range (i + (m + 1) - a)).map fun k => (a, a + k)).length +
        (j - i) := by
    unfold pairIdx
    generalize (i + (m + 1)) * i = D at hP ⊢
    generalize i * (i - 1) / 2 = T at hP ⊢
    omega
  rw [hidx, monomials, List.range_add, List.flatMap_append, List.range_succ_eq_map, List.map_cons,
    List.flatMap_cons, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simp; omega)]
  simp only [Nat.add_zero, Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range
    (by omega : j - i < m + 1), Option.map_some]
  congr 2
  omega

theorem monomials_checks : ((monomials 80).length == 3240) = true ∧
    (List.range 80).all (fun i => (List.range 80).all fun j =>
      !decide (i ≤ j) || (monomials 80)[pairIdx 80 i j]? == some (i, j)) = true := by
  refine ⟨?_, ?_⟩
  · have h := monomials_length 80
    rw [beq_iff_eq]
    generalize (monomials 80).length = L at h ⊢
    omega
  · simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, beq_iff_eq]
    intro i _ j hj
    by_cases h : i ≤ j
    · exact Or.inr (monomials_get 80 i j h hj)
    · exact Or.inl h

namespace PJ3Enc

open CFSG.Sporadic.Schreier.PairText

theorem natsI_eq (l : List Nat) (tl : List Int) : natsI l tl = l.map Int.ofNat ++ tl := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (Int.ofNat x :: ·) ih

theorem orbsI_eq (os : List (List Nat)) (tl : List Int) : orbsI os tl = orbsI os [] ++ tl := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    change Int.ofNat (lenK o) :: natsI o (orbsI os tl) =
      (Int.ofNat (lenK o) :: natsI o (orbsI os [])) ++ tl
    rw [natsI_eq, natsI_eq, ih]
    simp

theorem trisI_eq (ts : List (Nat × Nat × Nat)) (tl : List Int) : trisI ts tl = trisI ts [] ++ tl := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change _ :: _ :: _ :: trisI ts tl = (_ :: _ :: _ :: trisI ts []) ++ tl
    rw [ih]
    simp

theorem trisI_length (ts : List (Nat × Nat × Nat)) : (trisI ts []).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (trisI ts []).length + 3 = 3 * (ts.length + 1)
    omega

theorem msI_eq (ms : List (Nat × List (Nat × Nat × Nat))) (tl : List Int) :
    msI ms tl = msI ms [] ++ tl := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change _ :: _ :: trisI m.2 (msI ms tl) = (_ :: _ :: trisI m.2 (msI ms [])) ++ tl
    rw [trisI_eq, trisI_eq m.2 (msI ms []), ih]
    simp

theorem get_toArray (L : List Int) (i : Nat) : L.toArray[i]! = L.getD i 0 := by
  simp only [getElem!_def, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  cases L[i]? <;> rfl

theorem getD_mid (P R : List Int) (x : Int) : (P ++ x :: R).getD P.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_mid' (P R : List Int) (k : Nat) (hk : k < R.length) :
    (P ++ R).getD (P.length + k) 0 = R[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hk]

theorem getD_app (P A R : List Int) (i : Nat) (hi : i < A.length) :
    (P ++ (A ++ R)).getD (P.length + i) 0 = A.getD i 0 := by
  rw [getD_mid' _ _ _ (by simp; omega), List.getElem_append_left hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

@[expose] def stO (t : Array Int) (b : Nat × Array (List Nat)) (_ : Nat) : Nat × Array (List Nat) :=
  (b.1 + 1 + t[b.1]!.toNat, b.2.push (tokNats t (b.1 + 1) t[b.1]!.toNat).toList)

theorem tokNats_eq (P R : List Int) (o : List Nat) :
    (tokNats (P ++ Int.ofNat o.length :: o.map Int.ofNat ++ R).toArray (P.length + 1)
      o.length).toList = o := by
  rw [List.append_assoc, List.cons_append]
  apply List.ext_getElem (by simp [tokNats])
  intro j h1 h2
  simp only [tokNats, Array.toList_ofFn, List.getElem_ofFn, get_toArray]
  have e : P.length + 1 + j = P.length + (1 + j) := by omega
  rw [e, getD_mid' _ _ _ (by simp; omega)]
  simp [List.getElem_cons, show 1 + j - 1 = j by omega,
    List.getElem_append_left (by simpa using h2 : j < (o.map Int.ofNat).length)]

theorem orbs_fold (os : List (List Nat)) (P tl : List Int) (acc : Array (List Nat))
    (xs : List Nat) (hx : xs.length = os.length) :
    xs.foldl (stO (P ++ orbsI os tl).toArray) (P.length, acc) =
      ((P ++ orbsI os []).length, acc ++ os.toArray) := by
  induction os generalizing P acc xs with
  | nil =>
    rw [List.length_eq_zero_iff.1 hx]
    simp [orbsI]
  | cons o os ih =>
    obtain ⟨a, xs, rfl⟩ : ∃ a xs', xs = a :: xs' := by
      cases xs with
      | nil => simp at hx
      | cons a xs' => exact ⟨a, xs', rfl⟩
    have hP : P ++ orbsI (o :: os) tl =
        (P ++ Int.ofNat o.length :: o.map Int.ofNat) ++ orbsI os tl := by
      change P ++ (Int.ofNat (lenK o) :: natsI o (orbsI os tl)) = _
      rw [lenK_eq, natsI_eq]
      simp
    have hP0 : P ++ orbsI (o :: os) [] =
        (P ++ Int.ofNat o.length :: o.map Int.ofNat) ++ orbsI os [] := by
      change P ++ (Int.ofNat (lenK o) :: natsI o (orbsI os [])) = _
      rw [lenK_eq, natsI_eq]
      simp
    have hs : stO (P ++ orbsI (o :: os) tl).toArray (P.length, acc) a =
        ((P ++ Int.ofNat o.length :: o.map Int.ofNat).length, acc.push o) := by
      have h0 : (P ++ orbsI (o :: os) tl).toArray[P.length]! = Int.ofNat o.length := by
        rw [get_toArray, hP, List.append_assoc, List.cons_append, getD_mid]
      unfold stO
      have e : (Int.ofNat o.length).toNat = o.length := rfl
      dsimp only
      rw [h0, hP, e, tokNats_eq]
      simp only [List.length_append, List.length_cons, List.length_map]
      congr 1
      omega
    rw [List.foldl_cons, hs, hP, hP0, ih _ _ _ (by simpa using hx)]
    simp

@[expose] def stMg (t : Array Int) (b : Nat × Array (Nat × List (Nat × Nat × Nat))) (_ : Nat) :
    Nat × Array (Nat × List (Nat × Nat × Nat)) :=
  (b.1 + 2 + 3 * t[b.1 + 1]!.toNat, b.2.push (t[b.1]!.toNat, List.map
    (fun k => (t[b.1 + 2 + 3 * k]!.toNat, t[b.1 + 3 + 3 * k]!.toNat, t[b.1 + 4 + 3 * k]!.toNat))
    (List.range t[b.1 + 1]!.toNat)))

theorem trisI_get (ts : List (Nat × Nat × Nat)) (k : Nat) (hk : k < ts.length) :
    (trisI ts []).getD (3 * k) 0 = Int.ofNat ts[k].1 ∧
      (trisI ts []).getD (3 * k + 1) 0 = Int.ofNat ts[k].2.1 ∧
      (trisI ts []).getD (3 * k + 2) 0 = Int.ofNat ts[k].2.2 := by
  induction ts generalizing k with
  | nil => simp at hk
  | cons t ts ih =>
    change (_ :: _ :: _ :: trisI ts []).getD _ 0 = _ ∧ (_ :: _ :: _ :: trisI ts []).getD _ 0 = _ ∧
      (_ :: _ :: _ :: trisI ts []).getD _ 0 = _
    rcases k with _ | k
    · simp
    · have h := ih k (by simpa using hk)
      have e1 : 3 * (k + 1) = 3 * k + 3 := by ring
      simp only [e1, List.getD_cons_succ, List.getElem_cons_succ]
      exact h

theorem tris_map (P R : List Int) (ts : List (Nat × Nat × Nat)) :
    List.map (fun k => (((P ++ trisI ts [] ++ R).toArray)[P.length + 3 * k]!.toNat,
      ((P ++ trisI ts [] ++ R).toArray)[P.length + 3 * k + 1]!.toNat,
      ((P ++ trisI ts [] ++ R).toArray)[P.length + 3 * k + 2]!.toNat)) (List.range ts.length) = ts := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have hk : k < ts.length := by simpa using h1
  have hl := trisI_length ts
  obtain ⟨g1, g2, g3⟩ := trisI_get ts k hk
  simp only [List.getElem_map, List.getElem_range, get_toArray, List.append_assoc]
  have a1 : P.length + 3 * k + 1 = P.length + (3 * k + 1) := by omega
  have a2 : P.length + 3 * k + 2 = P.length + (3 * k + 2) := by omega
  rw [a1, a2, getD_app _ _ _ _ (by omega), getD_app _ _ _ _ (by omega),
    getD_app _ _ _ _ (by omega), g1, g2, g3]
  rfl

theorem ms_fold (ms : List (Nat × List (Nat × Nat × Nat))) (P tl : List Int)
    (acc : Array (Nat × List (Nat × Nat × Nat))) (xs : List Nat) (hx : xs.length = ms.length) :
    xs.foldl (stMg (P ++ msI ms tl).toArray) (P.length, acc) =
      ((P ++ msI ms []).length, acc ++ ms.toArray) := by
  induction ms generalizing P acc xs with
  | nil =>
    rw [List.length_eq_zero_iff.1 hx]
    simp [msI]
  | cons m ms ih =>
    obtain ⟨a, xs, rfl⟩ : ∃ a xs', xs = a :: xs' := by
      cases xs with
      | nil => simp at hx
      | cons a xs' => exact ⟨a, xs', rfl⟩
    have hP : P ++ msI (m :: ms) tl =
        (P ++ [Int.ofNat m.1, Int.ofNat m.2.length] ++ trisI m.2 []) ++ msI ms tl := by
      change P ++ (Int.ofNat m.1 :: Int.ofNat (lenK m.2) :: trisI m.2 (msI ms tl)) = _
      rw [lenK_eq, trisI_eq]
      simp
    have hP0 : P ++ msI (m :: ms) [] =
        (P ++ [Int.ofNat m.1, Int.ofNat m.2.length] ++ trisI m.2 []) ++ msI ms [] := by
      change P ++ (Int.ofNat m.1 :: Int.ofNat (lenK m.2) :: trisI m.2 (msI ms [])) = _
      rw [lenK_eq, trisI_eq]
      simp
    have hs : stMg (P ++ msI (m :: ms) tl).toArray (P.length, acc) a =
        ((P ++ [Int.ofNat m.1, Int.ofNat m.2.length] ++ trisI m.2 []).length, acc.push m) := by
      have h0 : (P ++ msI (m :: ms) tl).toArray[P.length]! = Int.ofNat m.1 := by
        rw [get_toArray, hP]
        simp [List.getD_eq_getElem?_getD, List.append_assoc]
      have h1 : (P ++ msI (m :: ms) tl).toArray[P.length + 1]! = Int.ofNat m.2.length := by
        rw [get_toArray, hP, List.append_assoc, List.append_assoc, getD_mid' _ _ _ (by simp)]
        simp
      unfold stMg
      dsimp only
      rw [h0, h1]
      have e : ∀ x : Nat, (Int.ofNat x).toNat = x := fun _ => rfl
      rw [e, e]
      have ht := tris_map (P ++ [Int.ofNat m.1, Int.ofNat m.2.length]) (msI ms tl) m.2
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have e2 : ∀ k, P.length + 2 + 3 * k = P.length + (0 + 1 + 1) + 3 * k := fun k => by omega
      have e3 : ∀ k, P.length + 3 + 3 * k = P.length + (0 + 1 + 1) + 3 * k + 1 := fun k => by omega
      have e4 : ∀ k, P.length + 4 + 3 * k = P.length + (0 + 1 + 1) + 3 * k + 2 := fun k => by omega
      simp only [e2, e3, e4]
      rw [hP, ht]
      refine Prod.ext ?_ rfl
      simp [trisI_length]
      omega
    rw [List.foldl_cons, hs, hP, hP0, ih _ _ _ (by simpa using hx)]
    simp

theorem parse_encOM (R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))) :
    parseOrbitsMerges (encOM R).toArray = R := by
  obtain ⟨os, ms⟩ := R
  have hE : encOM (os, ms) = [Int.ofNat os.length] ++ orbsI os (Int.ofNat ms.length :: msI ms []) := by
    change Int.ofNat (lenK os) :: orbsI os (Int.ofNat (lenK ms) :: msI ms []) = _
    rw [lenK_eq, lenK_eq]
    rfl
  have h0 : (encOM (os, ms)).toArray[0]! = Int.ofNat os.length := by
    rw [get_toArray, hE]
    rfl
  have hO := orbs_fold os [Int.ofNat os.length] (Int.ofNat ms.length :: msI ms []) #[]
    (List.range' 0 os.length) (by simp)
  have hE2 : encOM (os, ms) = ([Int.ofNat os.length] ++ orbsI os [] ++ [Int.ofNat ms.length]) ++
      msI ms [] := by
    rw [hE, orbsI_eq]
    simp
  have h1 : (encOM (os, ms)).toArray[([Int.ofNat os.length] ++ orbsI os []).length]! =
      Int.ofNat ms.length := by
    rw [get_toArray, hE2, List.append_assoc]
    exact getD_mid _ (msI ms []) _
  have hM := ms_fold ms ([Int.ofNat os.length] ++ orbsI os [] ++ [Int.ofNat ms.length]) [] #[]
    (List.range' 0 ms.length) (by simp)
  unfold parseOrbitsMerges
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind]
  rw [h0]
  have e : ∀ x : Nat, (Int.ofNat x).toNat = x := fun _ => rfl
  simp only [e, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← hE] at hO
  unfold stO at hO
  have h1l : [Int.ofNat os.length].length = 1 := rfl
  rw [h1l] at hO
  rw [hO]
  dsimp only
  rw [h1, e]
  have hlen : ([Int.ofNat os.length] ++ orbsI os [] ++ [Int.ofNat ms.length]).length =
      ([Int.ofNat os.length] ++ orbsI os []).length + 1 := by simp
  rw [← hE2, hlen] at hM
  unfold stMg at hM
  rw [hM]
  simp
  rfl

end PJ3Enc

end CFSG.KS.SporSch

end
