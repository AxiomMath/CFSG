module

public import Certificates.Data.Kernel.M24G.Img
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

def orStep (c : Nat → Bool) (g : Nat → Nat) (acc i : Nat) : Nat :=
  if c i then acc ||| g i else acc

theorem foldl_orStep (c : Nat → Bool) (g : Nat → Nat) :
    ∀ (l : List Nat) (acc : Nat), l.foldl (orStep c g) acc = acc ||| l.foldl (orStep c g) 0
  | [], acc => by simp
  | a :: l, acc => by
    simp only [List.foldl_cons, orStep]
    by_cases h : c a
    · simp only [h, if_true, Nat.zero_or]
      rw [foldl_orStep c g l (acc ||| g a), foldl_orStep c g l (g a), Nat.or_assoc]
    · simp only [h, Bool.false_eq_true, if_false]
      exact foldl_orStep c g l acc

theorem foldl_orStep_congr {c c' : Nat → Bool} {g g' : Nat → Nat} :
    ∀ (l : List Nat) (acc : Nat), (∀ i ∈ l, c i = c' i ∧ g i = g' i) →
      l.foldl (orStep c g) acc = l.foldl (orStep c' g') acc
  | [], _, _ => rfl
  | a :: l, acc, h => by
    simp only [List.foldl_cons]
    have ha := h a List.mem_cons_self
    have e : orStep c g acc a = orStep c' g' acc a := by simp only [orStep, ha.1, ha.2]
    rw [e]
    exact foldl_orStep_congr l _ fun i hi => h i (List.mem_cons_of_mem a hi)

theorem foldl_orStep_lt (c : Nat → Bool) (g : Nat → Nat) (hg : ∀ i, g i < 2 ^ 24) :
    ∀ (l : List Nat) (acc : Nat), acc < 2 ^ 24 → l.foldl (orStep c g) acc < 2 ^ 24
  | [], _, h => h
  | a :: l, acc, h => by
    simp only [List.foldl_cons]
    refine foldl_orStep_lt c g hg l _ ?_
    unfold orStep
    split
    · exact Nat.or_lt_two_pow h (hg a)
    · exact h

theorem field24_pack24 : ∀ (l : List Nat), (∀ e ∈ l, e < 16777216) →
    ∀ b, field24 (pack24 l) b = l.getD b 0
  | [], _, b => by simp [field24, pack24]
  | e :: es, h, b => by
    have he := h e List.mem_cons_self
    unfold field24 pack24
    cases b with
    | zero =>
      simp only [Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]
      omega
    | succ b =>
      have e1 : 24 * (b + 1) = 24 + 24 * b := by omega
      rw [e1, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (e + pack24 es * 16777216) 24]
      have e2 : (e + pack24 es * 16777216) / 2 ^ 24 = pack24 es := by
        have : (2 : Nat) ^ 24 = 16777216 := by decide
        rw [this]
        omega
      rw [e2, List.getD_cons_succ]
      exact field24_pack24 es (fun x hx => h x (List.mem_cons_of_mem e hx)) b

theorem byteImg_lt {t : List Nat} (ht : ∀ x ∈ t, x < 24) (o b : Nat) :
    byteImg t o b < 16777216 := by
  have hg : ∀ i, 1 <<< t.getD (o + i) 0 < 2 ^ 24 := by
    intro i
    rw [Nat.one_shiftLeft]
    refine Nat.pow_lt_pow_right (by decide) ?_
    rw [List.getD_eq_getElem?_getD]
    cases hx : t[o + i]? with
    | none => simp
    | some x => exact ht x (List.mem_of_getElem? hx)
  have := foldl_orStep_lt (fun j => b.testBit j) (fun j => 1 <<< t.getD (o + j) 0) hg
    (List.range 8) 0 (by decide)
  exact this

theorem field24_byteTab {t : List Nat} (ht : ∀ x ∈ t, x < 24) (k : Nat) {b : Nat}
    (hb : b < 256) : field24 (byteTab t k) b = byteImg t (8 * k) b := by
  unfold byteTab
  rw [field24_pack24 _ (by
    intro e he
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 he
    exact byteImg_lt ht _ a)]
  simp [List.getD_eq_getElem?_getD, hb]

theorem arr_getElem! (xs : Array Nat) (i : Nat) : xs[i]! = xs.toList.getD i 0 := by
  rcases xs with ⟨l⟩
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem byte_foldl (t : Array Nat) (m o : Nat) :
    ((List.range 8).map (o + ·)).foldl
        (orStep (fun i => m.testBit i) (fun i => 1 <<< t[i]!)) 0 =
      byteImg t.toList o ((m >>> o) % 256) := by
  rw [List.foldl_map]
  unfold byteImg
  refine foldl_orStep_congr (List.range 8) 0 fun j hj => ⟨?_, ?_⟩
  · have hj' : j < 8 := List.mem_range.1 hj
    have e : (256 : Nat) = 2 ^ 8 := by decide
    simp only [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hj', decide_true,
      Bool.true_and]
  · simp only [arr_getElem!]

theorem range24 : List.range 24 =
    ((List.range 8).map (0 + ·) ++ (List.range 8).map (8 + ·)) ++ (List.range 8).map (16 + ·) := by
  decide

theorem img_eq_imgF (t : Array Nat) (ht : ∀ x ∈ t.toList, x < 24) (m : Nat) :
    Native.img t m = imgF (imgTab t.toList) m := by
  have e0 : Native.img t m =
      (List.range 24).foldl (orStep (fun i => m.testBit i) (fun i => 1 <<< t[i]!)) 0 := rfl
  rw [e0, range24, List.foldl_append, List.foldl_append,
    foldl_orStep _ _ ((List.range 8).map (8 + ·)),
    foldl_orStep _ _ ((List.range 8).map (16 + ·)), byte_foldl, byte_foldl, byte_foldl]
  unfold imgF imgTab
  rw [field24_byteTab ht 0 (Nat.mod_lt _ (by decide)),
    field24_byteTab ht 1 (Nat.mod_lt _ (by decide)),
    field24_byteTab ht 2 (Nat.mod_lt _ (by decide)), Nat.shiftRight_zero]

end CFSG.KC.M24G
