module

public import Certificates.Data.Kernel.SmithEK
public import CFSG.LargeExtraspecial.SMod20AutPluck
import CFSG.Fischer.F4
public import CFSG.Fischer.UnitaryAction
public import Mathlib

public section

namespace CFSG.SmithE.K

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE CFSG.LargeExtraspecial.SMod20.Aut Matrix

@[expose] def xN (p i : Nat) : F4 := ⟨⟨coord p i, by unfold coord; omega⟩⟩

@[expose] def tvE (p : Nat) (r c : Fin 6) : F4 := (if r = c then 1 else 0) + xN p r * (xN p c * xN p c)

theorem tvEntry_code (p : Nat) (r c : Fin 6) : tvEntry p r.val c.val = (tvE p r c).code.val := by
  unfold tvEntry tvE f4sq
  rw [code_add, code_mul, code_mul]
  congr 1
  by_cases h : r = c
  · simp only [h, if_true]
    rfl
  · have h' : r.val ≠ c.val := fun e => h (Fin.ext e)
    simp only [h, h', if_false]
    rfl

theorem minor_eq_det (p : Nat) (s t : Fin 20) :
    minor (tvEntry p) s.val t.val =
      (Matrix.of fun a b => tvE p (triTab s a) (triTab t b)).det.code.val := by
  unfold minor
  rw [tri_get s, tri_get t, ← det3_code]
  simp only [Matrix.of_apply, tvEntry_code]

theorem neg_F4 (z : F4) : -z = z := rfl

@[expose] def RowEq (p : Nat) (s t : Fin 20) : Prop :=
  (Matrix.of fun a b => tvE p (triTab s a) (triTab t b)).det =
    minorG 0 1 (· + ·) (· * ·) (xN p) s.val t.val

local macro "row_tac" s:term:max t:ident : tactic => `(tactic| (
  unfold RowEq minorG
  rw [tri_get $s, tri_get $t, det_fin_three]
  fin_cases $t:ident <;> simp [tvE, triTab] <;> first | ring1 | (refine Eq.trans ?_ (neg_F4 _); ring1)))

theorem rowEq0 (p : Nat) (t : Fin 20) : RowEq p 0 t := by row_tac 0 t
theorem rowEq1 (p : Nat) (t : Fin 20) : RowEq p 1 t := by row_tac 1 t
theorem rowEq2 (p : Nat) (t : Fin 20) : RowEq p 2 t := by row_tac 2 t
theorem rowEq3 (p : Nat) (t : Fin 20) : RowEq p 3 t := by row_tac 3 t
theorem rowEq4 (p : Nat) (t : Fin 20) : RowEq p 4 t := by row_tac 4 t
theorem rowEq5 (p : Nat) (t : Fin 20) : RowEq p 5 t := by row_tac 5 t
theorem rowEq6 (p : Nat) (t : Fin 20) : RowEq p 6 t := by row_tac 6 t
theorem rowEq7 (p : Nat) (t : Fin 20) : RowEq p 7 t := by row_tac 7 t
theorem rowEq8 (p : Nat) (t : Fin 20) : RowEq p 8 t := by row_tac 8 t
theorem rowEq9 (p : Nat) (t : Fin 20) : RowEq p 9 t := by row_tac 9 t

theorem rowEq (p : Nat) (s t : Fin 20) (hs : s.val < 10) : RowEq p s t := by
  obtain ⟨s, hs'⟩ := s
  simp only at hs
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨
    s = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact rowEq0 p t
  · exact rowEq1 p t
  · exact rowEq2 p t
  · exact rowEq3 p t
  · exact rowEq4 p t
  · exact rowEq5 p t
  · exact rowEq6 p t
  · exact rowEq7 p t
  · exact rowEq8 p t
  · exact rowEq9 p t

theorem minorG_code (p s t : Nat) :
    (minorG 0 1 (· + ·) (· * ·) (xN p) s t).code.val = minorK p s t := by
  unfold minorK minorG
  generalize tri[s]! = A
  generalize tri[t]! = B
  obtain ⟨i0, i1, i2⟩ := A
  obtain ⟨j0, j1, j2⟩ := B
  dsimp only
  split_ifs <;> simp only [code_add, code_mul, code_zero] <;> rfl

theorem minor_eq_minorK (p : Nat) {s t : Nat} (hs : s < 10) (ht : t < 20) :
    minor (tvEntry p) s t = minorK p s t := by
  have h := minor_eq_det p ⟨s, by omega⟩ ⟨t, ht⟩
  have h2 : RowEq p ⟨s, by omega⟩ ⟨t, ht⟩ := rowEq p _ _ hs
  unfold RowEq at h2
  rw [h2, minorG_code] at h
  exact h

theorem compound_get (g : Nat → Nat → Nat) {k t : Nat} (hk : k < 10) (ht : t < 20) :
    (compound g)[k * 20 + t]! = minor g k t := by
  unfold compound
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  have h1 : (k * 20 + t) / 20 = k := by omega
  have h2 : (k * 20 + t) % 20 = t := by omega
  simp only [h1, h2]

theorem wcoef_pow : ∀ m < 20, ∀ t < 20, wcoef (2 ^ m) t =
    if t = m / 2 then 1 + m % 2 else if t = 19 - m / 2 then f4sq (1 + m % 2) else 0 := by
  decide +kernel

theorem f4mul_zero (x : Nat) : f4mul x 0 = 0 := by
  simp [f4mul]

theorem foldl_two (M : Nat → Nat) (u v : Nat) {i j : Nat} (hij : i < j) (n : Nat) :
    (List.range n).foldl (fun acc t =>
        acc ^^^ f4mul (M t) (if t = i then u else if t = j then v else 0)) 0 =
      (if i < n then f4mul (M i) u else 0) ^^^ (if j < n then f4mul (M j) v else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hi : n = i
    · subst hi
      have hj : n ≠ j := by omega
      simp only [if_true, hj, if_false, Nat.lt_irrefl, Nat.lt_succ_self, show ¬ j < n + 1 by omega,
        show ¬ j < n by omega, Nat.zero_xor, Nat.xor_zero]
    · by_cases hj : n = j
      · subst hj
        simp only [hi, if_false, if_true, Nat.lt_irrefl, Nat.lt_succ_self,
          show i < n + 1 by omega, show i < n by omega, Nat.xor_zero, Nat.xor_assoc]
      · simp only [hi, hj, if_false, f4mul_zero, Nat.xor_zero]
        have e1 : (i < n + 1) = (i < n) := propext ⟨fun h => by omega, fun h => by omega⟩
        have e2 : (j < n + 1) = (j < n) := propext ⟨fun h => by omega, fun h => by omega⟩
        simp only [e1, e2]

theorem wedgeAct_pow (p : Nat) {m : Nat} (hm : m < 20) :
    wedgeAct (compound (tvEntry p)) (2 ^ m) = colK p m := by
  unfold wedgeAct colK
  apply List.foldl_ext
  intro acc k hk
  have hk' : k < 10 := List.mem_range.1 hk
  congr 2
  have e : ∀ t ∈ List.range 20, ∀ a : Nat,
      a ^^^ f4mul (compound (tvEntry p))[k * 20 + t]! (wcoef (2 ^ m) t) =
        a ^^^ f4mul (minorK p k t)
          (if t = m / 2 then 1 + m % 2 else if t = 19 - m / 2 then f4sq (1 + m % 2) else 0) := by
    intro t ht a
    have ht' : t < 20 := List.mem_range.1 ht
    rw [compound_get _ hk' ht', minor_eq_minorK p hk' ht', wcoef_pow m hm t ht']
  rw [List.foldl_ext _ _ 0 (fun a t ht => e t ht a), foldl_two (minorK p k) _ _ (by omega) 20]
  simp only [show m / 2 < 20 by omega, show 19 - m / 2 < 20 by omega, if_true]

theorem tvCols_toList (k : Nat) : (tvCols k).toList = tvK (uPts ())[k]! := by
  unfold tvCols tvK
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact wedgeAct_pow _ (by simpa using h2)

theorem getElem!_toArray (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem tvCols_eq_of {L : List Nat} (hL : uPts () = L.toArray) (k : Nat) :
    tvCols k = (tvK (L.getD k 0)).toArray := by
  have h := tvCols_toList k
  rw [hL, getElem!_toArray] at h
  rw [← h, Array.toArray_toList]

end CFSG.SmithE.K
