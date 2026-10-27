module

public import Certificates.Data.Kernel.Co2SmithS.Spin
public import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Co2SmithS

open CFSG.Sporadic.Co2Smith.Native

@[expose] def ofCols (C : List (List Int)) : Array Int :=
  Array.ofFn (n := 64) fun k => (C.getD (k.val % 8) []).getD (k.val / 8) 0

@[expose] def WF8 (C : List (List Int)) : Prop := C.length = 8 ∧ ∀ c ∈ C, c.length = 8

theorem ofCols_get (C : List (List Int)) {i : Nat} (hi : i < 64) :
    (ofCols C)[i]! = (C.getD (i % 8) []).getD (i / 8) 0 := by
  rw [getElem!_pos (ofCols C) i (by simp [ofCols, hi])]
  simp [ofCols]

theorem getD_map {α β : Type} (f : α → β) {l : List α} {i : Nat} (d : α) (e : β)
    (hi : i < l.length) : (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

theorem rowsL_get (A : Array Int) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    ((rowsL A).getD i []).getD j 0 = A[8 * i + j]! := by
  rw [rowsL, getD_map _ 0 [] (by simpa using hi), getD_map _ 0 0 (by simpa using hj)]
  simp [List.getD_eq_getElem, hi, hj]

theorem rowsL_length (A : Array Int) : (rowsL A).length = 8 := by simp [rowsL]

theorem mulLC_length (R C : List (List Int)) : (mulLC R C).length = C.length := by simp [mulLC]

theorem mulZ_size (A B : Array Int) : (mulZ A B).size = 64 := by
  unfold mulZ
  exact Array.size_ofFn

theorem ofCols_size (C : List (List Int)) : (ofCols C).size = 64 := by
  unfold ofCols
  exact Array.size_ofFn

theorem mulZ_get (A B : Array Int) {k : Nat} (hk : k < 64) : (mulZ A B)[k]! =
    A[8 * (k / 8)]! * B[k % 8]! + A[8 * (k / 8) + 1]! * B[8 + k % 8]! +
      A[8 * (k / 8) + 2]! * B[16 + k % 8]! + A[8 * (k / 8) + 3]! * B[24 + k % 8]! +
      A[8 * (k / 8) + 4]! * B[32 + k % 8]! + A[8 * (k / 8) + 5]! * B[40 + k % 8]! +
      A[8 * (k / 8) + 6]! * B[48 + k % 8]! + A[8 * (k / 8) + 7]! * B[56 + k % 8]! := by
  rw [getElem!_pos (mulZ A B) k (by rw [mulZ_size]; exact hk)]
  unfold mulZ
  rw [Array.getElem_ofFn]

theorem col_get (C : List (List Int)) {r : Nat} (hr : r < 8) {t : Nat} (ht : t < 8) {i : Nat}
    (hi : i = 8 * t + r) : (ofCols C)[i]! = (C.getD r []).getD t 0 := by
  rw [ofCols_get _ (by omega)]
  have e1 : i % 8 = r := by omega
  have e2 : i / 8 = t := by omega
  rw [e1, e2]

theorem row_get (A : Array Int) {q : Nat} (hq : q < 8) {j : Nat} (hj : j < 8) {i : Nat}
    (hi : i = 8 * q + j) : ((rowsL A).getD q []).getD j 0 = A[i]! := by
  rw [rowsL_get A hq hj, hi]

theorem mulZ_ofCols_key (A : Array Int) {C : List (List Int)} (hC : C.length = 8) {k : Nat}
    (hk : k < 64) : (mulZ A (ofCols C))[k]! = (ofCols (mulLC (rowsL A) C))[k]! := by
    have hr : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hq : k / 8 < 8 := by omega
    rw [ofCols_get (mulLC (rowsL A) C) hk, mulLC, getD_map _ [] [] (by omega),
      getD_map _ [] 0 (by rw [rowsL_length]; exact hq), mulZ_get A (ofCols C) hk]
    unfold dot8
    rw [col_get C hr (t := 0) (by omega) (i := k % 8) (by omega),
      col_get C hr (t := 1) (by omega) (i := 8 + k % 8) (by omega),
      col_get C hr (t := 2) (by omega) (i := 16 + k % 8) (by omega),
      col_get C hr (t := 3) (by omega) (i := 24 + k % 8) (by omega),
      col_get C hr (t := 4) (by omega) (i := 32 + k % 8) (by omega),
      col_get C hr (t := 5) (by omega) (i := 40 + k % 8) (by omega),
      col_get C hr (t := 6) (by omega) (i := 48 + k % 8) (by omega),
      col_get C hr (t := 7) (by omega) (i := 56 + k % 8) (by omega),
      row_get A hq (j := 0) (by omega) (i := 8 * (k / 8)) (by omega),
      row_get A hq (j := 1) (by omega) rfl, row_get A hq (j := 2) (by omega) rfl,
      row_get A hq (j := 3) (by omega) rfl, row_get A hq (j := 4) (by omega) rfl,
      row_get A hq (j := 5) (by omega) rfl, row_get A hq (j := 6) (by omega) rfl,
      row_get A hq (j := 7) (by omega) rfl]

theorem ext64 {a b : Array Int} (ha : a.size = 64) (hb : b.size = 64)
    (h : ∀ k < 64, a[k]! = b[k]!) : a = b := by
  apply Array.ext (ha.trans hb.symm)
  intro k h1 h2
  have hk : k < 64 := ha ▸ h1
  rw [← getElem!_pos a k h1, ← getElem!_pos b k h2]
  exact h k hk

theorem mulZ_ofCols (A : Array Int) {C : List (List Int)} (hC : C.length = 8) :
    mulZ A (ofCols C) = ofCols (mulLC (rowsL A) C) :=
  ext64 (mulZ_size _ _) (ofCols_size _) fun _ hk => mulZ_ofCols_key A hC hk

theorem wordC_length : ∀ w : List Nat, (wordC w).length = 8
  | [] => by simp [wordC, idC]
  | k :: w => by
    have e : wordC (k :: w) = mulLC (spinRows k) (wordC w) := rfl
    rw [e, mulLC_length, wordC_length w]

theorem wordC_wf : ∀ w : List Nat, WF8 (wordC w)
  | [] => ⟨by simp [wordC, idC], fun c hc => by
      simp only [wordC, List.foldr_nil, idC, List.mem_map, List.mem_range] at hc
      obtain ⟨j, -, rfl⟩ := hc
      simp⟩
  | k :: w => by
    have e : wordC (k :: w) = mulLC (spinRows k) (wordC w) := rfl
    refine ⟨by rw [wordC_length], fun c hc => ?_⟩
    rw [e, mulLC, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp [spinRows, rowsL_length]

theorem idZ_eq : idZ () = ofCols idC := by decide +kernel

theorem negIdZ_eq : negIdZ () = ofCols negC := by decide +kernel

theorem wordZ_eq : ∀ w : List Nat, wordZ w = ofCols (wordC w)
  | [] => idZ_eq
  | k :: w => by
    have e1 : wordZ (k :: w) = mulZ (spinMats ())[k]! (wordZ w) := rfl
    have e2 : wordC (k :: w) = mulLC (spinRows k) (wordC w) := rfl
    rw [e1, e2, wordZ_eq w, mulZ_ofCols _ (wordC_length w)]
    rfl

theorem ofCols_inj {C D : List (List Int)} (hC : WF8 C) (hD : WF8 D) (h : ofCols C = ofCols D) :
    C = D := by
  apply List.ext_getElem (hC.1.trans hD.1.symm)
  intro r h1 h2
  have hr : r < 8 := hC.1 ▸ h1
  have hc := hC.2 _ (List.getElem_mem h1)
  have hd := hD.2 _ (List.getElem_mem h2)
  apply List.ext_getElem (hc.trans hd.symm)
  intro t t1 t2
  have ht : t < 8 := hc ▸ t1
  have e : (ofCols C)[8 * t + r]! = (ofCols D)[8 * t + r]! := by rw [h]
  rw [ofCols_get _ (by omega), ofCols_get _ (by omega)] at e
  have e1 : (8 * t + r) % 8 = r := by omega
  have e2 : (8 * t + r) / 8 = t := by omega
  rw [e1, e2, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2,
    List.getD_eq_getElem _ _ t1, List.getD_eq_getElem _ _ t2] at e
  exact e

theorem beq_ofCols {C D : List (List Int)} (hC : WF8 C) (hD : WF8 D) :
    (ofCols C == ofCols D) = (C == D) := by
  by_cases h : C = D
  · subst h
    simp
  · have h' : ofCols C ≠ ofCols D := fun e => h (ofCols_inj hC hD e)
    simp [h, h']

theorem idC_wf : WF8 idC := wordC_wf []

theorem negC_wf : WF8 negC := ⟨by simp [negC], fun c hc => by
  simp only [negC, List.mem_map, List.mem_range] at hc
  obtain ⟨j, -, rfl⟩ := hc
  simp⟩

theorem spinCheck_eq : spinCheck () = spinCheckK := by
  unfold spinCheck spinCheckK
  have hw : ∀ w, (wordZ w == idZ ()) = (wordC w == idC) := fun w => by
    rw [wordZ_eq, idZ_eq, beq_ofCols (wordC_wf w) idC_wf]
  simp only [hw]
  rw [wordZ_eq, negIdZ_eq, beq_ofCols (wordC_wf _) negC_wf]

end CFSG.KC.Co2SmithS

end
