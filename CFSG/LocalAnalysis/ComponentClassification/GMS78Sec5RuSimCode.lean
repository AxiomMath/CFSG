module

public import Certificates.Data.GMS78RuSimCheck
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCode

public section

namespace CFSG.ComponentClassification.GMS78.RuSimCode

open CFSG.GMS78Ru CFSG.GMS78RuSim

local instance : Std.Associative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

local instance : Std.Commutative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

theorem fin8_xor_zero (a : Fin 8) : a ^^^ 0 = a := by revert a; decide
theorem fin8_zero_xor (a : Fin 8) : 0 ^^^ a = a := by revert a; decide
theorem fin8_xor_self (a : Fin 8) : a ^^^ a = 0 := by revert a; decide

theorem val_xor (a b : Fin 8) : (a ^^^ b).val = a.val ^^^ b.val := by
  rw [Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt)]

theorem testBit_xor (a b : Fin 8) (i : Nat) :
    (a ^^^ b).val.testBit i = (a.val.testBit i ^^ b.val.testBit i) := by
  rw [val_xor, Nat.testBit_xor]

theorem ite_xor (x y : Bool) (c : Fin 8) :
    (if (x ^^ y) = true then c else 0) =
      (if x = true then c else 0) ^^^ (if y = true then c else 0) := by
  cases x <;> cases y <;> simp [fin8_xor_zero, fin8_zero_xor, fin8_xor_self]

theorem linApply_xor (r : Lin8) (a b : Fin 8) :
    linApply r (a ^^^ b) = linApply r a ^^^ linApply r b := by
  simp only [linApply, testBit_xor, ite_xor]
  ac_rfl

theorem selB_xor (x y : Bool) (c : Nat) : selB (x ^^ y) c = selB x c ^^^ selB y c := by
  cases x <;> cases y <;> simp [selB]

theorem sel_xor (m m' k c : Nat) : sel (m ^^^ m') k c = sel m k c ^^^ sel m' k c := by
  simp only [sel, Nat.testBit_xor]
  cases m.testBit k <;> cases m'.testBit k <;> simp

theorem maskApply_xor (cols : List Nat) (m m' : Nat) :
    maskApply cols (m ^^^ m') = maskApply cols m ^^^ maskApply cols m' := by
  simp only [maskApply, sel_xor]
  ac_rfl

theorem sCoeff_xor : ∀ p q s s' : Fin 8, canon p q = true → s ∈ lamList p q → s' ∈ lamList p q →
    sCoeff p q (s ^^^ s') = ((sCoeff p q s).1 ^^ (sCoeff p q s').1,
      (sCoeff p q s).2 ^^ (sCoeff p q s').2) := by
  decide

theorem xApply_addV (X : List Nat) {p q : Fin 8} (hpq : canon p q = true) {w w' : V3}
    (hw : w.2.2 ∈ lamList p q) (hw' : w'.2.2 ∈ lamList p q) :
    xApply X p q (addV w w') = xApply X p q w ^^^ xApply X p q w' := by
  have hs := sCoeff_xor p q w.2.2 w'.2.2 hpq hw hw'
  simp only [xApply, addV, testBit_xor, hs, selB_xor]
  ac_rfl


theorem m3Eq_iff {A B : M3} : m3Eq A B = true ↔ A = B := by
  constructor
  · intro h
    funext i j
    simp only [m3Eq, List.all_eq_true, List.mem_finRange, beq_iff_eq, forall_const] at h
    exact h i j
  · rintro rfl
    simp [m3Eq]

theorem mem_all256 {m : Nat} : m ∈ all256 ↔ m < 256 := by simp [all256]

theorem s0_parts (h : s0Check = true) :
    steinData.map Prod.fst = specialList ∧
    (∀ r ∈ glList, linComp r (linInv r) = linId ∧ linComp (linInv r) r = linId ∧
      bmul (rhoMat r) (rhoMat (linInv r)) = m3One ∧ bmul (rhoMat (linInv r)) (rhoMat r) = m3One) ∧
    (∀ m < 256, matToSl (slToMat m) = m) ∧
    (∀ r ∈ glList, ∀ m < 256, slToMat (maskApply (adMat r) m) =
      bmul (bmul (rhoMat r) (slToMat m)) (rhoMat (linInv r))) ∧
    (∀ d ∈ steinData, (∀ w ∈ wList d.1.2.2.1 d.1.2.2.2,
      xiApply d.2.2 (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w) = w) ∧
      ∀ m < 256, xApply d.2.1 d.1.2.2.1 d.1.2.2.2 (xiApply d.2.2 m) = m ∧
        (xiApply d.2.2 m).2.2 ∈ lamList d.1.2.2.1 d.1.2.2.2) := by
  simp only [s0Check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, m3Eq_iff, mem_all256,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun r hr => ?_, h3, h4, h5⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h2 r hr
  exact ⟨a, b, c, d⟩


theorem lamList_xor : ∀ p q s s' : Fin 8, canon p q = true → s ∈ lamList p q →
    s' ∈ lamList p q → s ^^^ s' ∈ lamList p q := by
  decide

theorem canon_of_mem_specialList : ∀ t ∈ specialList, canon t.2.2.1 t.2.2.2 = true := by
  intro t ht
  simp only [specialList, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem addV_mem_wList {p q : Fin 8} (hpq : canon p q = true) {w w' : V3}
    (hw : w ∈ wList p q) (hw' : w' ∈ wList p q) : addV w w' ∈ wList p q :=
  RuCode.mem_wList.mpr (lamList_xor p q _ _ hpq (RuCode.mem_wList.mp hw) (RuCode.mem_wList.mp hw'))

theorem xor_lt {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

theorem selB_lt (b : Bool) {c : Nat} (hc : c < 256) : selB b c < 256 := by
  cases b <;> simp [selB, hc]

theorem sel_lt (m k : Nat) {c : Nat} (hc : c < 256) : sel m k c < 256 := by
  unfold sel; split <;> omega

theorem getD_lt {l : List Nat} (hl : ∀ x ∈ l, x < 256) (i : Nat) : l.getD i 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some x => simpa using hl x (List.mem_of_getElem? h)

theorem xApply_lt {X : List Nat} (hX : ∀ x ∈ X, x < 256) (p q : Fin 8) (w : V3) :
    xApply X p q w < 256 := by
  have h := getD_lt hX
  unfold xApply
  repeat' first | apply xor_lt | exact selB_lt _ (h _)

theorem maskApply_lt {cols : List Nat} (hc : ∀ x ∈ cols, x < 256) (m : Nat) :
    maskApply cols m < 256 := by
  have h := getD_lt hc
  unfold maskApply
  repeat' first | apply xor_lt | exact sel_lt _ _ (h _)

theorem bitVal_le (b : Bool) (k : Nat) : bitVal b k ≤ 2 ^ k := by
  cases b <;> simp [bitVal]

theorem matToSl_lt (A : M3) : matToSl A < 256 := by
  unfold matToSl
  have := bitVal_le (A 0 1) 0
  have := bitVal_le (A 0 2) 1
  have := bitVal_le (A 1 0) 2
  have := bitVal_le (A 1 2) 3
  have := bitVal_le (A 2 0) 4
  have := bitVal_le (A 2 1) 5
  have := bitVal_le (A 0 0) 6
  have := bitVal_le (A 2 2) 7
  simp only [pow_zero, pow_one] at *
  norm_num at *
  omega

theorem adMat_lt (r : Lin8) : ∀ x ∈ adMat r, x < 256 := by
  intro x hx
  simp only [adMat, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact matToSl_lt _

theorem steinData_lt : ∀ d ∈ steinData, ∀ x ∈ d.2.1, x < 256 := by
  intro d hd x hx
  simp only [steinData, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;> omega


abbrev SData : Type := (Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3

@[expose] def nMap (d : SData) (r : Lin8) (w : V3) : V3 :=
  xiApply d.2.2 (maskApply (adMat r) (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w))

section Data

variable (h0 : s0Check = true) {d : SData} (hd : d ∈ steinData)
include h0 hd

theorem canon_d : canon d.1.2.2.1 d.1.2.2.2 = true := by
  have h1 := (s0_parts h0).1
  have hmem : d.1 ∈ specialList := by rw [← h1]; exact List.mem_map_of_mem hd
  exact canon_of_mem_specialList _ hmem

theorem xiApply_xApply {w : V3} (hw : w ∈ wList d.1.2.2.1 d.1.2.2.2) :
    xiApply d.2.2 (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w) = w :=
  ((s0_parts h0).2.2.2.2 d hd).1 w hw

theorem xApply_xiApply {m : Nat} (hm : m < 256) :
    xApply d.2.1 d.1.2.2.1 d.1.2.2.2 (xiApply d.2.2 m) = m :=
  (((s0_parts h0).2.2.2.2 d hd).2 m hm).1

theorem xiApply_mem {m : Nat} (hm : m < 256) :
    xiApply d.2.2 m ∈ wList d.1.2.2.1 d.1.2.2.2 :=
  RuCode.mem_wList.mpr (((s0_parts h0).2.2.2.2 d hd).2 m hm).2

theorem xiApply_xor {m m' : Nat} (hm : m < 256) (hm' : m' < 256) :
    xiApply d.2.2 (m ^^^ m') = addV (xiApply d.2.2 m) (xiApply d.2.2 m') := by
  have hc := canon_d h0 hd
  have ha := xiApply_mem h0 hd hm
  have hb := xiApply_mem h0 hd hm'
  have h1 := xApply_addV d.2.1 hc (RuCode.mem_wList.mp ha) (RuCode.mem_wList.mp hb)
  rw [xApply_xiApply h0 hd hm, xApply_xiApply h0 hd hm'] at h1
  rw [← h1, xiApply_xApply h0 hd (addV_mem_wList hc ha hb)]

theorem nMap_mem (r : Lin8) {w : V3} : nMap d r w ∈ wList d.1.2.2.1 d.1.2.2.2 :=
  xiApply_mem h0 hd (maskApply_lt (adMat_lt r) _)

theorem xApply_nMap (r : Lin8) (w : V3) :
    xApply d.2.1 d.1.2.2.1 d.1.2.2.2 (nMap d r w) =
      maskApply (adMat r) (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w) :=
  xApply_xiApply h0 hd (maskApply_lt (adMat_lt r) _)

theorem nMap_addV (r : Lin8) {w w' : V3} (hw : w ∈ wList d.1.2.2.1 d.1.2.2.2)
    (hw' : w' ∈ wList d.1.2.2.1 d.1.2.2.2) :
    nMap d r (addV w w') = addV (nMap d r w) (nMap d r w') := by
  have hc := canon_d h0 hd
  rw [nMap, xApply_addV d.2.1 hc (RuCode.mem_wList.mp hw) (RuCode.mem_wList.mp hw'),
    maskApply_xor, xiApply_xor h0 hd (maskApply_lt (adMat_lt r) _)
      (maskApply_lt (adMat_lt r) _)]
  rfl

end Data


@[expose] def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toZ_xor (a b : Bool) : toZ (a ^^ b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> decide

@[expose] def toZM (A : M3) : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun i j => toZ (A i j)

theorem toZM_bmul (A B : M3) : toZM (bmul A B) = toZM A * toZM B := by
  ext i j
  simp only [toZM, bmul, Matrix.mul_apply, Fin.sum_univ_three, toZ_xor, toZ_and]

theorem toZM_one : toZM m3One = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def slZ (m : Nat) : Matrix (Fin 3) (Fin 3) (ZMod 2) := toZM (slToMat m)

theorem slToMat_xor (m m' : Nat) (i j : Fin 3) :
    slToMat (m ^^^ m') i j = (slToMat m i j ^^ slToMat m' i j) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact Nat.testBit_xor m m' _
    | (show ((m ^^^ m').testBit 6 ^^ (m ^^^ m').testBit 7) =
          ((m.testBit 6 ^^ m.testBit 7) ^^ (m'.testBit 6 ^^ m'.testBit 7))
       rw [Nat.testBit_xor, Nat.testBit_xor]
       cases m.testBit 6 <;> cases m.testBit 7 <;> cases m'.testBit 6 <;> cases m'.testBit 7 <;>
         rfl)

theorem slZ_xor (m m' : Nat) : slZ (m ^^^ m') = slZ m + slZ m' := by
  ext i j
  simp only [slZ, toZM, Matrix.add_apply, slToMat_xor, toZ_xor]

theorem trace_slZ (m : Nat) : Matrix.trace (slZ m) = 0 := by
  have h0 : slZ m 0 0 = toZ (m.testBit 6) := rfl
  have h1 : slZ m 1 1 = toZ (m.testBit 6) + toZ (m.testBit 7) := toZ_xor _ _
  have h2 : slZ m 2 2 = toZ (m.testBit 7) := rfl
  rw [Matrix.trace, Fin.sum_univ_three, Matrix.diag, Matrix.diag, Matrix.diag, h0, h1, h2]
  generalize toZ (m.testBit 6) = a
  generalize toZ (m.testBit 7) = b
  revert a b
  decide


theorem toZ_injective : Function.Injective toZ := by decide

theorem bits_matToSl : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    let n := bitVal b0 0 + bitVal b1 1 + bitVal b2 2 + bitVal b3 3 + bitVal b4 4 + bitVal b5 5 +
      bitVal b6 6 + bitVal b7 7
    n.testBit 0 = b0 ∧ n.testBit 1 = b1 ∧ n.testBit 2 = b2 ∧ n.testBit 3 = b3 ∧
      n.testBit 4 = b4 ∧ n.testBit 5 = b5 ∧ n.testBit 6 = b6 ∧ n.testBit 7 = b7 := by
  decide

theorem slToMat_matToSl (B : M3) (hB : B 1 1 = (B 0 0 ^^ B 2 2)) : slToMat (matToSl B) = B := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    bits_matToSl (B 0 1) (B 0 2) (B 1 0) (B 1 2) (B 2 0) (B 2 1) (B 0 0) (B 2 2)
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7
    | (show ((matToSl B).testBit 6 ^^ (matToSl B).testBit 7) = B 1 1
       unfold matToSl
       rw [h6, h7, hB])

theorem exists_slZ_eq {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : Matrix.trace A = 0) :
    ∃ m < 256, slZ m = A := by
  set B : M3 := fun i j => decide (A i j = 1) with hBdef
  have htoZ : ∀ i j, toZ (B i j) = A i j := by
    intro i j
    have : ∀ z : ZMod 2, toZ (decide (z = 1)) = z := by decide
    exact this _
  have hB : B 1 1 = (B 0 0 ^^ B 2 2) := by
    apply toZ_injective
    rw [toZ_xor, htoZ, htoZ, htoZ]
    have h := hA
    rw [Matrix.trace, Fin.sum_univ_three] at h
    simp only [Matrix.diag] at h
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination h - (A 0 0 + A 2 2) * h2
  refine ⟨matToSl B, matToSl_lt B, ?_⟩
  ext i j
  rw [slZ, toZM, slToMat_matToSl B hB, htoZ]


theorem linApply_zero (r : Lin8) : linApply r 0 = 0 := by
  obtain ⟨a, b, c⟩ := r
  revert a b c
  decide

theorem linApply_one (r : Lin8) : linApply r 1 = r.1 := by
  obtain ⟨a, b, c⟩ := r
  revert a b c
  decide

theorem linApply_two (r : Lin8) : linApply r 2 = r.2.1 := by
  obtain ⟨a, b, c⟩ := r
  revert a b c
  decide

theorem linApply_four (r : Lin8) : linApply r 4 = r.2.2 := by
  obtain ⟨a, b, c⟩ := r
  revert a b c
  decide

theorem fin8_bits : ∀ t : Fin 8, t = (if t.val.testBit 0 then 1 else 0) ^^^
    (if t.val.testBit 1 then 2 else 0) ^^^ (if t.val.testBit 2 then 4 else 0) := by
  decide

theorem eq_linApply {f : Fin 8 → Fin 8} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (t : Fin 8) :
    f t = linApply (f 1, f 2, f 4) t := by
  have hf0 : f 0 = 0 := by
    have h := hf 0 0
    rw [fin8_xor_self, fin8_xor_self] at h
    exact h
  have hite : ∀ (x : Bool) (c : Fin 8), f (if x = true then c else 0) =
      if x = true then f c else 0 := by
    intro x c
    cases x <;> simp [hf0]
  conv_lhs => rw [fin8_bits t]
  rw [hf, hf, hite, hite, hite]
  rfl

theorem linApply_ite (r : Lin8) (x : Bool) (c : Fin 8) :
    linApply r (if x = true then c else 0) = if x = true then linApply r c else 0 := by
  cases x <;> simp [linApply_zero]

theorem linApply_linComp (r s : Lin8) (t : Fin 8) :
    linApply (linComp r s) t = linApply r (linApply s t) := by
  have e : linApply s t = (if t.val.testBit 0 then s.1 else 0) ^^^
      (if t.val.testBit 1 then s.2.1 else 0) ^^^ (if t.val.testBit 2 then s.2.2 else 0) := rfl
  rw [e, linApply_xor, linApply_xor, linApply_ite, linApply_ite, linApply_ite]
  rfl

theorem mem_glList {r : Lin8} : r ∈ glList ↔ indep3 r.1 r.2.1 r.2.2 = true := by
  obtain ⟨a, b, c⟩ := r
  simp [glList, all8, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem indep3_of_injective {r : Lin8}
    (hr : ∀ s t, linApply r s = linApply r t → s = t) : indep3 r.1 r.2.1 r.2.2 = true := by
  have h3 : linApply r 3 = r.1 ^^^ r.2.1 := by
    rw [show (3 : Fin 8) = 1 ^^^ 2 from rfl, linApply_xor, linApply_one, linApply_two]
  have hne : ∀ s t : Fin 8, s ≠ t → linApply r s ≠ linApply r t := fun s t hst h => hst (hr s t h)
  have e10 := hne 1 0 (by decide)
  have e20 := hne 2 0 (by decide)
  have e21 := hne 2 1 (by decide)
  have e40 := hne 4 0 (by decide)
  have e41 := hne 4 1 (by decide)
  have e42 := hne 4 2 (by decide)
  have e43 := hne 4 3 (by decide)
  rw [linApply_one, linApply_zero] at e10
  rw [linApply_two, linApply_zero] at e20
  rw [linApply_two, linApply_one] at e21
  rw [linApply_four, linApply_zero] at e40
  rw [linApply_four, linApply_one] at e41
  rw [linApply_four, linApply_two] at e42
  rw [linApply_four, h3] at e43
  simp [indep3, e10, e20, e21, e40, e41, e42, e43]

end CFSG.ComponentClassification.GMS78.RuSimCode
