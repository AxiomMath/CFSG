module

public import CFSG.F3.ConjSpec
public import Certificates.Data.GrSLitL34FactsCF23ONOutK2Data
public import CFSG.Certificates.Kernel.ONOut.MatSound
import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

namespace CFSG.KS.ONOut

open CFSG.F3.Native CFSG.ComponentClassification.SolMax.ONOut CFSG.Sporadic.ON.Native

@[expose] def RowC (d : ℕ) (a : V) : Prop :=
  a.wf = true ∧ ∀ j, d ≤ j → a.p.testBit j = false ∧ a.m.testBit j = false

theorem shr_zero_iff {p d : ℕ} : p >>> d = 0 ↔ ∀ j, d ≤ j → p.testBit j = false := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos d)]
  constructor
  · intro h j hj
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hj))
  · intro h
    exact Nat.lt_pow_two_of_testBit p h

theorem rowC_iff {d : ℕ} {a : V} :
    (a.wf && a.p >>> d == 0 && a.m >>> d == 0) = true ↔ RowC d a := by
  simp only [Bool.and_eq_true, beq_iff_eq, shr_zero_iff, RowC]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun j hj => ⟨h2 j hj, h3 j hj⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun j hj => (h2 j hj).1⟩, fun j hj => (h2 j hj).2⟩

theorem canonM_of {d : ℕ} {X : Array V} (hs : X.size = d) (h : ∀ i < d, RowC d X[i]!) :
    canonM d X = true := by
  unfold canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨hs, fun i hi => ?_⟩
  have := rowC_iff.2 (h i (hs ▸ hi))
  rwa [getElem!_pos X i hi] at this

theorem rowC_zero (d : ℕ) : RowC d V.zero := ⟨V.wf_zero, fun j _ => by simp [V.zero]⟩

theorem rows_of_canonM {d : ℕ} {X : Array V} (h : canonM d X = true) : ∀ i : ℕ, RowC d X[i]! := by
  obtain ⟨hs, hX⟩ := canonM_spec h
  intro i
  by_cases hi : i < X.size
  · exact rowC_iff.1 (hX i hi)
  · rw [getElem!_neg X i hi]
    exact rowC_zero d

theorem rowC_add {d : ℕ} {a b : V} (ha : RowC d a) (hb : RowC d b) : RowC d (a.add b) := by
  refine ⟨V.wf_add ha.1 hb.1, fun j hj => ?_⟩
  obtain ⟨hp, hm⟩ := V.add_bits a b j
  rw [hp, hm, (ha.2 j hj).1, (ha.2 j hj).2, (hb.2 j hj).1, (hb.2 j hj).2]
  simp

theorem rowC_neg {d : ℕ} {a : V} (ha : RowC d a) : RowC d a.neg :=
  ⟨V.wf_neg ha.1, fun j hj => ⟨(ha.2 j hj).2, (ha.2 j hj).1⟩⟩

theorem rowC_sub {d : ℕ} {a b : V} (ha : RowC d a) (hb : RowC d b) : RowC d (a.sub b) :=
  rowC_add ha (rowC_neg hb)

theorem rowC_ofFn (d : ℕ) (f : ℕ → ℕ) : RowC d (V.ofFn d f) := by
  refine ⟨V.wf_ofFn d f, fun j hj => ?_⟩
  rw [ofFn_eq_fold]
  obtain ⟨h1, h2⟩ := fold_ofFnStep_bits f j d
  rw [h1, h2]
  simp [show ¬ j < d by omega]

theorem rowC_comb {d n : ℕ} {Y : Array V} {r : V} (hY : ∀ j : ℕ, RowC d Y[j]!) (hr : r.wf = true) :
    RowC d (comb n Y r) := by
  rw [comb_eq_fold]
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    exact rowC_zero d
  | succ n ih =>
    rw [Nat.fold_succ]
    unfold combStep
    split_ifs
    · exact rowC_add ih (hY n)
    · exact rowC_sub ih (hY n)
    · exact ih

theorem mul_size' (d : ℕ) (X Y : Array V) : (mul d X Y).size = X.size := by
  unfold mul
  simp

theorem canonM_mul {d : ℕ} {X Y : Array V} (hXs : X.size = d) (hX : RowsWF X)
    (hY : canonM d Y = true) : canonM d (mul d X Y) = true := by
  refine canonM_of (by rw [mul_size', hXs]) fun i hi => ?_
  rw [mul_getElem! (by rw [hXs]; exact hi)]
  exact rowC_comb (rows_of_canonM hY) (hX i)

theorem eqM_self {d : ℕ} {X : Array V} (hs : X.size = d) : eqM d X X = true := by
  unfold eqM
  simp [hs, V.beq, Nat.all_eq_finRange_all]

theorem eqM_of_toMat {d : ℕ} {X Y : Array V} (hX : canonM d X = true) (hY : canonM d Y = true)
    (h : toMat d X = toMat d Y) : eqM d X Y = true := by
  rw [eq_of_canonM hX hY h]
  exact eqM_self (canonM_spec hY).1

theorem okRows_of {X : Array V} (h : canonM 154 X = true) : okRows X = true := by
  obtain ⟨hs, -⟩ := canonM_spec h
  have hw := RowsWF.of_canonM h
  unfold okRows wfM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨hs, fun i hi => ?_⟩
  have := hw i
  rwa [getElem!_pos X i hi] at this

theorem addM_get {X Y : Array V} {i : ℕ} (hi : i < 154) : (addM X Y)[i]! = X[i]!.add Y[i]! := by
  unfold addM
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem toMat_addM' {X Y : Array V} (hX : RowsWF X) (hY : RowsWF Y) :
    toMat 154 (addM X Y) = toMat 154 X + toMat 154 Y := by
  ext i j
  rw [Matrix.add_apply, toMat_apply, toMat_apply, toMat_apply, addM_get i.isLt,
    V.val_add (hX i) (hY i)]

theorem canonM_addM' {X Y : Array V} (hX : ∀ i : ℕ, RowC 154 X[i]!) (hY : ∀ i : ℕ, RowC 154 Y[i]!) :
    canonM 154 (addM X Y) = true := by
  refine canonM_of (by unfold addM; simp) fun i hi => ?_
  rw [addM_get hi]
  exact rowC_add (hX i) (hY i)

theorem negM_get {X : Array V} {i : ℕ} (hi : i < X.size) : (negM X)[i]! = X[i]!.neg := by
  unfold negM
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos X i hi]

theorem toMat_negM' {X : Array V} (hs : X.size = 154) (hX : RowsWF X) :
    toMat 154 (negM X) = -toMat 154 X := by
  ext i j
  rw [Matrix.neg_apply, toMat_apply, toMat_apply, negM_get (by rw [hs]; exact i.isLt),
    V.val_neg _ _ (hX i)]

theorem canonM_negM' {X : Array V} (h : canonM 154 X = true) : canonM 154 (negM X) = true := by
  obtain ⟨hs, -⟩ := canonM_spec h
  refine canonM_of (by unfold negM; simp [hs]) fun i hi => ?_
  rw [negM_get (by rw [hs]; exact hi)]
  exact rowC_neg (rows_of_canonM h i)

theorem outer_get (v u : V) {i : ℕ} (hi : i < 154) : (outerRows v u)[i]! =
    if v.get i = 1 then u else if v.get i = 2 then u.neg else V.zero := by
  unfold outerRows
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem get_lt (v : V) (i : ℕ) : v.get i < 3 := by
  unfold V.get
  split_ifs <;> omega

theorem toMat_outerRows {v u : V} (hu : u.wf = true) (i j : Fin 154) :
    toMat 154 (outerRows v u) i j = v.val i * u.val j := by
  rw [toMat_apply, outer_get v u i.isLt]
  unfold V.val
  have := get_lt v i.val
  interval_cases h : v.get i.val
  · simp [V.zero, V.get]
  · simp
  · simp only [show (2 : ℕ) ≠ 1 by norm_num, ite_false, ite_true]
    rw [show ((u.neg).get j.val : ZMod 3) = u.neg.val j.val from rfl, V.val_neg u _ hu]
    unfold V.val
    push_cast
    ring_nf
    have : ∀ x : ZMod 3, -x = x * 2 := by decide
    exact this _

theorem canonM_outerRows (v : V) {u : V} (hu : RowC 154 u) : canonM 154 (outerRows v u) = true := by
  refine canonM_of (by unfold outerRows; simp) fun i hi => ?_
  rw [outer_get v u hi]
  split_ifs
  · exact hu
  · exact rowC_neg hu
  · exact rowC_zero 154

theorem rowC_transpose (X : Array V) : ∀ j : ℕ, RowC 154 (transpose 154 X)[j]! := by
  intro j
  unfold transpose
  by_cases hj : j < 154
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact rowC_ofFn _ _
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact rowC_zero 154

theorem val_mulVecRow (M : Array V) {x : V} (hx : x.wf = true) (k : Fin 154) :
    (mulVecRow M x).val k.val = ∑ j : Fin 154, toMat 154 M k j * x.val j.val := by
  unfold mulVecRow
  rw [V.val_comb 154 _ x (RowsWF.transpose 154 M) hx k.val,
    Finset.sum_range (fun j => x.val j * (transpose 154 M)[j]!.val k.val)]
  apply Finset.sum_congr rfl
  intro j _
  have e := congrFun (congrFun (toMat_transpose (d := 154) M) j) k
  rw [toMat_apply, Matrix.transpose_apply] at e
  rw [e, mul_comm]

theorem rowC_mulVecRow (M : Array V) {x : V} (hx : x.wf = true) : RowC 154 (mulVecRow M x) := by
  unfold mulVecRow
  exact rowC_comb (rowC_transpose M) hx

theorem beq_zero_of {a : V} (ha : RowC 154 a) (h : ∀ k < 154, a.val k = 0) : a.beq V.zero = true := by
  have hc : (a.wf && a.p >>> 154 == 0 && a.m >>> 154 == 0) = true := rowC_iff.2 ha
  have hz : (V.zero.wf && V.zero.p >>> 154 == 0 && V.zero.m >>> 154 == 0) = true := by decide
  rw [V.eq_of_canon hc hz fun j hj => by rw [h j hj, V.val_zero]]
  decide

theorem wordRows_spec (S Si : Array (Array V)) :
    ∀ w : List Int, (∀ l ∈ w, canonM 154 (letterRows S Si l) = true) →
      canonM 154 (wordRows S Si w) = true ∧
        toMat 154 (wordRows S Si w) = (w.map fun l => toMat 154 (letterRows S Si l)).prod
  | [], _ => ⟨canonM_idM 154, toMat_idM 154⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := wordRows_spec S Si w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hl := h l List.mem_cons_self
    have hs := (canonM_spec hl).1
    unfold wordRows
    refine ⟨canonM_mul hs (RowsWF.of_canonM hl) ih1, ?_⟩
    rw [toMat_mul hs (RowsWF.of_canonM hl) (RowsWF.of_canonM ih1), ih2, List.map_cons,
      List.prod_cons]

theorem digit27_eq {c : ℕ} (hc : c < 128) : digit27 (UInt8.ofNat c) = d27v c := by
  unfold digit27 d27v
  rw [UInt8.toNat_ofNat_of_lt' (show c < 256 by omega)]

theorem tritAt_eq {cs : List Char} (ha : ∀ c ∈ cs, c.toNat < 128) {k : ℕ} (hk : k / 3 < cs.length) :
    tritAt (String.ofList cs).toUTF8 k = tri cs k := by
  unfold tritAt tri
  rw [CFSG.KS.Text.get!_toUTF8 (K := cs.length) (by rw [List.take_length]; exact ha) hk hk,
    digit27_eq (ha _ (List.getElem_mem hk)), List.getD_eq_getElem _ _ hk]

end CFSG.KS.ONOut

end
