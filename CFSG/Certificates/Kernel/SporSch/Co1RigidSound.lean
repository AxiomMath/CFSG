module

public import Certificates.Data.Kernel.SporSch.Co1Rigid
public import CFSG.Certificates.Kernel.SporSch.Co1SplitSound
public import CFSG.Sporadic.Schreier.Co1RigidCheckInputs
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
import CFSG.Certificates.Kernel.SporSch.Co1MatSound
import CFSG.Certificates.Kernel.SporSch.Co1StabSound

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw CFSG.KS.Mathieu

@[expose] def coefBP (hq : Array Rows) (c p q : Nat) : Bool :=
  (c / 24 % 24 == p && ((hq.getD (c / 576 % 3) one).getD q 0).testBit (c % 24)) ^^
    (q == c % 24 && ((hq.getD (c / 576 % 3) one).getD (c / 24 % 24) 0).testBit p)

@[expose] def combBP (hq : Array Rows) (eqs : Array (List Nat)) (u p q : Nat) : Bool :=
  (eqs.getD u []).foldl (fun b c => b ^^ coefBP hq c p q) false

@[expose] def propCheckP (hq : Array Rows) (rank : Array Nat) (eqs : Array (List Nat)) : Bool :=
  (List.range 576).all fun u => rank.getD u 0 == 0 ||
    (combBP hq eqs u (u / 24) (u % 24) && (List.range 576).all fun v =>
      v == u || decide (rank.getD v 0 < rank.getD u 0) || !combBP hq eqs u (v / 24) (v % 24))

@[expose] def freeCheckP (rank : Array Nat) (free : Array (Nat × Nat)) : Bool :=
  (List.range 576).all fun u => rank.getD u 0 != 0 ||
    (List.range 8).any fun f => free.getD f (0, 0) == (u / 24, u % 24)

@[expose] def basisCheckP (dq hq : Array Rows) (free : Array (Nat × Nat)) : Bool :=
  (List.range 8).all fun f =>
    (List.range 3).all (fun i =>
      mul (dq.getD f one) (hq.getD i one) == mul (hq.getD i one) (dq.getD f one)) &&
    (List.range 8).all fun g =>
      ((dq.getD f one).getD (free.getD g (0, 0)).1 0).testBit (free.getD g (0, 0)).2 == (f == g)

@[expose] def rigP (Q QI : Rows) (c ci : Nat → Rows) (g2 g2i x y : Rows) (h k : Nat → Rows)
    (a1 : Rows) (free : Array (Nat × Nat)) : Bool :=
  mul Q QI == one && (List.range 2).all (fun i => mul (c i) (ci i) == one) &&
    mul g2 g2i == one &&
    (List.range 3).all (fun i => mul x (h i) == mul (k i) x) &&
    mul x x == one && pow (mul x y) 28 == one && a1 == y && a1 != one &&
    wf a1 && wf one && free.size == 8 &&
    (List.range 8).all fun f => decide ((free.getD f (0, 0)).1 < 24) &&
      decide ((free.getD f (0, 0)).2 < 24)

@[expose] def candRowsP (ds : Array Rows) (ε : Fin 8 → Bool) : Rows :=
  (List.finRange 8).foldl (fun R f => if ε f then add R (ds.getD f.val one) else R) zeroRows

@[expose] def candOKP (x y : Rows) (ds : Array Rows) (ε : Fin 8 → Bool) : Bool :=
  wf (mul (mul x (candRowsP ds ε)) (mul x (candRowsP ds ε))) &&
    wf (pow (mul (mul x (candRowsP ds ε)) y) 28) &&
    (mul (mul x (candRowsP ds ε)) (mul x (candRowsP ds ε)) != one ||
      pow (mul (mul x (candRowsP ds ε)) y) 28 != one || candRowsP ds ε == one)

namespace RigL

open CFSG.KC.Enum

private theorem bitShift (s x i k : Nat) :
    Nat.lor s (Nat.shiftLeft (Nat.land (Nat.shiftRight x i) (nat_lit 1)) k) =
      if x.testBit i = true then Nat.lor s (Nat.shiftLeft 1 k) else s := by
  have e : Nat.land (Nat.shiftRight x i) 1 = if x.testBit i = true then 1 else 0 := by
    change (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]
  rw [e]
  split
  · rfl
  · change s ||| 0 <<< k = s
    rw [Nat.zero_shiftLeft, Nat.or_zero]

private theorem toArray_getD {α : Type} (l : List α) (i : Nat) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

private theorem ofFn_getD {n : Nat} (F : Nat → Rows) {i : Nat} (hi : i < n) (d : Rows) :
    (Array.ofFn (n := n) fun j => F j.val).getD i d = F i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [hi]

private theorem foldN8_eq (f : Nat → Nat → Nat) (s : Nat) : foldN 8 f s = (List.range 8).foldr f s := by
  have h : foldN 8 f s = foldBlk 0 f 8 s := rfl
  rw [h, MatL.foldBlk_eq]
  simp only [Nat.zero_add]

private theorem rankOK_spec {RT : Nat → Nat} {R : List Nat} (hr : rankOK RT R = true) :
    ∀ u < 576, RT u = R.getD u 0 := by
  intro u hu
  unfold rankOK at hr
  rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff] at hr
  rw [Nat.eq_of_beq_eq_true (hr.2 u hu), StabL.nget_eq]

private theorem lenP_eq : ∀ l : List (Nat × Nat), lenP l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenP_eq l)

private theorem coef_eq (HQ : Nat → Nat) (c p q : Nat) (hq : q < 24) :
    coefK2 HQ c p q = coefBP (Array.ofFn (n := 3) fun i => unpack 24 24 (HQ i.val)) c p q := by
  have hi : c / 576 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hk : c / 24 % 24 < 24 := Nat.mod_lt _ (by decide)
  unfold coefBP
  rw [ofFn_getD (fun i => unpack 24 24 (HQ i)) hi, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?,
    MatL.unpack_getD _ _ hq, MatL.unpack_getD _ _ hk]
  unfold coefK2
  simp only [MatL.strictB_eq, StabL.xorRec, MatL.bAnd_eq, StabL.bitK_eq, MatL.rowK_eq]
  rfl

private theorem comb_eq (HQ : Nat → Nat) (cs : List Nat) (p q : Nat) (hq : q < 24) :
    combK2 HQ cs p q = cs.foldl (fun b c =>
      b ^^ coefBP (Array.ofFn (n := 3) fun i => unpack 24 24 (HQ i.val)) c p q) false := by
  rw [StabL.foldl_xor, Bool.false_xor]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change Bool.rec (motive := fun _ => Bool) (combK2 HQ cs p q) (bIf(combK2 HQ cs p q, false, true))
      (coefK2 HQ c p q) = _
    rw [StabL.xorRec, List.foldr_cons, ← ih, coef_eq HQ c p q hq]

private theorem pos3K_spec {w : List Nat} (h : pos3K w = true) : ∀ j ∈ w, 1 ≤ j ∧ j ≤ 3 := by
  induction w with
  | nil => simp
  | cons j w ih =>
    have e : pos3K (j :: w) = (Nat.ble 1 j && (Nat.ble j 3 && pos3K w)) := by
      rw [← MatL.bAnd_eq, ← MatL.bAnd_eq]
      rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 j' hj'

private theorem wordPosK_eq (C : Nat → Nat) (w : List Nat) :
    wordPosK C w = w.foldl (fun acc j => mulK acc (C (Nat.sub j 1))) idM := by
  unfold wordPosK
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons j w ih => exact (MatL.strictN_eq _ _).trans (ih _)

private theorem rowV_xor (a b i : Nat) : MatL.rowV (a ^^^ b) i = MatL.rowV a i ^^^ MatL.rowV b i := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [MatL.rowV, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  by_cases ht : t < 24 <;> simp [ht]

private theorem unpack_xor (a b : Nat) :
    unpack 24 24 (a ^^^ b) = add (unpack 24 24 a) (unpack 24 24 b) := by
  apply Array.ext
  · simp [add, MatL.unpack_size]
  · intro i h1 h2
    have hi : i < 24 := by rw [MatL.unpack_size] at h1; exact h1
    rw [MatL.unpack_getElem]
    simp only [add, Array.getElem_ofFn]
    rw [MatL.unpack_getD _ _ hi, MatL.unpack_getD _ _ hi, rowV_xor]

private theorem unpack_zero : unpack 24 24 0 = zeroRows := by
  apply Array.ext
  · simp [zeroRows, MatL.unpack_size]
  · intro i h1 h2
    rw [MatL.unpack_getElem]
    simp [zeroRows, MatL.rowV]

private theorem ofBits_lt (f : Nat → Bool) : ofBits 8 f < 2 ^ 8 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [ActL.testBit_ofBits]
  have : ¬ i < 8 := by omega
  simp [this]

private theorem ne_one_of {Z : Nat} (hZ : Nat.shiftRight Z 576 = 0) (h : Z ≠ idM) :
    (unpack 24 24 Z != one ()) = true := by
  have hb : Nat.beq Z idM = false := Bool.eq_false_iff.2 fun hh => h (Nat.eq_of_beq_eq_true hh)
  refine unpack_ne_one (by rw [hZ]; rfl) ?_
  rw [hb]

end RigL

open RigL in
theorem transOK_sound {PZ PQ : Nat} {fv : List (List Nat)} (h : transOK PZ PQ fv = true) :
    qMatP (unpack 24 24 PZ) fv = unpack 24 24 PQ := by
  have hcol : ∀ k < 24, colK PZ fv k < 2 ^ 24 := by
    intro k _
    unfold colK
    rw [MatL.strictN_eq, MatL.nIf_eq]
    split
    · exact qK_lt _ _ _
    · exact actK_lt _ _
  have hcolEq : ∀ t < 24, (qColsP (unpack 24 24 PZ) fv)[t]?.getD 0 = colK PZ fv t := by
    intro t ht
    unfold colK
    rw [MatL.strictN_eq, MatL.nIf_eq, qK_unpack]
    have e1 : Nat.shiftRight t 1 = t / 2 := MatS.shiftRight_one_div t
    have e2 : Nat.land t 1 = t % 2 := Nat.and_one_is_mod t
    rw [e1, e2]
    simp only [qColsP, Array.getElem?_ofFn, ht, ↓reduceDIte, Option.getD_some, Nat.beq_eq,
      ActL.act_unpack]
  unfold transOK at h
  rw [MatL.strictB_eq, MatL.allN_iff] at h
  have hrow : ∀ k < 24, rowK (CFSG.KC.Enum.foldN 24 (fun k s => Nat.lor s
      (Nat.shiftLeft (colK PZ fv k) (Nat.mul 24 k))) 0) k = colK PZ fv k := fun k hk => by
    rw [MatL.rowK_eq, MatL.foldN_eq]
    exact MatL.pack_field (colK PZ fv) hcol k hk
  unfold qMatP
  apply Array.ext
  · simp [transposeRows, MatL.unpack_size]
  · intro i h1 h2
    have hi : i < 24 := by rw [MatL.unpack_size] at h2; exact h2
    rw [MatL.unpack_getElem, ← MatL.rowK_eq, Nat.eq_of_beq_eq_true (h i hi), MatL.foldN_eq]
    simp only [transposeRows, Array.getElem_ofFn, bitShift]
    apply Nat.eq_of_testBit_eq
    intro t
    rw [ActL.testBit_ofBits, ActL.testBit_foldr_or]
    by_cases ht : t < 24
    · simp only [ht, decide_true, List.mem_range, Bool.true_and]
      rw [hrow t ht, hcolEq t ht]
    · simp [ht]

open RigL in
theorem locK_sound {A C : Nat → Nat} {p : List Nat × List Nat} (h : pos3K (pr2 p) = true)
    (is : List Rows) :
    mul (eRowsP (fun i => unpack 24 24 (A i)) (expVec p.1))
      (word [unpack 24 24 (C 0), unpack 24 24 (C 1), unpack 24 24 (C 2)] is (p.2.map Int.ofNat)) =
      unpack 24 24 (locK A C p) := by
  obtain ⟨p1, p2⟩ := p
  change pos3K p2 = true at h
  change mul (eRowsP (fun i => unpack 24 24 (A i)) (expVec p1))
      (word [unpack 24 24 (C 0), unpack 24 24 (C 1), unpack 24 24 (C 2)] is (p2.map Int.ofNat)) =
    unpack 24 24 (mulK (eProdK A (enc3 p1)) (wordPosK C p2))
  rw [MatL.unpack_mulK, unpack_eProdK]
  refine congrArg (mul _) ?_
  have hpos := pos3K_spec h
  unfold word
  rw [List.foldl_map, ← MatL.unpack_idM, wordPosK_eq]
  clear h
  generalize idM = a
  induction p2 generalizing a with
  | nil => rfl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hj : letter [unpack 24 24 (C 0), unpack 24 24 (C 1), unpack 24 24 (C 2)] is
        (Int.ofNat j) = unpack 24 24 (C (Nat.sub j 1)) := by
      obtain ⟨h1, h3⟩ := hpos j (List.mem_cons_self ..)
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      all_goals simp [letter]
    rw [hj, ← MatL.unpack_mulK]
    exact ih (fun j' hj' => hpos j' (List.mem_cons_of_mem j hj')) _

open RigL in
theorem propK_sound {HQ RT : Nat → Nat} {R : List Nat} {EQ : List (List Nat)}
    (hr : rankOK RT R = true) (hs : ∀ s < 9, propK HQ RT EQ (64 * s) 64 = true) :
    propCheckP (Array.ofFn (n := 3) fun i => unpack 24 24 (HQ i.val)) R.toArray EQ.toArray =
      true := by
  have hRT := rankOK_spec hr
  unfold propCheckP
  rw [List.all_eq_true]
  intro u hum
  have hu : u < 576 := List.mem_range.1 hum
  have hs0 := MatL.allN_iff.1 (hs (u / 64) (by omega)) (u % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (64 * (u / 64)) (u % 64) = u := Nat.div_add_mod u 64
  simp only [MatL.strictB_eq, e] at hs0
  simp only [StabL.impRec, StabL.orRec, MatL.bAnd_eq, MatL.allN_iff, StabL.bltD, StabL.beqD,
    Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, beq_iff_eq, StabL.ngetL_eq, hu, not_true_eq_false, false_or] at hs0
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true', toArray_getD]
  have hc : ∀ p q, q < 24 → combBP (Array.ofFn (n := 3) fun i => unpack 24 24 (HQ i.val))
      EQ.toArray u p q = combK2 HQ (EQ.getD u []) p q := fun p q hq => by
    unfold combBP
    rw [toArray_getD, comb_eq HQ _ p q hq]
  rcases hs0 with h0 | ⟨h1, h2⟩
  · left
    rw [← hRT u hu]
    exact h0
  · right
    refine ⟨(hc _ _ (Nat.mod_lt _ (by decide))).trans h1, fun v hv => ?_⟩
    rcases h2 v hv with h3 | h3 | h3
    · exact Or.inl (Or.inl h3)
    · refine Or.inl (Or.inr ?_)
      rw [← hRT v hv, ← hRT u hu]
      exact h3
    · exact Or.inr ((hc _ _ (Nat.mod_lt _ (by decide))).trans h3)

open RigL in
theorem freeK_sound {RT : Nat → Nat} {R : List Nat} {FF : List (Nat × Nat)}
    (hr : rankOK RT R = true) (h : freeK RT FF = true) :
    freeCheckP R.toArray FF.toArray = true := by
  have hRT := rankOK_spec hr
  unfold freeCheckP
  rw [List.all_eq_true]
  intro u hum
  have hu : u < 576 := List.mem_range.1 hum
  have hf := MatL.allN_iff.1 h u hu
  simp only [StabL.impRec, Bool.or_false, MatL.bAnd_eq, MatL.allN_eq, StabL.beqD,
    StabL.pairFst_eq, StabL.pairSnd_eq, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    List.all_eq_false, List.mem_range, Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hf
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, List.mem_range, beq_iff_eq,
    toArray_getD]
  by_cases h0 : R.getD u 0 = 0
  · right
    rcases hf with hf | ⟨f, hf8, h1, h2⟩
    · exact absurd (by rw [hRT u hu]; exact h0) hf
    · exact ⟨f, hf8, Prod.ext h1 h2⟩
  · exact Or.inl h0

open RigL in
theorem basisK_sound {D HQ : Nat → Nat} {FF : List (Nat × Nat)} (h : basisK D HQ FF = true) :
    basisCheckP (Array.ofFn (n := 8) fun f => unpack 24 24 (D f.val))
      (Array.ofFn (n := 3) fun i => unpack 24 24 (HQ i.val)) FF.toArray = true := by
  unfold basisCheckP
  rw [List.all_eq_true]
  intro f hfm
  have hf8 : f < 8 := List.mem_range.1 hfm
  have hf := MatL.allN_iff.1 h f hf8
  rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff, MatL.allN_iff] at hf
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true,
    ofFn_getD (fun f => unpack 24 24 (D f)) hf8]
  refine ⟨fun i him => ?_, fun g hgm => ?_⟩
  · have hi : i < 3 := List.mem_range.1 him
    rw [ofFn_getD (fun i => unpack 24 24 (HQ i)) hi, ← MatL.unpack_mulK, ← MatL.unpack_mulK,
      Nat.eq_of_beq_eq_true (hf.1 i hi)]
    exact beq_self_eq_true _
  · have hg : g < 8 := List.mem_range.1 hgm
    have hfg := hf.2 g hg
    simp only [MatL.bAnd_eq, Bool.and_eq_true, StabL.pairFst_eq, StabL.pairSnd_eq,
      StabL.bitK_eq, MatL.rowK_eq, Nat.blt_eq] at hfg
    obtain ⟨h1, -, h3⟩ := hfg
    rw [toArray_getD FF, Array.getD_eq_getD_getElem?, MatL.unpack_getD _ _ h1]
    have hbq : (f == g) = Nat.beq f g := rfl
    rw [hbq]
    revert h3
    generalize (MatL.rowV (D f) (FF.getD g (0, 0)).1).testBit (FF.getD g (0, 0)).2 = b
    cases b <;> cases Nat.beq f g <;> decide

open RigL in
theorem rigK_sound {Q QI G2 G2I X Y A1 : Nat} {C CI H K : Nat → Nat} {FF : List (Nat × Nat)}
    (h : rigK Q QI C CI G2 G2I X Y H K A1 FF = true) :
    rigP (unpack 24 24 Q) (unpack 24 24 QI) (fun i => unpack 24 24 (C i))
      (fun i => unpack 24 24 (CI i)) (unpack 24 24 G2) (unpack 24 24 G2I) (unpack 24 24 X)
      (unpack 24 24 Y) (fun i => unpack 24 24 (H i)) (fun i => unpack 24 24 (K i))
      (unpack 24 24 A1) FF.toArray = true := by
  unfold rigK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hQ, hC, hG, hX, hXX, hP, hA, hS, hN, hL, hF⟩ := h
  have hone : ∀ {U V : Nat}, Nat.beq (mulK U V) idM = true →
      mul (unpack 24 24 U) (unpack 24 24 V) = one () := fun e => by
    rw [← MatL.unpack_mulK, Nat.eq_of_beq_eq_true e, MatL.unpack_idM]
  unfold rigP
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc]
  refine ⟨hone hQ, fun i hi => hone (MatL.allN_iff.1 hC i hi), hone hG, fun i hi => ?_, hone hXX,
    ?_, by rw [Nat.eq_of_beq_eq_true hA], unpack_ne_one hS hN, StabL.wf_unpack' A1,
    by rw [← MatL.unpack_idM]; exact StabL.wf_unpack' _, ?_, fun f hf => ?_⟩
  · rw [← MatL.unpack_mulK, ← MatL.unpack_mulK, Nat.eq_of_beq_eq_true (MatL.allN_iff.1 hX i hi)]
  · rw [← MatL.unpack_mulK, ← unpack_powK, Nat.eq_of_beq_eq_true hP, MatL.unpack_idM]
  · rw [List.size_toArray, ← lenP_eq, Nat.eq_of_beq_eq_true hL]
  · have h2 := MatL.allN_iff.1 hF f hf
    simp only [Bool.and_eq_true, Nat.blt_eq, StabL.pairFst_eq, StabL.pairSnd_eq] at h2
    rw [toArray_getD FF]
    exact h2

open RigL in
theorem candK_sound {X Y DS : Nat → Nat} (hs : ∀ s < 4, candK X Y DS (64 * s) 64 = true)
    (ε : Fin 8 → Bool) :
    candOKP (unpack 24 24 (X 0)) (unpack 24 24 (Y 0))
      (Array.ofFn (n := 8) fun f => unpack 24 24 (DS f.val)) ε = true := by
  let g : Nat → Bool := fun f => if hf : f < 8 then ε ⟨f, hf⟩ else false
  have hm : ofBits 8 g < 256 := ofBits_lt g
  have hbit : ∀ f < 8, (ofBits 8 g).testBit f = g f := fun f hf => by
    rw [ActL.testBit_ofBits]
    simp [hf]
  have hfold : ∀ (l : List Nat) (acc : Nat), (∀ f ∈ l, f < 8) →
      unpack 24 24 (l.foldl (fun acc f => if (ofBits 8 g).testBit f = true then acc ^^^ DS f
        else acc) acc) =
      l.foldl (fun R f => if g f = true then add R (unpack 24 24 (DS f)) else R)
        (unpack 24 24 acc) := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons f l ih =>
      intro acc hl
      rw [List.foldl_cons, List.foldl_cons, hbit f (hl f (List.mem_cons_self ..))]
      have hl' : ∀ f ∈ l, f < 8 := fun f' hf' => hl f' (List.mem_cons_of_mem _ hf')
      by_cases hg : g f = true
      · rw [ite_eq_left hg, ite_eq_left hg, ih _ hl', unpack_xor]
      · rw [ite_eq_right hg, ite_eq_right hg, ih _ hl']
  have hT : unpack 24 24 (candT DS (ofBits 8 g)) =
      candRowsP (Array.ofFn (n := 8) fun f => unpack 24 24 (DS f.val)) ε := by
    unfold candT
    rw [foldN8_eq]
    simp only [MatL.nIf_eq, MatL.hasBit_eq]
    change unpack 24 24 ((List.range 8).foldr (fun f s =>
      if (ofBits 8 g).testBit f = true then s ^^^ DS f else s) 0) = _
    rw [MatL.foldr_xor_eq_foldl, hfold _ 0 (fun f hf => List.mem_range.1 hf), unpack_zero]
    unfold candRowsP
    have e : (List.finRange 8).map Fin.val = List.range 8 := List.ext_getElem (by simp) (by simp)
    rw [← e, List.foldl_map]
    apply List.foldl_ext
    intro R f _
    simp [g, ofFn_getD (fun f => unpack 24 24 (DS f)) f.2]
  have hb := MatL.allN_iff.1 (hs (ofBits 8 g / 64) (by omega)) (ofBits 8 g % 64)
    (Nat.mod_lt _ (by decide))
  have e : Nat.add (64 * (ofBits 8 g / 64)) (ofBits 8 g % 64) = ofBits 8 g :=
    Nat.div_add_mod (ofBits 8 g) 64
  simp only [MatL.strictB_eq, e, StabL.impRec, Bool.or_eq_true, Bool.not_eq_true'] at hb
  unfold candOKP
  rw [← hT]
  generalize candT DS (ofBits 8 g) = T at hb ⊢
  rw [← MatL.unpack_mulK, ← MatL.unpack_mulK, ← MatL.unpack_mulK, ← unpack_powK,
    StabL.wf_unpack', StabL.wf_unpack', Bool.true_and, Bool.true_and]
  simp only [Bool.or_eq_true]
  rcases hb with h1 | h1 | h1
  · refine Or.inl (Or.inl (ne_one_of (mulK_shift _ _) fun e => ?_))
    rw [e, Nat.beq_refl] at h1
    exact Bool.noConfusion h1
  · refine Or.inl (Or.inr (ne_one_of ?_ fun e => ?_))
    · change Nat.shiftRight (CFSG.KC.Enum.strictN (powK (mulK (mulK (X 0) T) (Y 0)) 27)
        (fun Z => mulK Z (mulK (mulK (X 0) T) (Y 0)))) 576 = 0
      rw [MatL.strictN_eq]
      exact mulK_shift _ _
    · rw [e, Nat.beq_refl] at h1
      exact Bool.noConfusion h1
  · refine Or.inr ?_
    rw [Nat.eq_of_beq_eq_true h1, MatL.unpack_idM]
    exact beq_self_eq_true _

end CFSG.KS.SporSch.M24

end
