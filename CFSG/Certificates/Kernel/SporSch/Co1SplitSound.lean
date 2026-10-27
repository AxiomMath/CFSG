module

public import Certificates.Data.Kernel.SporSch.Co1Split
public import CFSG.Certificates.Kernel.SporSch.Co1ElemSound
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
import CFSG.Certificates.Kernel.SporSch.Co1MatSound
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw CFSG.KS.Mathieu

@[expose] def zqTP (Z : Rows) (fv : List (List Nat)) : Array Nat :=
  Array.ofFn (n := 36) fun i => zPowP Z (i.val % 3) (qNatP Z fv (i.val / 3))

@[expose] def zqP (Z : Rows) (fv : List (List Nat)) (e k : Nat) : Nat := (zqTP Z fv).getD (3 * k + e) 0

@[expose] def msSearchP (Z : Rows) (fv : List (List Nat)) (X : Rows) (j : Nat) : Nat × Nat × Nat :=
  let v := act X (zqP Z fv 0 j)
  let w := act X (zqP Z fv 1 j)
  match (List.range 36).find? (fun i => (zqTP Z fv).getD i 0 == v) with
  | some i => (i / 3, i % 3, ((List.range 3).find? fun f => zqP Z fv f (i / 3) == w).getD 0)
  | none => (0, 0, 0)

@[expose] def msSgnP (Z : Rows) (fv : List (List Nat)) (X : Rows) (j : Nat) : Nat :=
  ((msSearchP Z fv X j).2.2 + 3 - (msSearchP Z fv X j).2.1) % 3

@[expose] def msOKP (Z : Rows) (fv : List (List Nat)) (X : Rows) : Bool := (List.range 12).all fun j =>
  let d := msSearchP Z fv X j
  let s := (d.2.2 + 3 - d.2.1) % 3
  d.1 < 12 && d.2.1 < 3 && s != 0 &&
    (List.range 3).all fun e => act X (zqP Z fv e j) == zqP Z fv ((d.2.1 + s * e) % 3) d.1

@[expose] def splitCheckP (aR bR : Rows) (flag : Bool) (g a : Nat → Rows) (Z : Rows)
    (fv : List (List Nat)) (LR : List (List Nat)) : Bool :=
  mul aR (inv aR) == one && mul bR (inv bR) == one && flag &&
    (List.range 3).all (fun i => g i == (LR.getD i []).toArray) &&
    ((List.range 6).map a ++ (List.range 3).map g).all
      (fun X => let Y := inv X; mul X Y == one && msOKP Z fv X && msOKP Z fv Y)

@[expose] def splitDataCheckP (g a : Nat → Rows) (Z : Rows) (fv : List (List Nat))
    (LP LS : List (List Nat)) : Bool :=
  (List.range 6).all (fun i => (List.range 12).all fun j =>
      (msSearchP Z fv (a i) j).1 == j && msSgnP Z fv (a i) j == 1) &&
    (List.range 2).all (fun i => (List.range 12).all fun j =>
      (msSearchP Z fv (g i) j).1 == (LP.getD i []).getD j 0 &&
        msSgnP Z fv (g i) j == (LS.getD i []).getD j 0) &&
    (List.range 12).all fun j => (msSearchP Z fv (g 2) j).1 == j && msSgnP Z fv (g 2) j == 2

@[expose] def splitConjCheckP (g a : Nat → Rows) (CE : List (List (List Nat)))
    (CR : List (List Nat)) : Bool :=
  (List.range 3).all (fun i => (List.range 6).all fun j =>
      mul (mul (g i) (a j)) (inv (g i)) == eRowsP a (expVec ((CE.getD i []).getD j []))) &&
    (List.range 2).all (fun i =>
      mul (mul (mul (g 2) (g i)) (inv (g 2))) (inv (g i)) == eRowsP a (expVec (CR.getD i []))) &&
    mul (g 2) (g 2) == one && g 2 != one

@[expose] def zqCheckP (Z : Rows) (fv : List (List Nat)) : Bool :=
  (List.range 12).all fun j => (List.range 3).all fun e => decide (zqP Z fv e j < 2 ^ 24) &&
    (List.range 12).all fun k => (List.range 3).all fun f =>
      (zqP Z fv e j == zqP Z fv f k) == (j == k && e == f)

namespace SplitL

open CFSG.KC.Enum

private theorem nget_eq : ∀ (l : List Nat) (i : Nat), nget l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nget_eq l i

private theorem ngetL_eq : ∀ (l : List (List Nat)) (i : Nat), ngetL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => ngetL_eq l i

private theorem beqD (x y : Nat) : Nat.beq x y = (x == y) := rfl

private theorem bNot_eq (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = !c := by
  cases c <;> rfl

private theorem foldN12_eq (f : Nat → Nat → Nat) (s : Nat) :
    foldN 12 f s = (List.range 12).foldr f s := by
  have h : foldN 12 f s = foldBlk 0 f 12 s := rfl
  rw [h, MatL.foldBlk_eq]
  simp only [Nat.zero_add]

private theorem finRange12_foldl (F : Nat → Nat → Nat) (a : Nat) :
    (List.finRange 12).foldl (fun acc k => F acc k.val) a = (List.range 12).foldl F a := by
  have e : (List.finRange 12).map Fin.val = List.range 12 :=
    List.ext_getElem (by simp) (by simp)
  rw [← e, List.foldl_map]

private theorem f4LoK_eq (cs : List Nat) : f4LoK cs = f4Lo cs := by
  have key : (List.range 12).foldr
      (fun k s => if (cs.getD k 0 % 2 == 1) = true then s ^^^ (1 <<< k) else s) 0 =
      (List.range 12).foldl
        (fun acc k => if (cs.getD k 0 % 2 == 1) = true then acc ^^^ (1 <<< k) else acc) 0 :=
    MatL.foldr_xor_eq_foldl (fun k => cs.getD k 0 % 2 == 1) (fun k => 1 <<< k) _
  unfold f4LoK f4Lo
  rw [foldN12_eq]
  simp only [MatL.nIf_eq, nget_eq]
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · rw [finRange12_foldl (fun acc k => if cs.getD k 0 % 2 = 1 then acc ^^^ (1 <<< k) else acc)]
    apply List.foldl_ext
    intro a k _
    simp

private theorem f4HiK_eq (PZ : Nat) (cs : List Nat) : f4HiK PZ cs = f4HiP (unpack 24 24 PZ) cs := by
  have key : (List.range 12).foldr
      (fun k s => if (cs.getD k 0 / 2 % 2 == 1) = true then s ^^^ act (unpack 24 24 PZ) (1 <<< k)
        else s) 0 =
      (List.range 12).foldl
        (fun acc k => if (cs.getD k 0 / 2 % 2 == 1) = true then
          acc ^^^ act (unpack 24 24 PZ) (1 <<< k) else acc) 0 :=
    MatL.foldr_xor_eq_foldl (fun k => cs.getD k 0 / 2 % 2 == 1)
      (fun k => act (unpack 24 24 PZ) (1 <<< k)) _
  unfold f4HiK f4HiP
  rw [foldN12_eq]
  simp only [MatL.nIf_eq, nget_eq, ← ActL.act_unpack]
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · rw [finRange12_foldl (fun acc k => if cs.getD k 0 / 2 % 2 = 1 then
      acc ^^^ act (unpack 24 24 PZ) (1 <<< k) else acc)]
    apply List.foldl_ext
    intro a k _
    simp

private theorem qK_eq (PZ : Nat) (fv : List (List Nat)) (j : Nat) :
    qK PZ fv j = qNatP (unpack 24 24 PZ) fv j := by
  unfold qK qNatP
  rw [ngetL_eq, f4LoK_eq, f4HiK_eq]
  rfl

private theorem zPowK_eq (PZ v : Nat) : ∀ e, zPowK PZ e v = zPowP (unpack 24 24 PZ) e v
  | 0 => rfl
  | e + 1 => by
    change strictN (zPowK PZ e v) (fun u => actK PZ u) = _
    rw [MatL.strictN_eq, zPowK_eq PZ v e, ← ActL.act_unpack]
    unfold zPowP
    rw [Function.iterate_succ_apply']

private theorem zq_bind {PZ : Nat} {fv : List (List Nat)} {ZQ : Nat → Nat}
    (hz : zqOK PZ fv ZQ = true) : ∀ i < 36, ZQ i = (zqTP (unpack 24 24 PZ) fv).getD i 0 := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true (MatL.allN_iff.1 hz i hi)]
  unfold zqIK
  rw [MatL.nIf_eq, ite_eq_left (Nat.blt_eq.mpr hi)]
  change zPowK PZ (i % 3) (qK PZ fv (i / 3)) = _
  rw [zPowK_eq, qK_eq]
  simp [zqTP, hi]

private theorem findV_eq {ZQ T : Nat → Nat} (hZ : ∀ i < 36, ZQ i = T i) (v : Nat) :
    ∀ n i0, i0 + n ≤ 36 →
      findV ZQ v n i0 = ((List.range' i0 n).find? fun i => T i == v).getD 36 := by
  intro n
  induction n with
  | zero => intro i0 _; rfl
  | succ n ih =>
    intro i0 h
    have e : findV ZQ v (n + 1) i0 =
        Bool.rec (motive := fun _ => Nat) (findV ZQ v n (i0 + 1)) i0 (Nat.beq (ZQ i0) v) := rfl
    rw [e, MatL.nIf_eq, hZ i0 (by omega), ih (i0 + 1) (by omega), List.range'_succ]
    simp only [List.find?_cons, beqD]
    by_cases hT : (T i0 == v) = true
    · rw [ite_eq_left hT, hT]
      rfl
    · rw [ite_eq_right hT, Bool.eq_false_iff.2 hT]

private theorem findF_eq {PZ : Nat} {fv : List (List Nat)} {ZQ : Nat → Nat}
    (hZ : ∀ i < 36, ZQ i = (zqTP (unpack 24 24 PZ) fv).getD i 0) {k : Nat} (hk : k < 12)
    (w : Nat) :
    findF ZQ k w = ((List.range 3).find? fun f => zqP (unpack 24 24 PZ) fv f k == w).getD 0 := by
  have e0 : zqL ZQ 0 k = zqP (unpack 24 24 PZ) fv 0 k := hZ (3 * k + 0) (by omega)
  have e1 : zqL ZQ 1 k = zqP (unpack 24 24 PZ) fv 1 k := hZ (3 * k + 1) (by omega)
  have e2 : zqL ZQ 2 k = zqP (unpack 24 24 PZ) fv 2 k := hZ (3 * k + 2) (by omega)
  have r3 : List.range 3 = [0, 1, 2] := rfl
  unfold findF
  rw [r3]
  simp only [MatL.nIf_eq, e0, e1, e2, beqD, List.find?_cons, List.find?_nil]
  cases (zqP (unpack 24 24 PZ) fv 0 k == w) <;> cases (zqP (unpack 24 24 PZ) fv 1 k == w) <;>
    cases (zqP (unpack 24 24 PZ) fv 2 k == w) <;> rfl

private theorem find3_lt (p : Nat → Bool) : ((List.range 3).find? p).getD 0 < 3 := by
  cases h : (List.range 3).find? p with
  | none => decide
  | some f => exact List.mem_range.1 (List.mem_of_find?_eq_some h)

private theorem msSearchP_some {Z : Rows} {fv : List (List Nat)} {Y : Rows} {j i : Nat}
    (h : (List.range 36).find? (fun i => (zqTP Z fv).getD i 0 == act Y (zqP Z fv 0 j)) = some i) :
    msSearchP Z fv Y j = (i / 3, i % 3,
      ((List.range 3).find? fun f => zqP Z fv f (i / 3) == act Y (zqP Z fv 1 j)).getD 0) := by
  unfold msSearchP
  simp only [h]

private theorem msSearchP_none {Z : Rows} {fv : List (List Nat)} {Y : Rows} {j : Nat}
    (h : (List.range 36).find? (fun i => (zqTP Z fv).getD i 0 == act Y (zqP Z fv 0 j)) = none) :
    msSearchP Z fv Y j = (0, 0, 0) := by
  unfold msSearchP
  simp only [h]

private theorem msSearchP_lt (Z : Rows) (fv : List (List Nat)) (Y : Rows) (j : Nat) :
    (msSearchP Z fv Y j).1 < 12 ∧ (msSearchP Z fv Y j).2.1 < 3 ∧ (msSearchP Z fv Y j).2.2 < 3 := by
  cases hf : (List.range 36).find? (fun i => (zqTP Z fv).getD i 0 == act Y (zqP Z fv 0 j)) with
  | none =>
    rw [msSearchP_none hf]
    exact ⟨by decide, by decide, by decide⟩
  | some i =>
    have hi36 : i < 36 := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    rw [msSearchP_some hf]
    have h1 : i / 3 < 12 := by omega
    have h2 : i % 3 < 3 := Nat.mod_lt _ (by decide)
    dsimp only
    exact ⟨h1, h2, find3_lt (fun f => zqP Z fv f (i / 3) == act Y (zqP Z fv 1 j))⟩

private theorem msSearch_eq {PZ : Nat} {fv : List (List Nat)} {ZQ : Nat → Nat}
    (hZ : ∀ i < 36, ZQ i = (zqTP (unpack 24 24 PZ) fv).getD i 0) (X : Nat) {j : Nat}
    (hj : j < 12) :
    msSearchK ZQ X j = (msSearchP (unpack 24 24 PZ) fv (unpack 24 24 X) j).1 +
      64 * (msSearchP (unpack 24 24 PZ) fv (unpack 24 24 X) j).2.1 +
      4096 * (msSearchP (unpack 24 24 PZ) fv (unpack 24 24 X) j).2.2 := by
  have hv : actK X (zqL ZQ 0 j) = act (unpack 24 24 X) (zqP (unpack 24 24 PZ) fv 0 j) := by
    rw [ActL.act_unpack]
    exact congrArg (actK X) (hZ (3 * j + 0) (by omega))
  have hw : actK X (zqL ZQ 1 j) = act (unpack 24 24 X) (zqP (unpack 24 24 PZ) fv 1 j) := by
    rw [ActL.act_unpack]
    exact congrArg (actK X) (hZ (3 * j + 1) (by omega))
  have hf36 := findV_eq hZ (act (unpack 24 24 X) (zqP (unpack 24 24 PZ) fv 0 j)) 36 0 (by omega)
  rw [← List.range_eq_range'] at hf36
  unfold msSearchK
  rw [MatL.strictN_eq, hv, MatL.strictN_eq, hw, MatL.strictN_eq, hf36]
  cases hf : (List.range 36).find? (fun i => (zqTP (unpack 24 24 PZ) fv).getD i 0 ==
      act (unpack 24 24 X) (zqP (unpack 24 24 PZ) fv 0 j)) with
  | none =>
    rw [msSearchP_none hf]
    rfl
  | some i =>
    have hi36 : i < 36 := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    have hi3 : i / 3 < 12 := by omega
    rw [msSearchP_some hf, Option.getD_some, MatL.nIf_eq, ite_eq_left (Nat.blt_eq.mpr hi36),
      MatL.strictN_eq]
    have hF := findF_eq hZ hi3 (act (unpack 24 24 X) (zqP (unpack 24 24 PZ) fv 1 j))
    calc _ = i / 3 + (64 * (i % 3) + 4096 *
          findF ZQ (i / 3) (act (unpack 24 24 X) (zqP (unpack 24 24 PZ) fv 1 j))) := rfl
      _ = _ := by
        rw [hF]
        dsimp only
        exact (Nat.add_assoc _ _ _).symm

end SplitL

open SplitL in
theorem msOKK_sound {PZ : Nat} {fv : List (List Nat)} {ZQ : Nat → Nat} {X : Nat}
    (hz : zqOK PZ fv ZQ = true) (h : msOKK ZQ X = true) :
    msOKP (unpack 24 24 PZ) fv (unpack 24 24 X) = true := by
  have hZ := zq_bind hz
  unfold msOKP
  rw [List.all_eq_true]
  intro j hjm
  have hj : j < 12 := List.mem_range.1 hjm
  have hb := msSearchP_lt (unpack 24 24 PZ) fv (unpack 24 24 X) j
  have hs := msSearch_eq hZ X hj
  have hj' := MatL.allN_iff.1 h j hj
  simp only [MatL.strictB_eq] at hj'
  generalize hd : msSearchK ZQ X j = d at hj'
  change (Nat.blt (d % 64) 12 && (Nat.blt (d / 64 % 64) 3 &&
    (!(Nat.beq ((d / 4096 + 3 - d / 64 % 64) % 3) 0) &&
      CFSG.KC.Enum.allN 3 (fun e => Nat.beq (actK X (zqL ZQ e j))
        (zqL ZQ ((d / 64 % 64 + (d / 4096 + 3 - d / 64 % 64) % 3 * e) % 3) (d % 64)))))) =
    true at hj'
  dsimp only
  generalize msSearchP (unpack 24 24 PZ) fv (unpack 24 24 X) j = D at hs hb ⊢
  obtain ⟨k0, a0, f0⟩ := D
  dsimp only at hs hb ⊢
  obtain ⟨hk0, ha0, hf0⟩ := hb
  rw [hs] at hd
  have he3 : (d / 4096 + 3 - d / 64 % 64) % 3 = (f0 + 3 - a0) % 3 := by omega
  have he1 : d % 64 = k0 := by omega
  have he2 : d / 64 % 64 = a0 := by omega
  rw [he3, he1, he2] at hj'
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', MatL.allN_iff] at hj'
  obtain ⟨-, -, hs0, hall⟩ := hj'
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨hk0, ha0⟩, fun e0 => ?_⟩, fun e he => ?_⟩
  · rw [e0] at hs0
    exact Bool.noConfusion hs0
  · have hq := Nat.eq_of_beq_eq_true (hall e he)
    have hx : (a0 + (f0 + 3 - a0) % 3 * e) % 3 < 3 := Nat.mod_lt _ (by decide)
    rw [← ActL.act_unpack] at hq
    have l1 : zqL ZQ e j = zqP (unpack 24 24 PZ) fv e j := hZ (3 * j + e) (by omega)
    have l2 : zqL ZQ ((a0 + (f0 + 3 - a0) % 3 * e) % 3) k0 =
        zqP (unpack 24 24 PZ) fv ((a0 + (f0 + 3 - a0) % 3 * e) % 3) k0 :=
      hZ (3 * k0 + (a0 + (f0 + 3 - a0) % 3 * e) % 3) (by omega)
    rw [l1, l2] at hq
    exact hq

theorem wordSK_sound {M MI : Nat → Nat} {k R : Nat} {w : List Nat}
    (h : bAnd(lettersK k w, Nat.beq (wordSK M MI w) R) = true) :
    word ((List.range k).map fun i => unpack 24 24 (M i))
      ((List.range k).map fun i => unpack 24 24 (MI i)) (decWord w) = unpack 24 24 R := by
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  have e := MatS.word_eq_wordSK (M := M) (MI := MI) h.1
  rw [Nat.eq_of_beq_eq_true h.2] at e
  exact e

private noncomputable def lowOK (N : Nat) (ls : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => Bool.rec (motive := fun _ => Bool) false ih (lettersK N w)) ls

private theorem lowOK_cons (N : Nat) (w : List Nat) (ls : List (List Nat)) :
    lowOK N (w :: ls) = (lettersK N w && lowOK N ls) :=
  MatL.bAnd_eq _ _

theorem gValK_sound {A AI S SI : Nat → Nat} {N : Nat} {t : List Nat} {ls : List (List Nat)}
    (h : gLettersK N t ls = true) :
    ls.foldl (fun X w => mul X (word ((List.range N).map fun i => unpack 24 24 (S i))
        ((List.range N).map fun i => unpack 24 24 (SI i)) (decWord w)))
      (word ((List.range 2).map fun i => unpack 24 24 (A i))
        ((List.range 2).map fun i => unpack 24 24 (AI i)) (decWord t)) =
      unpack 24 24 (gValK A AI S SI t ls) := by
  unfold gLettersK at h
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨ht, hl⟩ := h
  have hl' : lowOK N ls = true := hl
  clear hl
  have et := MatS.word_eq_wordSK (M := A) (MI := AI) ht
  unfold MatL.rowsL at et
  rw [et]
  unfold gValK
  generalize wordSK A AI t = a
  induction ls generalizing a with
  | nil => rfl
  | cons w ls ih =>
    rw [lowOK_cons, Bool.and_eq_true] at hl'
    have ew := MatS.word_eq_wordSK (M := S) (MI := SI) hl'.1
    unfold MatL.rowsL at ew
    rw [List.foldl_cons, ew, ← MatL.unpack_mulK]
    change _ = unpack 24 24 (CFSG.KC.Enum.strictN (mulK a (wordSK S SI w)) _)
    rw [MatL.strictN_eq]
    exact ih hl'.2 _

theorem splitK_sound {PA PB AI BI PZ : Nat} {XI A G : Nat → Nat} {fv LR : List (List Nat)}
    {ZQ : Nat → Nat}
    (hab : bAnd(invOKK PA AI, invOKK PB BI) = true)
    (hz : zqOK PZ fv ZQ = true)
    (hg : ∀ i < 3, CFSG.KS.Raw.bindListK 24 24 (G i) (LR.getD i []) = true)
    (hm : gensK ZQ A G XI = true) :
    splitCheckP (unpack 24 24 PA) (unpack 24 24 PB) true (fun i => unpack 24 24 (G i))
      (fun i => unpack 24 24 (A i)) (unpack 24 24 PZ) fv LR = true := by
  rw [MatL.bAnd_eq, Bool.and_eq_true] at hab
  obtain ⟨ma, ia⟩ := MatL.invOK_of hab.1
  obtain ⟨mb, ib⟩ := MatL.invOK_of hab.2
  have hone : ∀ {X Y : Nat}, invOKK X Y = true → msOKK ZQ X = true → msOKK ZQ Y = true →
      (mul (unpack 24 24 X) (inv (unpack 24 24 X)) == one () &&
        msOKP (unpack 24 24 PZ) fv (unpack 24 24 X) &&
        msOKP (unpack 24 24 PZ) fv (inv (unpack 24 24 X))) = true := by
    intro X Y hXY hX hY
    obtain ⟨m, i⟩ := MatL.invOK_of hXY
    rw [i, m, msOKK_sound hz hX, msOKK_sound hz hY]
    rfl
  have hgen : ∀ k < 9, ∀ X, X = Bool.rec (motive := fun _ => Nat) (G (k - 6)) (A k) (Nat.blt k 6) →
      (mul (unpack 24 24 X) (inv (unpack 24 24 X)) == one () &&
        msOKP (unpack 24 24 PZ) fv (unpack 24 24 X) &&
        msOKP (unpack 24 24 PZ) fv (inv (unpack 24 24 X))) = true := by
    intro k hk X hX
    have h := MatL.allN_iff.1 hm k hk
    simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true] at h
    change invOKK (Bool.rec (motive := fun _ => Nat) (G (k - 6)) (A k) (Nat.blt k 6)) (XI k) = true ∧
      msOKK ZQ (Bool.rec (motive := fun _ => Nat) (G (k - 6)) (A k) (Nat.blt k 6)) = true ∧
      msOKK ZQ (XI k) = true at h
    rw [← hX] at h
    exact hone h.1 h.2.1 h.2.2
  unfold splitCheckP
  dsimp only
  have hL : ∀ i < 3, (unpack 24 24 (G i) == (LR.getD i []).toArray) = true := fun i hi => by
    rw [CFSG.KS.Raw.toArray_eq_of_bindListK (hg i hi)]
    exact beq_self_eq_true _
  have hX : ∀ X ∈ (List.range 6).map (fun i => unpack 24 24 (A i)) ++
      (List.range 3).map (fun i => unpack 24 24 (G i)),
      (mul X (inv X) == one () && msOKP (unpack 24 24 PZ) fv X &&
        msOKP (unpack 24 24 PZ) fv (inv X)) = true := by
    intro X hXm
    rcases List.mem_append.1 hXm with hXm | hXm
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hXm
      have hi6 : i < 6 := List.mem_range.1 hi
      refine hgen i (by omega) (A i) ?_
      rw [MatL.nIf_eq, ite_eq_left (Nat.blt_eq.mpr hi6)]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hXm
      have hi3 : i < 3 := List.mem_range.1 hi
      refine hgen (i + 6) (by omega) (G i) ?_
      rw [MatL.nIf_eq, ite_eq_right (by rw [Nat.blt_eq]; omega), Nat.add_sub_cancel]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, trivial⟩, fun i hi => ?_⟩, fun X hXm => ?_⟩
  · rw [ia]
    exact ma
  · rw [ib]
    exact mb
  · exact beq_iff_eq.1 (hL i hi)
  · simpa only [Bool.and_eq_true, beq_iff_eq] using hX X hXm

theorem unpack_powK (X : Nat) : ∀ e, unpack 24 24 (powK X e) = pow (unpack 24 24 X) e
  | 0 => MatL.unpack_idM
  | e + 1 => by
    change unpack 24 24 (CFSG.KC.Enum.strictN (powK X e) (fun Y => mulK Y X)) =
      mul (pow (unpack 24 24 X) e) (unpack 24 24 X)
    rw [MatL.strictN_eq, MatL.unpack_mulK, unpack_powK X e]

private theorem foldN6_eq (f : Nat → Nat → Nat) (s : Nat) :
    CFSG.KC.Enum.foldN 6 f s = (List.range 6).foldr f s := by
  have h : CFSG.KC.Enum.foldN 6 f s = CFSG.KC.Enum.foldBlk 0 f 6 s := rfl
  rw [h, MatL.foldBlk_eq]
  simp only [Nat.zero_add]

private theorem dig3_enc3 (l : List Nat) {i : Nat} (hi : i < 6) :
    dig3 (enc3 l) i = l.getD i 0 % 3 := by
  have em : ∀ x y : Nat, Nat.mod x y = x % y := fun _ _ => rfl
  have ed : ∀ x y : Nat, Nat.div x y = x / y := fun _ _ => rfl
  have e : enc3 l = l.getD 5 0 % 3 * 243 + l.getD 4 0 % 3 * 81 + l.getD 3 0 % 3 * 27 +
      l.getD 2 0 % 3 * 9 + l.getD 1 0 % 3 * 3 + l.getD 0 0 % 3 := by
    unfold enc3
    rw [foldN6_eq]
    have r6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
    simp only [r6, List.foldr_cons, List.foldr_nil, Nat.add_eq, Nat.mul_eq,
      Nat.pow_eq, em, SplitL.nget_eq]
    omega
  unfold dig3
  rw [e]
  simp only [em, ed, Nat.pow_eq]
  have h0 := Nat.mod_lt (l.getD 0 0) (by decide : 3 > 0)
  have h1 := Nat.mod_lt (l.getD 1 0) (by decide : 3 > 0)
  have h2 := Nat.mod_lt (l.getD 2 0) (by decide : 3 > 0)
  have h3 := Nat.mod_lt (l.getD 3 0) (by decide : 3 > 0)
  have h4 := Nat.mod_lt (l.getD 4 0) (by decide : 3 > 0)
  have h5 := Nat.mod_lt (l.getD 5 0) (by decide : 3 > 0)
  obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    omega
  all_goals norm_num
  all_goals omega

theorem unpack_eProdK (A : Nat → Nat) (l : List Nat) :
    unpack 24 24 (eProdK A (enc3 l)) = eRowsP (fun i => unpack 24 24 (A i)) (expVec l) := by
  have hv : ∀ k : Fin 6, (expVec l k).val = dig3 (enc3 l) k.val := fun k => by
    rw [dig3_enc3 l k.2]
    unfold expVec
    exact ZMod.val_natCast _ _
  unfold eProdK eRowsP
  rw [foldN6_eq]
  have r6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  have f6 : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [r6, f6]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, MatL.unpack_mulK,
    unpack_powK, MatL.unpack_idM, hv]
  rfl

theorem unpack_inj {X Y : Nat} (hX : Nat.shiftRight X 576 = 0) (hY : Nat.shiftRight Y 576 = 0)
    (h : unpack 24 24 X = unpack 24 24 Y) : X = Y := by
  have hz : ∀ Z : Nat, Nat.shiftRight Z 576 = 0 → ∀ b, 576 ≤ b → Z.testBit b = false := by
    intro Z hZ b hb
    have e := Nat.testBit_shiftRight (i := 576) (j := b - 576) Z
    have e' : Z >>> 576 = 0 := hZ
    rw [e', Nat.zero_testBit, Nat.add_sub_cancel' hb] at e
    exact e.symm
  have hr : ∀ i < 24, MatL.rowV X i = MatL.rowV Y i := fun i hi => by
    rw [← MatL.unpack_getD X i hi, ← MatL.unpack_getD Y i hi, h]
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 576
  · have key : ∀ Z : Nat, Z.testBit b = (MatL.rowV Z (b / 24)).testBit (b % 24) := by
      intro Z
      unfold MatL.rowV
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      simp only [Nat.mod_lt b (by decide : 24 > 0), decide_true, Bool.true_and]
      congr 1
      omega
    rw [key X, key Y, hr _ (by omega)]
  · rw [hz X hX b (by omega), hz Y hY b (by omega)]

theorem unpack_ne_one {X : Nat} (hs : Nat.beq (Nat.shiftRight X 576) 0 = true)
    (hne : Bool.rec (motive := fun _ => Bool) true false (Nat.beq X idM) = true) :
    (unpack 24 24 X != one ()) = true := by
  have hI : Nat.shiftRight idM 576 = 0 := by decide +kernel
  rw [bne_iff_ne, ne_eq]
  intro e
  rw [← MatL.unpack_idM] at e
  rw [unpack_inj (Nat.eq_of_beq_eq_true hs) hI e, Nat.beq_refl] at hne
  exact absurd hne (by decide)

theorem mulK_shift (X Y : Nat) : Nat.shiftRight (mulK X Y) 576 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  have e : Nat.shiftRight (mulK X Y) 576 = mulK X Y >>> 576 := rfl
  rw [e, Nat.testBit_shiftRight, Nat.zero_testBit]
  unfold mulK
  rw [MatL.foldN_eq, MatL.pack_testBit (fun i => vmulK (rowK X i) Y), List.any_eq_false]
  intro i hi
  have hi24 := List.mem_range.1 hi
  rw [MatL.testBit_false_of_lt (MatL.vmulK_lt _ _) (by omega), Bool.and_false]
  exact Bool.false_ne_true

theorem actK_lt (X v : Nat) : actK X v < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [ActL.actK_eq_foldr, ActL.testBit_foldr_or]
  have : ¬ i < 24 := by omega
  simp [this]

private theorem foldr_xor_lt (p : Nat → Bool) (g : Nat → Nat) :
    ∀ l : List Nat, (∀ k ∈ l, g k < 2 ^ 24) →
      l.foldr (fun k s => Bool.rec (motive := fun _ => Nat) s (Nat.xor s (g k)) (p k)) 0 < 2 ^ 24
  | [], _ => Nat.two_pow_pos 24
  | k :: l, h => by
    rw [List.foldr_cons]
    have ih := foldr_xor_lt p g l fun k hk => h k (List.mem_cons_of_mem _ hk)
    cases p k
    · exact ih
    · exact Nat.xor_lt_two_pow ih (h k (List.mem_cons_self ..))

theorem qK_lt (PZ : Nat) (fv : List (List Nat)) (j : Nat) : qK PZ fv j < 2 ^ 24 := by
  unfold qK f4LoK f4HiK
  rw [SplitL.foldN12_eq, SplitL.foldN12_eq]
  refine Nat.xor_lt_two_pow (foldr_xor_lt _ (fun k => Nat.shiftLeft 1 k) _ fun k hk => ?_)
    (foldr_xor_lt _ (fun k => actK PZ (Nat.shiftLeft 1 k)) _ fun k _ => actK_lt _ _)
  have hk12 := List.mem_range.1 hk
  change 1 <<< k < 2 ^ 24
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem qK_unpack (PZ : Nat) (fv : List (List Nat)) (j : Nat) :
    qK PZ fv j = qNatP (unpack 24 24 PZ) fv j :=
  SplitL.qK_eq PZ fv j

private theorem ngetLL_eq : ∀ (l : List (List (List Nat))) (i : Nat),
    CFSG.KS.SporSch.Orb.ngetLL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => ngetLL_eq l i

open SplitL in
private theorem msSearch_dec {PZ : Nat} {fv : List (List Nat)} {ZQ : Nat → Nat}
    (hZ : ∀ i < 36, ZQ i = (zqTP (unpack 24 24 PZ) fv).getD i 0) (X : Nat) {j : Nat}
    (hj : j < 12) :
    Nat.mod (msSearchK ZQ X j) 64 = (msSearchP (unpack 24 24 PZ) fv (unpack 24 24 X) j).1 ∧
      sgnK (msSearchK ZQ X j) = msSgnP (unpack 24 24 PZ) fv (unpack 24 24 X) j := by
  have hb := msSearchP_lt (unpack 24 24 PZ) fv (unpack 24 24 X) j
  rw [msSearch_eq hZ X hj]
  unfold msSgnP sgnK
  generalize msSearchP (unpack 24 24 PZ) fv (unpack 24 24 X) j = D at hb ⊢
  obtain ⟨k0, a0, f0⟩ := D
  dsimp only at hb ⊢
  change (k0 + 64 * a0 + 4096 * f0) % 64 = k0 ∧
    ((k0 + 64 * a0 + 4096 * f0) / 4096 + 3 - (k0 + 64 * a0 + 4096 * f0) / 64 % 64) % 3 =
      (f0 + 3 - a0) % 3
  omega

open SplitL in
theorem splitDataK_sound {PZ : Nat} {A G : Nat → Nat} {fv LP LS : List (List Nat)} {ZQ : Nat → Nat}
    (hz : zqOK PZ fv ZQ = true)
    (h : dataK ZQ A G LP LS = true) :
    splitDataCheckP (fun i => unpack 24 24 (G i)) (fun i => unpack 24 24 (A i)) (unpack 24 24 PZ)
      fv LP LS = true := by
  have hZ := zq_bind hz
  unfold dataK at h
  rw [MatL.bAnd_eq, MatL.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold splitDataCheckP
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩, fun j hj => ?_⟩
  · have hc := MatL.allN_iff.1 (MatL.allN_iff.1 h1 i hi) j hj
    simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hc
    obtain ⟨e1, e2⟩ := msSearch_dec hZ (A i) hj
    rw [e1, e2] at hc
    exact hc
  · have hc := MatL.allN_iff.1 (MatL.allN_iff.1 h2 i hi) j hj
    simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, nget_eq,
      ngetL_eq] at hc
    obtain ⟨e1, e2⟩ := msSearch_dec hZ (G i) hj
    rw [e1, e2] at hc
    exact hc
  · have hc := MatL.allN_iff.1 h3 j hj
    simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hc
    obtain ⟨e1, e2⟩ := msSearch_dec hZ (G 2) hj
    rw [e1, e2] at hc
    exact hc

open SplitL in
theorem conjK_sound {A G GI : Nat → Nat} {CE : List (List (List Nat))} {CR : List (List Nat)}
    (h : conjK A G GI CE CR = true) :
    splitConjCheckP (fun i => unpack 24 24 (G i)) (fun i => unpack 24 24 (A i)) CE CR = true := by
  unfold conjK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hI, hC, hR, hsq, hsh, hne⟩ := h
  have hinv : ∀ i < 3, inv (unpack 24 24 (G i)) = unpack 24 24 (GI i) := fun i hi =>
    (MatL.invOK_of (MatL.allN_iff.1 hI i hi)).2
  unfold splitConjCheckP
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨fun i hi j hj => ?_, fun i hi => ?_⟩, ?_⟩, unpack_ne_one hsh hne⟩
  · have e := Nat.eq_of_beq_eq_true (MatL.allN_iff.1 (MatL.allN_iff.1 hC i hi) j hj)
    rw [hinv i hi, ← MatL.unpack_mulK, ← MatL.unpack_mulK, e, unpack_eProdK, ngetLL_eq, ngetL_eq]
  · have e := Nat.eq_of_beq_eq_true (MatL.allN_iff.1 hR i hi)
    rw [hinv 2 (by omega), hinv i (by omega), ← MatL.unpack_mulK, ← MatL.unpack_mulK,
      ← MatL.unpack_mulK, e, unpack_eProdK, ngetL_eq]
  · rw [← MatL.unpack_mulK, Nat.eq_of_beq_eq_true hsq, MatL.unpack_idM]

open SplitL in
theorem zqK_sound {PZ : Nat} {fv : List (List Nat)} {ZQ : Nat → Nat} (hz : zqOK PZ fv ZQ = true)
    (h : zqDistK ZQ = true) :
    zqCheckP (unpack 24 24 PZ) fv = true := by
  have hZ := zq_bind hz
  have hZ' : ∀ e j, e < 3 → j < 12 → zqP (unpack 24 24 PZ) fv e j = ZQ (3 * j + e) := by
    intro e j he hj
    unfold zqP
    exact (hZ (3 * j + e) (by omega)).symm
  unfold zqCheckP
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq]
  intro j hj e he
  have hi : 3 * j + e < 36 := by omega
  have h1 := MatL.allN_iff.1 h (3 * j + e) hi
  dsimp only at h1
  rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff] at h1
  refine ⟨?_, fun k hk f hf => ?_⟩
  · rw [hZ' e j he hj]
    simpa using h1.1
  · have hi' : 3 * k + f < 36 := by omega
    have h2 := h1.2 (3 * k + f) hi'
    rw [hZ' e j he hj, hZ' f k hf hk, Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq,
      beq_iff_eq]
    constructor
    · intro hq
      by_contra hjk
      have hne : 3 * j + e ≠ 3 * k + f := by omega
      have hb : Nat.beq (3 * j + e) (3 * k + f) = false :=
        Bool.eq_false_iff.2 fun hh => hne (Nat.eq_of_beq_eq_true hh)
      rw [hb, hq, Nat.beq_refl] at h2
      exact absurd h2 (by decide)
    · rintro ⟨rfl, rfl⟩
      rfl

end CFSG.KS.SporSch.M24

end
