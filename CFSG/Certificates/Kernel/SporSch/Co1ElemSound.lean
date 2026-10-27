module

public import Certificates.Data.Kernel.SporSch.Co1Elem
public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw

@[expose] def eRowsP (a : Nat → Rows) (b : Fin 6 → ZMod 3) : Rows :=
  ((List.finRange 6).map fun i => pow (a i.val) (b i).val).foldr mul one

@[expose] def eCheckP (a : Nat → Rows) : Bool :=
  decide (∀ b ∈ (Finset.univ : Finset (Fin 6 → ZMod 3)), wf (eRowsP a b) = true) &&
    decide ((Finset.univ : Finset (Fin 6 → ZMod 3)).val.map (eRowsP a)).Nodup &&
    (List.finRange 6).all fun i => eRowsP a (Pi.single i 1) == a i.val

@[expose] def f4HiP (Z : Rows) (cs : List Nat) : Nat :=
  (List.finRange 12).foldl
    (fun acc k => if cs.getD k.val 0 / 2 % 2 = 1 then acc ^^^ act Z (1 <<< k.val) else acc) 0

@[expose] def qNatP (Z : Rows) (fv : List (List Nat)) (j : Nat) : Nat :=
  f4Lo (fv.getD j []) ^^^ f4HiP Z (fv.getD j [])

@[expose] def zPowP (Z : Rows) (e : Nat) (v : Nat) : Nat := Nat.iterate (act Z) e v

@[expose] def gamP (ec : List (List Nat)) (j i : Nat) : Nat := (ec.getD j []).getD i 0

@[expose] def qColsP (Z : Rows) (fv : List (List Nat)) : Array Nat := Array.ofFn (n := 24) fun k =>
  if k.val % 2 = 0 then qNatP Z fv (k.val / 2) else act Z (qNatP Z fv (k.val / 2))

@[expose] def qMatP (Z : Rows) (fv : List (List Nat)) : Rows := transposeRows 24 (qColsP Z fv)

@[expose] def eigenP (a : Nat → Rows) (Z : Rows) (fv ec : List (List Nat)) : Bool :=
  (List.range 6).all (fun i => (List.range 12).all fun j =>
      act (a i) (qNatP Z fv j) == zPowP Z (gamP ec j i) (qNatP Z fv j) && decide (gamP ec j i < 3)) &&
    mul Z Z == add Z one && mul (inv (qMatP Z fv)) (qMatP Z fv) == one && a 0 == Z &&
    mul (qMatP Z fv) (inv (qMatP Z fv)) == one

namespace ElemL

open CFSG.KC.Enum CFSG.KS.Mathieu

private theorem unpack_powK (X : Nat) : ∀ e, unpack 24 24 (powK X e) = pow (unpack 24 24 X) e
  | 0 => MatL.unpack_idM
  | e + 1 => by
    change unpack 24 24 (strictN (powK X e) (fun Y => mulK Y X)) =
      mul (pow (unpack 24 24 X) e) (unpack 24 24 X)
    rw [MatL.strictN_eq, MatL.unpack_mulK, unpack_powK X e]

private theorem rowV_xor (a b i : Nat) :
    MatL.rowV (a ^^^ b) i = MatL.rowV a i ^^^ MatL.rowV b i := by
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

private theorem unpack_inj {X Y : Nat} (hX : Nat.shiftRight X 576 = 0)
    (hY : Nat.shiftRight Y 576 = 0) (h : unpack 24 24 X = unpack 24 24 Y) : X = Y := by
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

private theorem mulK_shift (X Y : Nat) : Nat.shiftRight (mulK X Y) 576 = 0 := by
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

private theorem wf_unpack (R : Nat) : wf (unpack 24 24 R) = true := by
  unfold wf
  rw [Bool.and_eq_true]
  refine ⟨by simp [MatL.unpack_size], ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  rw [MatL.unpack_getElem]
  exact decide_eq_true (MatL.rowV_lt R i)

private theorem foldN6_eq (f : Nat → Nat → Nat) (s : Nat) :
    foldN 6 f s = (List.range 6).foldr f s := by
  have h : foldN 6 f s = foldBlk 0 f 6 s := rfl
  rw [h, MatL.foldBlk_eq]
  simp only [Nat.zero_add]

private def enc (b : Fin 6 → ZMod 3) : Nat :=
  (b 0).val + 3 * (b 1).val + 9 * (b 2).val + 27 * (b 3).val + 81 * (b 4).val + 243 * (b 5).val

private theorem enc_lt (b : Fin 6 → ZMod 3) : enc b < 729 := by
  have h := fun i => ZMod.val_lt (b i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  unfold enc
  omega

private theorem dig3_enc (b : Fin 6 → ZMod 3) (k : Fin 6) : dig3 (enc b) k.val = (b k).val := by
  have em : ∀ x y : Nat, Nat.mod x y = x % y := fun _ _ => rfl
  have ed : ∀ x y : Nat, Nat.div x y = x / y := fun _ _ => rfl
  have h := fun i => ZMod.val_lt (b i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  unfold dig3 enc
  simp only [em, ed, Nat.pow_eq]
  fin_cases k
  all_goals norm_num
  all_goals omega

private theorem enc_single (i : Fin 6) : enc (Pi.single i 1) = Nat.pow 3 i.val := by
  fin_cases i <;> decide

private theorem eProdK_eq (A : Nat → Nat) (b : Fin 6 → ZMod 3) :
    unpack 24 24 (eProdK A (enc b)) = eRowsP (fun i => unpack 24 24 (A i)) b := by
  have hv : ∀ k : Fin 6, (b k).val = dig3 (enc b) k.val := fun k => (dig3_enc b k).symm
  unfold eProdK eRowsP
  rw [foldN6_eq]
  have r6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  have f6 : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [r6, f6]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, MatL.unpack_mulK,
    unpack_powK, MatL.unpack_idM, hv]
  rfl

private theorem eProdK_shift (A : Nat → Nat) (n : Nat) : Nat.shiftRight (eProdK A n) 576 = 0 := by
  unfold eProdK
  rw [foldN6_eq]
  exact mulK_shift _ _

private theorem distP_spec (MsP : Nat) : ∀ n M, distP MsP n M = true →
    (∀ k < n, idxK MsP k < 729 ∧ M.testBit (idxK MsP k) = false) ∧
      ∀ k < n, ∀ k' < n, idxK MsP k = idxK MsP k' → k = k'
  | 0, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, M, h => by
    have e : distP MsP (n + 1) M = (Nat.blt (idxK MsP n) 729 &&
        (!M.testBit (idxK MsP n) && distP MsP n (M ||| (1 <<< idxK MsP n)))) := by
      change strictB (idxK MsP n) (fun x => bAnd(Nat.blt x (nat_lit 729),
        bAnd(bIf(hasBit M x, false, true),
          strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) x)) (distP MsP n)))) = _
      rw [MatL.strictB_eq, MatL.bAnd_eq, MatL.bAnd_eq, MatL.strictB_eq, MatL.hasBit_eq]
      cases M.testBit (idxK MsP n) <;> rfl
    rw [e, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    obtain ⟨hlt, hb, hr⟩ := h
    obtain ⟨ih1, ih2⟩ := distP_spec MsP n _ hr
    have hbit : ∀ k < n, M.testBit (idxK MsP k) = false ∧ idxK MsP k ≠ idxK MsP n := by
      intro k hk
      have h2 := (ih1 k hk).2
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.one_shiftLeft, Nat.testBit_two_pow,
        decide_eq_false_iff_not] at h2
      exact ⟨h2.1, fun e' => h2.2 e'.symm⟩
    refine ⟨fun k hk => ?_, fun k hk k' hk' e' => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ⟨(ih1 k hk).1, (hbit k hk).1⟩
      · exact ⟨hlt, hb⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
      · exact ih2 k hk k' hk' e'
      · exact absurd e' (hbit k hk).2
      · exact absurd e'.symm (hbit k' hk').2
      · rfl

private theorem eProdK_inj {A : Nat → Nat} {MsP : Nat} (hd : distP MsP 729 0 = true)
    (hs : ∀ s < 9, incSl A MsP (81 * s) 81 = true) {n n' : Nat} (hn : n < 729) (hn' : n' < 729)
    (e : eProdK A n = eProdK A n') : n = n' := by
  obtain ⟨h1, h2⟩ := distP_spec MsP 729 0 hd
  have hstep : ∀ k, k + 1 < 729 →
      eProdK A (idxK MsP k) < eProdK A (idxK MsP (k + 1)) := by
    intro k hk
    have h0 := hs (k / 81) (by omega)
    unfold incSl at h0
    rw [MatL.allN_iff] at h0
    have h3 := h0 (k % 81) (Nat.mod_lt _ (by decide))
    have ek : Nat.add (81 * (k / 81)) (k % 81) = k := Nat.div_add_mod k 81
    rw [MatL.strictB_eq, ek] at h3
    have hb : Nat.blt (Nat.succ k) 729 = true := Nat.blt_eq.mpr hk
    rw [hb] at h3
    exact Nat.blt_eq.mp h3
  have hmono : ∀ d k, k + d + 1 < 729 →
      eProdK A (idxK MsP k) < eProdK A (idxK MsP (k + d + 1)) := by
    intro d
    induction d with
    | zero => exact hstep
    | succ d ih =>
      intro k hk
      have e1 : k + (d + 1) + 1 = k + d + 1 + 1 := by omega
      rw [e1]
      exact lt_trans (ih k (by omega)) (hstep _ (by omega))
  have hinj : ∀ k < 729, ∀ k' < 729,
      eProdK A (idxK MsP k) = eProdK A (idxK MsP k') → k = k' := by
    intro k hk k' hk' e'
    rcases Nat.lt_trichotomy k k' with hl | rfl | hl
    · have := hmono (k' - k - 1) k (by omega)
      rw [show k + (k' - k - 1) + 1 = k' by omega, e'] at this
      exact absurd this (lt_irrefl _)
    · rfl
    · have := hmono (k - k' - 1) k' (by omega)
      rw [show k' + (k - k' - 1) + 1 = k by omega, e'] at this
      exact absurd this (lt_irrefl _)
  let g : Fin 729 → Fin 729 := fun k => ⟨idxK MsP k.val, (h1 k.val k.isLt).1⟩
  have hg : Function.Injective g := fun k k' e' =>
    Fin.ext (h2 k.val k.isLt k'.val k'.isLt (congrArg Fin.val e'))
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hg) ⟨n, hn⟩
  obtain ⟨k', hk'⟩ := (Finite.injective_iff_surjective.1 hg) ⟨n', hn'⟩
  have ek : idxK MsP k.val = n := congrArg Fin.val hk
  have ek' : idxK MsP k'.val = n' := congrArg Fin.val hk'
  rw [← ek, ← ek'] at e ⊢
  rw [hinj k.val k.isLt k'.val k'.isLt e]

private theorem nget_eq : ∀ (l : List Nat) (i : Nat), nget l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nget_eq l i

private theorem ngetL_eq : ∀ (l : List (List Nat)) (i : Nat), ngetL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => ngetL_eq l i

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

private theorem f4HiK_eq (PZ : Nat) (cs : List Nat) :
    f4HiK PZ cs = f4HiP (unpack 24 24 PZ) cs := by
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

private theorem actK_lt (X v : Nat) : actK X v < 2 ^ 24 := by
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

private theorem qK_lt (PZ : Nat) (fv : List (List Nat)) (j : Nat) : qK PZ fv j < 2 ^ 24 := by
  unfold qK f4LoK f4HiK
  rw [foldN12_eq, foldN12_eq]
  refine Nat.xor_lt_two_pow (foldr_xor_lt _ (fun k => Nat.shiftLeft 1 k) _ fun k hk => ?_)
    (foldr_xor_lt _ (fun k => actK PZ (Nat.shiftLeft 1 k)) _ fun k _ => actK_lt _ _)
  have hk12 := List.mem_range.1 hk
  change 1 <<< k < 2 ^ 24
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

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

private theorem transOK_eq {PZ PQ : Nat} {fv : List (List Nat)} (h : transOK PZ PQ fv = true) :
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
    rw [MatL.strictN_eq, MatL.nIf_eq, qK_eq]
    have e1 : Nat.shiftRight t 1 = t / 2 := (Nat.shiftRight_eq_div_pow t 1).trans (by norm_num)
    have e2 : Nat.land t 1 = t % 2 := Nat.and_one_is_mod t
    rw [e1, e2]
    simp only [qColsP, Array.getElem?_ofFn, ht, ↓reduceDIte, Option.getD_some, Nat.beq_eq,
      ActL.act_unpack]
  unfold transOK at h
  rw [MatL.strictB_eq, MatL.allN_iff] at h
  have hrow : ∀ k < 24, rowK (foldN 24 (fun k s => Nat.lor s
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

end ElemL

open ElemL

theorem elemK_sound {A : Nat → Nat} (h : elemK A = true) :
    ((List.range 6).all (fun i => (List.range 6).all fun j =>
        mul (unpack 24 24 (A i)) (unpack 24 24 (A j)) ==
          mul (unpack 24 24 (A j)) (unpack 24 24 (A i))) &&
      (List.range 6).all fun i => pow (unpack 24 24 (A i)) 3 == one) = true := by
  unfold elemK at h
  rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff, MatL.allN_iff] at h
  obtain ⟨hc, hp⟩ := h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.all_eq_true]
    intro j hj
    have e := Nat.eq_of_beq_eq_true
      (MatL.allN_iff.1 (hc i (List.mem_range.1 hi)) j (List.mem_range.1 hj))
    rw [← MatL.unpack_mulK, ← MatL.unpack_mulK, e]
    exact beq_self_eq_true _
  · have e := Nat.eq_of_beq_eq_true (hp i (List.mem_range.1 hi))
    rw [← unpack_powK, e, MatL.unpack_idM]
    exact beq_self_eq_true _

theorem eK_sound {A : Nat → Nat} {MsP : Nat} (h : eK A MsP = true)
    (hs : ∀ s < 9, incSl A MsP (81 * s) 81 = true) :
    eCheckP (fun i => unpack 24 24 (A i)) = true := by
  unfold eK at h
  rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff] at h
  obtain ⟨hd, hg⟩ := h
  unfold eCheckP
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true fun b _ => ?_, decide_eq_true ?_⟩, ?_⟩
  · rw [← eProdK_eq]
    exact wf_unpack _
  · refine Multiset.Nodup.map (fun b b' e => ?_) Finset.univ.nodup
    rw [← eProdK_eq, ← eProdK_eq] at e
    have en := eProdK_inj hd hs (enc_lt b) (enc_lt b')
      (unpack_inj (eProdK_shift A _) (eProdK_shift A _) e)
    funext k
    apply ZMod.val_injective
    rw [← dig3_enc b k, ← dig3_enc b' k, en]
  · rw [List.all_eq_true]
    intro i _
    rw [← eProdK_eq, enc_single, Nat.eq_of_beq_eq_true (hg i.val i.isLt)]
    exact beq_self_eq_true _

theorem eigenK_sound {A : Nat → Nat} {PZ PQ PQI : Nat} {fv ec : List (List Nat)}
    (h : eigenK A PZ PQ PQI fv ec = true) :
    eigenP (fun i => unpack 24 24 (A i)) (unpack 24 24 PZ) fv ec = true := by
  unfold eigenK at h
  rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.bAnd_eq, Bool.and_eq_true, MatL.bAnd_eq,
    Bool.and_eq_true, MatL.bAnd_eq, Bool.and_eq_true, MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hQ := transOK_eq h3
  have hI := MatL.invOK_of h4
  have hI' := MatL.invOK_of h5
  unfold eigenP
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, hQ, hI.2]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    have hij := MatL.allN_iff.1 (MatL.allN_iff.1 h1 i (List.mem_range.1 hi)) j
      (List.mem_range.1 hj)
    rw [MatL.strictB_eq, MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, qK_eq,
      zPowK_eq, nget_eq, ngetL_eq] at hij
    obtain ⟨hg, ha⟩ := hij
    rw [ActL.act_unpack]
    unfold gamP
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨Nat.eq_of_beq_eq_true ha, hg⟩
  · have e : Nat.xor PZ idM = PZ ^^^ idM := rfl
    rw [← MatL.unpack_mulK, Nat.eq_of_beq_eq_true h2, e, unpack_xor, MatL.unpack_idM]
    exact beq_self_eq_true _
  · rw [hI'.1]
    exact beq_self_eq_true _
  · change (unpack 24 24 (A 0) == unpack 24 24 PZ) = true
    rw [Nat.eq_of_beq_eq_true h6]
    exact beq_self_eq_true _
  · rw [hI.1]
    exact beq_self_eq_true _

end CFSG.KS.SporSch.M24

end
