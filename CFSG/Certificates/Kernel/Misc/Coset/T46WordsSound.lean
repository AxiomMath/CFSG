module

public import Certificates.Data.Kernel.Misc.Coset.T46Words
public import CFSG.Certificates.Kernel.Misc.T46Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

namespace CFSG.KC.MiscCoset.T46W.Aux

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46 CFSG.F4.Native
  CFSG.Sporadic.Th.Native

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem ble_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem nbeq_eq (a b : ℕ) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [beq_iff, beq_iff_eq])

theorem allN_iff {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

theorem listAnd_iff {α : Type} (g : α → Bool) (l : List α) :
    List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (g w) ih) l = true ↔
      ∀ w ∈ l, g w = true := by
  induction l with
  | nil => simp
  | cons w l ih =>
    change andB (g w) (List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (g w) ih) l) =
      true ↔ _
    rw [andB_iff, ih, List.forall_mem_cons]

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show Nat.succ (lenN l) = _
    rw [ih]
    rfl

theorem nthN_eq (l : List ℕ) (i : ℕ) : wordM7.nthN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      show wordM7.nthN l i = _
      rw [ih]
      rfl

theorem at'_eq (w P i : ℕ) : at' w P i = P >>> (w * i) % 2 ^ w := by
  change (P >>> (w * i)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem at'_lt (w P i : ℕ) : at' w P i < 2 ^ w := by
  rw [at'_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem getElem_of_ofFn {n : ℕ} {f : Fin n → ℕ} {L : List ℕ} (hL : L = List.ofFn f) (i : ℕ)
    (h : i < L.length) (hn : i < n) : L[i] = f ⟨i, hn⟩ := by
  subst hL
  simp

theorem allIn_iff {n : ℕ} {p : ℕ → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    have := h ⟨i, by omega⟩ (List.mem_finRange _)
    simpa using this
  · intro h k _
    simpa using h k.val (by have := k.isLt; omega)

theorem arr_get (a : Array ℕ) (i : ℕ) : a[i]! = a.toList.getD i 0 := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, List.getD_eq_getElem _ _ (by simpa using h), Array.getElem_toList]
  · rw [getElem!_neg a i h, List.getD_eq_default _ _ (by simpa using h)]
    rfl

theorem recFold (g : ℕ → ℕ → ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => g acc i) n = (List.range n).foldl g 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← recFold g n]
    rfl

theorem hermK_eq (c d : ℕ) : hermK c d = hermC c d := by
  have : hermK c d = Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => acc ^^^ f4mul (coord c i) (f4mul (coord d i) (coord d i))) 6 := by
    unfold hermK
    simp only [letN_eq]
    rfl
  rw [this]
  exact recFold (fun acc i => acc ^^^ f4mul (coord c i) (f4mul (coord d i) (coord d i))) 6

theorem scaleK_eq (a c : ℕ) : scaleK a c = scaleC a c :=
  recFold (fun acc i => acc + f4mul a (coord c i) * 4 ^ i) 6

theorem leadK_eq (c : ℕ) : leadK c = leadC c := by
  have sel : ∀ x acc : ℕ, Bool.rec (motive := fun _ => ℕ) x acc (Nat.beq x 0) =
      if x = 0 then acc else x := by
    intro x acc
    rcases x with _ | n
    · simp
    · have hb : Nat.beq (n + 1) 0 = false := rfl
      simp [hb]
  have sel2 : ∀ x acc : ℕ, (if (x != 0) = true then x else acc) = if x = 0 then acc else x := by
    intro x acc
    by_cases h : x = 0 <;> simp [h]
  show letN (coord c 0) (fun e => Bool.rec (motive := fun _ => ℕ) e
      (letN (coord c 1) (fun e => Bool.rec (motive := fun _ => ℕ) e
        (letN (coord c 2) (fun e => Bool.rec (motive := fun _ => ℕ) e
          (letN (coord c 3) (fun e => Bool.rec (motive := fun _ => ℕ) e
            (letN (coord c 4) (fun e => Bool.rec (motive := fun _ => ℕ) e
              (letN (coord c 5) (fun e => Bool.rec (motive := fun _ => ℕ) e 0 (Nat.beq e 0)))
              (Nat.beq e 0))) (Nat.beq e 0))) (Nat.beq e 0))) (Nat.beq e 0))) (Nat.beq e 0)) =
    (if (coord c 0 != 0) = true then coord c 0 else if (coord c 1 != 0) = true then coord c 1
      else if (coord c 2 != 0) = true then coord c 2 else if (coord c 3 != 0) = true then coord c 3
      else if (coord c 4 != 0) = true then coord c 4 else if (coord c 5 != 0) = true then coord c 5
      else 0)
  simp only [letN_eq, sel, sel2]

theorem normK_eq (c : ℕ) : normK c = normC c := by
  unfold normK
  simp only [letN_eq, scaleK_eq, leadK_eq]
  rfl

theorem tvK_eq (v x : ℕ) : tvK v x = tvC v x := by
  unfold tvK
  rw [scaleK_eq, hermK_eq]
  rfl

theorem weightK_eq (c : ℕ) : weightK c = weightC c := by
  have : ∀ n, ((List.range n).filter fun i => coord c i != 0).length =
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc
        (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (crdK c i) 0))) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      show _ = Nat.add _ (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (coord c n) 0))
      congr 1
      rcases hc : coord c n with _ | m
      · rw [show Nat.beq 0 0 = true from rfl]
        show _ = 0
        simp [hc]
      · rw [show Nat.beq (m + 1) 0 = false from rfl]
        show _ = 1
        simp [hc]
  exact (this 6).symm

theorem gensK_eq (l : List ℕ) : gensK l = l.filter (fun c => weightC c == 2) ++ [85] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    show Bool.rec (motive := fun _ => List ℕ) (gensK l) (c :: gensK l) (Nat.beq (weightK c) 2) = _
    rw [weightK_eq, nbeq_eq, ih, List.filter_cons]
    cases (weightC c == 2) <;> rfl

theorem ap_idT {n i : ℕ} (hi : i < n) (hn : n < 2 ^ 32) : ap (idT n) i = i := by
  unfold ap idT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact UInt32.toNat_ofNat_of_lt' (show i < 2 ^ 32 by omega)

theorem ap_compT {n : ℕ} (P Q : Table) {i : ℕ} (hi : i < n) :
    ap (compT n P Q) i = ap P (ap Q i) := by
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem size_wordT (n : ℕ) (gens : ℤ → Table) : ∀ w, (wordT n gens w).size = n
  | [] => by simp [wordT, idT]
  | z :: w => by
    show ((wordT n gens w).map fun t => (gens z)[t.toNat]!).size = n
    rw [Array.size_map, size_wordT n gens w]

theorem ap_wordT_cons (n : ℕ) (gens : ℤ → Table) (z : ℤ) (w : List ℤ) {x : ℕ} (hx : x < n) :
    ap (wordT n gens (z :: w)) x = ap (gens z) (ap (wordT n gens w) x) := by
  show ap ((wordT n gens w).map fun t => (gens z)[t.toNat]!) x = _
  unfold ap
  rw [getElem!_pos _ x (by rw [Array.size_map, size_wordT]; exact hx), Array.getElem_map,
    ← getElem!_pos _ x (by rw [size_wordT]; exact hx)]

end CFSG.KC.MiscCoset.T46W.Aux

public section

namespace CFSG.KC.MiscCoset.T46W

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi22.Native CFSG.KC.Misc.T46

@[expose] def wordsG (U : Array Nat) (rws : List (List Int)) (xw xp yw yp : List Int) : Bool :=
  rws.all (fun r => t46FixAll (wordT 693 (genG U) r)) &&
    t46TblEq (wordT 693 (genG U) xw) (powT 693 3 (wordT 693 (genG U) xp)) &&
    t46TblEq (wordT 693 (genG U) yw) (powT 693 2 (wordT 693 (genG U) yp)) &&
    allIn 0 46 (fun k => t46FixAll (compT 693 (genG U ((k : ℤ) + 1)) (genG U ((k : ℤ) + 1))))

theorem pointK_sound {U : Array Nat} {UL : List Nat} {UP : Nat} {GP : List Nat}
    {A : Nat → Nat} {rws : List (List Int)} {xw xp yw yp : List Int} (hU : U = UL.toArray)
    (hp : ptsK UL UP = true) (hg : ∀ k < 46, gensOK UL UP GP k 1 = true)
    (hl : lettersK rws xw xp yw yp = true)
    (h : ∀ x < 693, pointK A GP rws xw xp yw yp x = true) : wordsG U rws xw xp yw yp = true := by
  open Aux CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 in
  subst hU
  unfold ptsK at hp
  rw [andB_iff, andB_iff, andB_iff, andB_iff, beq_iff, allN_iff, allN_iff] at hp
  obtain ⟨hlen, -, hat, hinc, -⟩ := hp
  rw [lenN_eq] at hlen
  have hat' : ∀ i (hi : i < 693), at' 12 UP i = UL[i]'(by omega) := fun i hi => by
    rw [beq_iff.1 (hat i hi), nthN_eq, List.getD_eq_getElem _ _ (by omega)]
  have hnd : UL.Nodup := by
    obtain ⟨M, hM⟩ : ∃ M, M = List.ofFn (fun i : Fin 693 => at' 12 UP i.val) := ⟨_, rfl⟩
    have hUM : UL = M := by
      apply List.ext_getElem (by rw [hM, List.length_ofFn, hlen])
      intro j h1 h2
      have hj : j < 693 := by omega
      rw [← hat' j hj, getElem_of_ofFn hM j h2 hj]
    rw [hUM, hM]
    apply List.SortedLT.nodup
    rw [List.sortedLT_ofFn_iff]
    exact Fin.strictMono_iff_lt_succ.2 fun i => blt_iff.1 (hinc i.val i.isLt)
  have hux : ∀ x < 693, (UL.toArray)[x]! = at' 12 UP x := fun x hx => by
    rw [arr_get, List.toList_toArray, ← nthN_eq, beq_iff.1 (hat x hx)]
  have htv : (CFSG.KC.Misc.T46.tvGensG UL.toArray).toList = gensK UL := by
    rw [CFSG.KC.Misc.T46.tvGensG, Array.toList_push, Array.toList_filter, List.toList_toArray,
      gensK_eq]
  have hpt : ∀ x < 693, (∀ k < 46, A (x * 46 + k) = at' 10 (wordM7.nthN GP k) x) ∧
      (∀ w ∈ rws, walkT A w x = x) ∧
      walkT A xw x = walkT A xp (walkT A xp (walkT A xp x)) ∧
      walkT A yw x = walkT A yp (walkT A yp x) ∧
      ∀ k < 46, A (A (x * 46 + k) * 46 + k) = x := by
    intro x hx
    have hx' := h x hx
    unfold pointK at hx'
    rw [andB_iff, andB_iff, andB_iff, andB_iff, allN_iff, allN_iff, beq_iff, beq_iff,
      listAnd_iff] at hx'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx'
    exact ⟨fun k hk => beq_iff.1 (h1 k hk), fun w hw => beq_iff.1 (h2 w hw), h3, h4,
      fun k hk => beq_iff.1 (h5 k hk)⟩
  have hGen : ∀ k < 46, ∀ x < 693,
      ap (tvTableG UL.toArray (CFSG.KC.Misc.T46.tvGensG UL.toArray)[k]!) x =
        at' 10 (wordM7.nthN GP k) x ∧ at' 10 (wordM7.nthN GP k) x < 693 := by
    intro k hk x hx
    have hk' := hg k hk
    unfold gensOK at hk'
    rw [andB_iff, andB_iff, beq_iff, beq_iff, allN_iff] at hk'
    obtain ⟨hg46, -, hk'⟩ := hk'
    have h0 := hk' 0 (by norm_num)
    simp only [letB_eq] at h0
    rw [show Nat.add k 0 = k from rfl, blt_iff.2 hk] at h0
    change genK UP (wordM7.nthN (gensK UL) k) (wordM7.nthN GP k) = true at h0
    unfold genK at h0
    rw [letB_eq, andB_iff, allN_iff] at h0
    have hx0 := h0.2 x hx
    simp only [letB_eq] at hx0
    rw [andB_iff, blt_iff, beq_iff] at hx0
    obtain ⟨hj, hjx⟩ := hx0
    rw [lenN_eq] at hg46
    have hv : (CFSG.KC.Misc.T46.tvGensG UL.toArray)[k]! = wordM7.nthN (gensK UL) k := by
      rw [arr_get, htv, nthN_eq]
    refine ⟨?_, hj⟩
    unfold ap CFSG.KC.Misc.T46.tvTableG
    rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    simp only
    rw [hv, hux x hx, ← tvK_eq, ← normK_eq, ← hjx]
    unfold CFSG.KC.Misc.T46.uPosG
    rw [getElem!_pos _ _ (by simpa using at'_lt 12 UP _), Array.getElem_ofFn]
    simp only
    rw [hat' _ hj, hnd.idxOf_getElem,
      UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hj (by norm_num))]
  have W : ∀ w : List ℤ, lettersOK 46 w = true → ∀ x < 693,
      ap (wordT 693 (genG UL.toArray) w) x = walkT A w x ∧ walkT A w x < 693 := by
    intro w
    induction w with
    | nil =>
      intro _ x hx
      refine ⟨?_, hx⟩
      rw [wordT, List.foldr_nil]
      exact ap_idT hx (by norm_num)
    | cons z w ih =>
      intro hw x hx
      change andB (andB (Nat.ble 1 z.natAbs) (Nat.ble z.natAbs 46)) (lettersOK 46 w) = true at hw
      rw [andB_iff, andB_iff, ble_iff, ble_iff] at hw
      obtain ⟨⟨hz1, hz2⟩, hw⟩ := hw
      obtain ⟨e, b⟩ := ih hw x hx
      have hk : z.natAbs - 1 < 46 := by omega
      obtain ⟨e2, b2⟩ := hGen (z.natAbs - 1) hk (walkT A w x) b
      have hA := (hpt (walkT A w x) b).1 (z.natAbs - 1) hk
      have hwalk : walkT A (z :: w) x = A (walkT A w x * 46 + (z.natAbs - 1)) := rfl
      rw [ap_wordT_cons _ _ _ _ hx, e, hwalk, hA]
      exact ⟨e2, b2⟩
  unfold CFSG.KC.MiscCoset.T46W.lettersK at hl
  rw [andB_iff, andB_iff, andB_iff, andB_iff, listAnd_iff] at hl
  obtain ⟨hr, ⟨hxw, hxp⟩, hyw, hyp⟩ := hl
  unfold wordsG t46FixAll t46TblEq
  simp only [Bool.and_eq_true, List.all_eq_true, allIn_iff, beq_iff_eq]
  refine ⟨⟨⟨fun r hr' i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩, fun k hk i hi => ?_⟩
  · rw [(W r (hr r hr') i hi).1]
    exact (hpt i hi).2.1 r hr'
  · obtain ⟨e1, b1⟩ := W xp hxp i hi
    obtain ⟨e2, b2⟩ := W xp hxp _ b1
    obtain ⟨e3, -⟩ := W xp hxp _ b2
    have hp3 : powT 693 3 (wordT 693 (genG UL.toArray) xp) =
        compT 693 (wordT 693 (genG UL.toArray) xp) (compT 693 (wordT 693 (genG UL.toArray) xp)
          (compT 693 (wordT 693 (genG UL.toArray) xp) (idT 693))) := rfl
    rw [hp3, ap_compT _ _ hi, ap_compT _ _ hi, ap_compT _ _ hi, ap_idT hi (by norm_num), e1, e2, e3,
      (W xw hxw i hi).1]
    exact (hpt i hi).2.2.1
  · obtain ⟨e1, b1⟩ := W yp hyp i hi
    obtain ⟨e2, -⟩ := W yp hyp _ b1
    have hp2 : powT 693 2 (wordT 693 (genG UL.toArray) yp) =
        compT 693 (wordT 693 (genG UL.toArray) yp)
          (compT 693 (wordT 693 (genG UL.toArray) yp) (idT 693)) := rfl
    rw [hp2, ap_compT _ _ hi, ap_compT _ _ hi, ap_idT hi (by norm_num), e1, e2, (W yw hyw i hi).1]
    exact (hpt i hi).2.2.2.1
  · have e : ((k : ℤ) + 1).natAbs - 1 = k := by omega
    change ap (compT 693 (tvTableG UL.toArray (CFSG.KC.Misc.T46.tvGensG UL.toArray)[((k : ℤ) +
      1).natAbs - 1]!) (tvTableG UL.toArray (CFSG.KC.Misc.T46.tvGensG UL.toArray)[((k : ℤ) +
      1).natAbs - 1]!)) i = i
    rw [e, ap_compT _ _ hi]
    obtain ⟨e1, b1⟩ := hGen k hk i hi
    have h5 := (hpt i hi).2.2.2.2 k hk
    rw [(hpt i hi).1 k hk, (hpt _ b1).1 k hk] at h5
    rw [e1, (hGen k hk _ b1).1]
    exact h5

end CFSG.KC.MiscCoset.T46W

end
