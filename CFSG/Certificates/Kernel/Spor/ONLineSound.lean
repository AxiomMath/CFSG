module

public import Certificates.Data.Kernel.Spor.ONLineK
public import CFSG.Certificates.Kernel.Spor.ONSplitSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
open CFSG.ONSchreier.Native
open CFSG.Sporadic.Th.Native (Table)

theorem join_ofNat {p : Nat} (hp : p < 2 ^ 256) :
    join (UInt64.ofNat p) (UInt64.ofNat (p >>> 64)) (UInt64.ofNat (p >>> 128))
      (UInt64.ofNat (p >>> 192)) = p := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hb : ∀ k, 256 ≤ k → p.testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) hk))
  simp only [join, Nat.testBit_or, Nat.testBit_shiftLeft, UInt64.toNat_ofNat',
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h1 : i < 64
  · have a1 : ¬ 64 ≤ i := by omega
    have a2 : ¬ 128 ≤ i := by omega
    have a3 : ¬ 192 ≤ i := by omega
    have a4 : i < 256 := by omega
    simp [h1, a1, a2, a3, a4]
  · have a1 : 64 ≤ i := by omega
    by_cases h2 : i < 128
    · have e : 64 + (i - 64) = i := by omega
      have a2 : ¬ 128 ≤ i := by omega
      have a3 : ¬ 192 ≤ i := by omega
      have a4 : i - 64 < 64 := by omega
      have a5 : i < 256 := by omega
      simp [h1, a1, a2, a3, a4, a5, e]
    · have a2 : 128 ≤ i := by omega
      have b1 : ¬ i - 64 < 64 := by omega
      by_cases h3 : i < 192
      · have e : 128 + (i - 128) = i := by omega
        have a3 : ¬ 192 ≤ i := by omega
        have a4 : i - 128 < 64 := by omega
        have a5 : i < 256 := by omega
        simp [h1, a1, a2, a3, a4, a5, b1, e]
      · have a3 : 192 ≤ i := by omega
        have b2 : ¬ i - 128 < 64 := by omega
        by_cases h4 : i < 256
        · have e : 192 + (i - 192) = i := by omega
          have a4 : i - 192 < 64 := by omega
          simp [h1, a1, a2, a3, a4, h4, b1, b2, e]
        · have b3 : ¬ i - 192 < 64 := by omega
          rw [hb i (by omega)]
          simp [h1, b1, b2, b3]

theorem vP_lt (X : Nat) : vP X < 2 ^ 256 := by
  change X &&& mask 256 < 2 ^ 256
  rw [PackFld.mask_eq]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos 256) Nat.one_pos)

theorem toV_wOfK {X : Nat} (h : canon X = true) : (wOfK X).toV = vOf X := by
  obtain ⟨-, -, hm⟩ := canon_bits h
  have hm' : vM X < 2 ^ 256 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  unfold wOfK
  simp only [W.toV, ofV, vOf]
  rw [join_ofNat (vP_lt X), join_ofNat hm']

theorem toV_neg_wOfK {X : Nat} (h : canon X = true) : (wOfK X).neg.toV = ⟨vM X, vP X⟩ := by
  obtain ⟨-, -, hm⟩ := canon_bits h
  have hm' : vM X < 2 ^ 256 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  unfold wOfK
  simp only [W.toV, W.neg, ofV]
  rw [join_ofNat (vP_lt X), join_ofNat hm']

theorem lead1_spec {X L : Nat} (h : lead1 X L = true) :
    L < 154 ∧ (vP X).testBit L = true ∧ ∀ i < L, (vP X).testBit i = false ∧ (vM X).testBit i = false := by
  unfold lead1 at h
  simp only [PackFld.strictB_eqP, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, by rw [← bit_testBit]; exact h2, fun i hi => ?_⟩
  have e := congrArg (fun z => Nat.testBit z i) (Nat.eq_of_beq_eq_true h3)
  change ((vP X ||| vM X) &&& (1 <<< L - 1)).testBit i = Nat.testBit 0 i at e
  rw [Nat.one_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_or,
    Nat.zero_testBit] at e
  simp only [hi, decide_true, Bool.and_true, Bool.or_eq_false_iff] at e
  exact e

theorem find_range {P : Nat → Bool} {L : Nat} (hP : P L = true) (hl : ∀ i < L, P i = false) :
    ∀ n, L < n → (List.range n).find? P = some L
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge L n with h' | h'
    · rw [find_range hP hl n h']
      rfl
    · have e : L = n := by omega
      subst e
      have h0 : (List.range L).find? P = none :=
        List.find?_eq_none.2 fun x hx => by simp [hl x (List.mem_range.1 hx)]
      rw [h0]
      simp [hP]

theorem find_lead {p m L : Nat} (hL : L < 154) (hb : (p.testBit L || m.testBit L) = true)
    (hlo : ∀ i < L, p.testBit i = false ∧ m.testBit i = false) :
    (List.range 154).find? (fun j => p.testBit j || m.testBit j) = some L :=
  find_range (P := fun j => p.testBit j || m.testBit j) hb
    (fun i hi => by simp [(hlo i hi).1, (hlo i hi).2]) 154 hL

theorem W_neg_neg (a : W) : a.neg.neg = a := by
  cases a
  rfl

theorem nuW_of_lead1 {K L Y : Nat} (hc : canon K = true) (hl : lead1 K L = true)
    (hy : Y = K ∨ Y = vneg K) : nuW (wOfK Y) = wOfK K := by
  obtain ⟨hL, hp, hlo⟩ := lead1_spec hl
  obtain ⟨h0, -, -⟩ := canon_bits hc
  have hm : (vM K).testBit L = false := by
    have := congrArg (fun z => Nat.testBit z L) h0
    simp only [Nat.testBit_and, Nat.zero_testBit, hp, Bool.true_and] at this
    exact this
  rcases hy with rfl | rfl
  · simp only [nuW, leadIsTwo, toV_wOfK hc, vOf]
    rw [find_lead hL (by simp [hp]) hlo]
    simp [hm]
  · rw [← wOfK_vneg hc]
    simp only [nuW, leadIsTwo, toV_neg_wOfK hc]
    rw [find_lead (p := vM K) (m := vP K) hL (by simp [hp])
      (fun i hi => ⟨(hlo i hi).2, (hlo i hi).1⟩)]
    simp [hp, W_neg_neg]

theorem pmEq_spec {Z Y : Nat} (h : pmEq Z Y = true) : Y = Z ∨ Y = vneg Z := by
  unfold pmEq at h
  cases e : Nat.beq Z Y
  · rw [e] at h
    exact Or.inr (Nat.eq_of_beq_eq_true h)
  · exact Or.inl (Nat.eq_of_beq_eq_true e).symm

theorem lineAt_spec {KL LP AL BL : Nat → Nat} {LA LB : List Nat} {n h : Nat}
    (H : lineAt KL LP LA LB AL BL n h = true) : canon (key KL h) = true ∧
      lead1 (key KL h) (tab LP h) = true ∧ tab AL h < n ∧ tab BL h < n ∧
      pmEq (key KL (tab AL h)) (mv LA (key KL h)) = true ∧
      pmEq (key KL (tab BL h)) (mv LB (key KL h)) = true := by
  unfold lineAt at H
  simp only [PackFld.strictB_eqP, bAnd_iff] at H
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  exact ⟨h1, h2, Nat.blt_eq.mp h3, Nat.blt_eq.mp h4, h5, h6⟩

theorem piAt_spec {K NEG A B KL AL BL PI : Nat → Nat} {n i : Nat}
    (H : piAt K NEG A B KL AL BL PI n i = true) : tab PI i < n ∧
      pmEq (key KL (tab PI i)) (key K i) = true ∧ tab PI (tab NEG i) = tab PI i ∧
      tab NEG i ≠ i ∧ tab PI (tab A i) = tab AL (tab PI i) ∧ tab PI (tab B i) = tab BL (tab PI i) := by
  unfold piAt at H
  simp only [PackFld.strictB_eqP, bAnd_iff] at H
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  refine ⟨Nat.blt_eq.mp h1, h2, Nat.eq_of_beq_eq_true h3, fun e => ?_, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h6⟩
  have : Nat.beq (tab NEG i) i = true := by rw [e]; exact Nat.beq_refl i
  rw [this] at h4
  exact absurd h4 (by decide)

theorem preAt_spec {PI PRE : Nat → Nat} {N j : Nat} (H : preAt PI PRE N j = true) :
    tab PRE j < N ∧ tab PI (tab PRE j) = j := by
  unfold preAt at H
  simp only [PackFld.strictB_eqP, bAnd_iff] at H
  exact ⟨Nat.blt_eq.mp H.1, Nat.eq_of_beq_eq_true H.2⟩

theorem line_img {cA cB : Array W} {KL LP AL BL : Nat → Nat} {LA LB : List Nat} {n : Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = wOfK (LB.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hl : ∀ h < n, lineAt KL LP LA LB AL BL n h = true) {h : Nat} (hh : h < n) :
    (nuW (mulVecT cA (wOfK (key KL h))) = wOfK (key KL (tab AL h)) ∧ tab AL h < n) ∧
      (nuW (mulVecT cB (wOfK (key KL h))) = wOfK (key KL (tab BL h)) ∧ tab BL h < n) := by
  obtain ⟨c1, -, a1, b1, a2, b2⟩ := lineAt_spec (hl h hh)
  obtain ⟨ca, la, -⟩ := lineAt_spec (hl _ a1)
  obtain ⟨cb, lb, -⟩ := lineAt_spec (hl _ b1)
  refine ⟨⟨?_, a1⟩, ⟨?_, b1⟩⟩
  · rw [mv_sound hcA hCA c1]
    exact nuW_of_lead1 ca la (pmEq_spec a2)
  · rw [mv_sound hcB hCB c1]
    exact nuW_of_lead1 cb lb (pmEq_spec b2)

theorem wOfK_ne_zero {K L : Nat} (hc : canon K = true) (hl : lead1 K L = true) :
    wOfK K ≠ W.zero := by
  obtain ⟨-, hp, -⟩ := lead1_spec hl
  intro e
  have h0 : canon 0 = true := by decide
  have e' : wOfK K = wOfK 0 := by rw [e]; rfl
  have := wOfK_inj hc h0 e'
  subst this
  have z : vP 0 = 0 := by
    change 0 &&& mask 256 = 0
    exact Nat.zero_and _
  rw [z, Nat.zero_testBit] at hp
  exact absurd hp Bool.false_ne_true

theorem parAll_of {n chunks : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    CFSG.Sporadic.Th.Native.parAll n chunks p = true := by
  unfold CFSG.Sporadic.Th.Native.parAll
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  change CFSG.Sporadic.Th.Native.allStep j (chunks + 1) n p = true
  unfold CFSG.Sporadic.Th.Native.allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  have hc : 0 < chunks + 1 := Nat.succ_pos _
  have h1 := (Nat.le_div_iff_mul_le hc).1 (Nat.succ_le_of_lt hk)
  rw [Nat.succ_mul, Nat.mul_comm] at h1
  exact h _ (by omega)

theorem ap_of {t : Table} {T : Nat → Nat} {n : Nat}
    (e : natTab t = Array.ofFn (n := n) fun i => tab T i.val) {i : Nat} (hi : i < n) :
    CFSG.Sporadic.Th.Native.ap t i = tab T i := by
  have hts : t.size = n := by simpa [natTab] using congrArg Array.size e
  have := congrArg (fun x => x[i]!) e
  rw [getElem!_pos _ i (by simp [natTab, hts, hi]), getElem!_pos _ i (by simp [hi])] at this
  simp only [natTab, Array.getElem_map, Array.getElem_ofFn] at this
  unfold CFSG.Sporadic.Th.Native.ap
  rw [getElem!_pos _ i (by rw [hts]; exact hi)]
  exact this

theorem size_of_natTab {t : Table} {T : Nat → Nat} {n : Nat}
    (e : natTab t = Array.ofFn (n := n) fun i => tab T i.val) : t.size = n := by
  simpa [natTab] using congrArg Array.size e

theorem ofFnGet {n x : Nat} {f : Nat → Nat} (hx : x < n) :
    (Array.ofFn (n := n) fun i => f i.val)[x]! = f x := by
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem allIn0_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    CFSG.Sporadic.Th.Native.allIn 0 n p = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  exact h _ (by omega)

theorem slice_pt {F : Nat → Bool} {SL NS : Nat}
    (h : ∀ s < NS, allBlk (Nat.mul s SL) F SL = true) : ∀ i < NS * SL, F i = true := by
  intro i hi
  have hSL : 0 < SL := by
    rcases Nat.eq_zero_or_pos SL with e | e
    · rw [e, Nat.mul_zero] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · exact e
  have hs : i / SL < NS := by
    rw [Nat.div_lt_iff_lt_mul hSL]
    exact hi
  have := allBlk_spec (h (i / SL) hs) (i % SL) (Nat.mod_lt i hSL)
  have e : Nat.add (Nat.mul (i / SL) SL) (i % SL) = i := by
    change i / SL * SL + i % SL = i
    rw [Nat.mul_comm]
    exact Nat.div_add_mod i SL
  rw [e] at this
  exact this

theorem getSet {par : Array Nat} {j i v : Nat} (hj : j < par.size) :
    (par.set! j v)[i]! = if j = i then v else par[i]! := by
  by_cases hi : i < par.size
  · rw [getElem!_pos _ i (by simpa using hi), getElem!_pos par i hi]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds hi]
  · have e : ¬ j = i := by omega
    rw [getElem!_neg _ i (by simpa using hi), getElem!_neg par i hi]
    simp [e]

theorem piPre_eq (n : Nat) (pi : Array Nat) : piPre n pi =
    (List.range' 0 nPts).foldl (fun pre i => pre.set! pi[i]! i) (Array.replicate n 0) := by
  unfold piPre
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one, Nat.sub_zero]

@[expose] def PreInv (n : Nat) (pi : Array Nat) (I : Nat) (pre : Array Nat) : Prop :=
  pre.size = n ∧ ∀ j < n, (∃ i < I, pi[i]! = j) → pre[j]! < I ∧ pi[pre[j]!]! = j

theorem preInv_fold {n : Nat} {pi : Array Nat} (hlt : ∀ i < nPts, pi[i]! < n) :
    ∀ r I (pre : Array Nat), I + r ≤ nPts → PreInv n pi I pre →
      PreInv n pi (I + r) ((List.range' I r).foldl (fun pre i => pre.set! pi[i]! i) pre)
  | 0, I, pre, _, h => h
  | r + 1, I, pre, hr, ⟨hs, hp⟩ => by
    have e : I + (r + 1) = I + 1 + r := by omega
    rw [List.range'_succ, List.foldl_cons, e]
    refine preInv_fold hlt r (I + 1) _ (by omega) ⟨?_, fun j hj hex => ?_⟩
    · simp [hs]
    · have hI : pi[I]! < pre.size := by rw [hs]; exact hlt I (by omega)
      rw [getSet hI]
      by_cases e : pi[I]! = j
      · rw [if_pos e]
        exact ⟨by omega, e⟩
      · rw [if_neg e]
        obtain ⟨i, hi, hij⟩ := hex
        have hi' : i < I := by
          rcases Nat.lt_or_ge i I with h | h
          · exact h
          · have : i = I := by omega
            subst this
            exact absurd hij e
        have := hp j hj ⟨i, hi', hij⟩
        exact ⟨by omega, this.2⟩

theorem piPre_spec {n : Nat} {pi : Array Nat} (hlt : ∀ i < nPts, pi[i]! < n)
    (hsurj : ∀ j < n, ∃ i < nPts, pi[i]! = j) :
    ∀ j < n, (piPre n pi)[j]! < nPts ∧ pi[(piPre n pi)[j]!]! = j := by
  rw [piPre_eq]
  have h0 : PreInv n pi 0 (Array.replicate n 0) :=
    ⟨by simp, fun j _ ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  have := preInv_fold hlt nPts 0 _ (by omega) h0
  rw [Nat.zero_add] at this
  exact fun j hj => this.2 j hj (hsurj j hj)

end CFSG.KS.ON

namespace CFSG.KS.ONLine

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.Th.Native (Table)

abbrev LSt := Array W × Std.HashMap W Nat × Table × Table

def lBody (fA fB : W → W) (h : Nat) (s : LSt) : Id (ForInStep LSt) :=
  if h < s.1.size then
    match s.2.1[fA s.1[h]!]? with
    | some k =>
      match s.2.1[fB s.1[h]!]? with
      | some k1 =>
        pure (ForInStep.yield (s.1, s.2.1, s.2.2.1.push (UInt32.ofNat k),
          s.2.2.2.push (UInt32.ofNat k1)))
      | none =>
        pure (ForInStep.yield (s.1.push (fB s.1[h]!),
          s.2.1.insert (fB s.1[h]!) s.1.size, s.2.2.1.push (UInt32.ofNat k),
          s.2.2.2.push (UInt32.ofNat s.1.size)))
    | none =>
      match (s.2.1.insert (fA s.1[h]!) s.1.size)[fB s.1[h]!]? with
      | some k =>
        pure (ForInStep.yield (s.1.push (fA s.1[h]!),
          s.2.1.insert (fA s.1[h]!) s.1.size, s.2.2.1.push (UInt32.ofNat s.1.size),
          s.2.2.2.push (UInt32.ofNat k)))
      | none =>
        pure (ForInStep.yield ((s.1.push (fA s.1[h]!)).push (fB s.1[h]!),
          (s.2.1.insert (fA s.1[h]!) s.1.size).insert (fB s.1[h]!)
            (s.1.push (fA s.1[h]!)).size,
          s.2.2.1.push (UInt32.ofNat s.1.size),
          s.2.2.2.push (UInt32.ofNat (s.1.push (fA s.1[h]!)).size)))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

def lInit (r : W) : LSt := (#[r], (∅ : Std.HashMap W Nat).insert r 0, #[], #[])

theorem lineBFS_eq (cA cB : Array W) (v₀ : W) (cap : Nat) : lineBFS cA cB v₀ cap =
    ⟨(Id.run (forIn (List.range' 0 cap) (lInit (nuW v₀))
      (lBody (fun x => nuW (mulVecT cA x)) (fun x => nuW (mulVecT cB x))))).1,
     (Id.run (forIn (List.range' 0 cap) (lInit (nuW v₀))
      (lBody (fun x => nuW (mulVecT cA x)) (fun x => nuW (mulVecT cB x))))).2.2.1,
     (Id.run (forIn (List.range' 0 cap) (lInit (nuW v₀))
      (lBody (fun x => nuW (mulVecT cA x)) (fun x => nuW (mulVecT cB x))))).2.2.2⟩ := by
  simp only [lineBFS, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : [:cap].size = cap := by simp [Std.Legacy.Range.size]
  rw [hsz]
  rfl

section Sim

variable (v : Nat → W) (n : Nat)

def KeysR (c : Nat) (keys : Array W) : Prop := keys.size = c ∧ ∀ k < c, keys[k]! = v k

def IdxR (c : Nat) (idx : Std.HashMap W Nat) : Prop :=
  (∀ k < c, idx[v k]? = some k) ∧ ∀ y, (∀ k < c, v k ≠ y) → idx[y]? = none

def TabR (T : Nat → Nat) (h : Nat) (t : Table) : Prop :=
  t.size = h ∧ ∀ i < h, t[i]! = UInt32.ofNat (tab T i)

def BR (A B : Nat → Nat) (c h : Nat) (s : LSt) : Prop :=
  KeysR v c s.1 ∧ IdxR v c s.2.1 ∧ TabR A h s.2.2.1 ∧ TabR B h s.2.2.2

variable {v n}

theorem keys_push {c : Nat} {keys : Array W} (hk : KeysR v c keys) :
    KeysR v (c + 1) (keys.push (v c)) := by
  refine ⟨by rw [Array.size_push, hk.1], fun k hk' => ?_⟩
  rw [getElem!_pos _ k (by rw [Array.size_push, hk.1]; exact hk'), Array.getElem_push]
  by_cases e : k < keys.size
  · rw [dite_eq_left e, ← getElem!_pos keys k e]
    exact hk.2 k (by rw [hk.1] at e; exact e)
  · rw [dite_eq_right e]
    have : k = c := by rw [hk.1] at e; omega
    rw [this]

theorem idx_insert {c : Nat} {idx : Std.HashMap W Nat} (hi : IdxR v c idx) (hc : c < n)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b) : IdxR v (c + 1) (idx.insert (v c) c) := by
  refine ⟨fun k hk => ?_, fun y hy => ?_⟩
  · rw [Std.HashMap.getElem?_insert]
    by_cases e : k = c
    · subst e
      simp
    · have : (v c == v k) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => e (hinj k (by omega) c hc h.symm)
      rw [this]
      exact hi.1 k (by omega)
  · rw [Std.HashMap.getElem?_insert]
    have : (v c == y) = false := by
      rw [beq_eq_false_iff_ne]
      exact hy c (by omega)
    rw [this]
    exact hi.2 y fun k hk => hy k (by omega)

theorem idx_old {c a : Nat} {idx : Std.HashMap W Nat} (hi : IdxR v c idx) (ha : a < c) :
    idx[v a]? = some a := hi.1 a ha

theorem idx_new {c : Nat} {idx : Std.HashMap W Nat} (hi : IdxR v c idx) (hc : c < n)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b) : idx[v c]? = none :=
  hi.2 _ fun k hk e => by have := hinj k (by omega) c hc e; omega

theorem tab_push {T : Nat → Nat} {h : Nat} {t : Table} (ht : TabR T h t) :
    TabR T (h + 1) (t.push (UInt32.ofNat (tab T h))) := by
  refine ⟨by rw [Array.size_push, ht.1], fun i hi => ?_⟩
  rw [getElem!_pos _ i (by rw [Array.size_push, ht.1]; exact hi), Array.getElem_push]
  by_cases e : i < t.size
  · rw [dite_eq_left e, ← getElem!_pos t i e]
    exact ht.2 i (by rw [ht.1] at e; exact e)
  · rw [dite_eq_right e]
    have : i = h := by rw [ht.1] at e; omega
    rw [this]

theorem body_step {fA fB : W → W} {A B : Nat → Nat} {c h : Nat} {s : LSt}
    (hs : BR v A B c h s) (hhc : h < c)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b)
    (hA : fA (v h) = v (tab A h)) (hB : fB (v h) = v (tab B h))
    (hAn : tab A h < n) (hBn : tab B h < n) (hord : ordStep A B h c ≠ 0) :
    ∃ s', lBody fA fB h s = pure (ForInStep.yield s') ∧ BR v A B (ordStep A B h c) (h + 1) s' := by
  obtain ⟨hk, hi, ha, hb⟩ := hs
  have hx : s.1[h]! = v h := hk.2 h hhc
  rw [ordStep_eq, ite_eq_left hhc] at hord ⊢
  have hc1 : ordImg (tab A h) c ≠ 0 := fun e => by rw [ite_eq_left e] at hord; exact hord rfl
  rw [ite_eq_right hc1] at hord ⊢
  obtain ⟨hac, -, hA1, hA2⟩ := ordImg_ne hc1
  obtain ⟨hbc, -, hB1, hB2⟩ := ordImg_ne hord
  have hsz : h < s.1.size := by
    rw [hk.1]
    exact hhc
  unfold lBody
  rw [ite_eq_left hsz, hx, hA, hB, hk.1]
  rcases Nat.lt_or_eq_of_le hac with hlt | heq
  · rw [idx_old hi hlt]
    rw [hA2 hlt] at hbc hB1 hB2 ⊢
    rcases Nat.lt_or_eq_of_le hbc with hlt' | heq'
    · rw [idx_old hi hlt', hB2 hlt']
      exact ⟨_, rfl, hk, hi, tab_push ha, tab_push hb⟩
    · rw [hB1 heq', heq', idx_new hi (by omega) hinj]
      refine ⟨_, rfl, ?_, ?_, tab_push ha, ?_⟩
      · exact keys_push hk
      · exact idx_insert hi (by omega) hinj
      · have := tab_push (T := B) hb
        rw [heq'] at this
        exact this
  · rw [hA1 heq] at hbc hB1 hB2 ⊢
    rw [heq, idx_new hi (by omega) hinj]
    have hi' := idx_insert hi (by omega : c < n) hinj
    rcases Nat.lt_or_eq_of_le hbc with hlt' | heq'
    · rw [idx_old hi' hlt', hB2 hlt']
      refine ⟨_, rfl, keys_push hk, hi', ?_, tab_push hb⟩
      have := tab_push (T := A) ha
      rw [heq] at this
      exact this
    · rw [hB1 heq', heq', idx_new hi' (by omega) hinj]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
      · rw [Array.size_push, hk.1]
        exact keys_push (keys_push hk)
      · rw [Array.size_push, hk.1]
        exact idx_insert hi' (by omega) hinj
      · have := tab_push (T := A) ha
        rw [heq] at this
        exact this
      · have := tab_push (T := B) hb
        rw [heq'] at this
        rw [Array.size_push, hk.1]
        exact this

theorem loop_sim {fA fB : W → W} {A B : Nat → Nat}
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b)
    (hA : ∀ h < n, fA (v h) = v (tab A h) ∧ tab A h < n)
    (hB : ∀ h < n, fB (v h) = v (tab B h) ∧ tab B h < n)
    (hcnt : ∀ h < n, h < ordRun A B 0 h 1 ∧
      ordRun A B 0 (h + 1) 1 = ordStep A B h (ordRun A B 0 h 1) ∧
      ordStep A B h (ordRun A B 0 h 1) ≠ 0) :
    ∀ r h (s : LSt), h + r ≤ n → BR v A B (ordRun A B 0 h 1) h s →
      BR v A B (ordRun A B 0 (h + r) 1) (h + r) (Id.run (forIn (List.range' h r) s (lBody fA fB)))
  | 0, h, s, _, hs => hs
  | r + 1, h, s, hr, hs => by
    obtain ⟨h1, h2, h3⟩ := hcnt h (by omega)
    obtain ⟨s', e, hs'⟩ := body_step hs h1 hinj (hA h (by omega)).1 (hB h (by omega)).1
      (hA h (by omega)).2 (hB h (by omega)).2 h3
    rw [← h2] at hs'
    have ih := loop_sim hinj hA hB hcnt r (h + 1) s' (by omega) hs'
    have e2 : h + (r + 1) = h + 1 + r := by omega
    rw [List.range'_succ, List.forIn_cons, e, e2]
    exact ih

end Sim

theorem line_sim {cA cB : Array W} {root : W} {n SL NS : Nat}
    {KL LP AL BL SO SOI NX : Nat → Nat} {LA LB : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = wOfK (LB.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hr : nuW root = wOfK (key KL 0)) (hn : 0 < n ∧ n < 2 ^ 18)
    (hl : ∀ h < n, lineAt KL LP LA LB AL BL n h = true)
    (hNS : NS * SL = n) (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun AL BL (s * SL) SL (NX s)) (NX (s + 1)) = true)
    (hsort : ∀ i < n, sortAt KL SO SOI n i = true) :
    (lineBFS cA cB root n).keys = (Array.ofFn (n := n) fun i => wOfK (key KL i.val)) ∧
      natTab (lineBFS cA cB root n).alpha = (Array.ofFn (n := n) fun i => tab AL i.val) ∧
      natTab (lineBFS cA cB root n).beta = (Array.ofFn (n := n) fun i => tab BL i.val) := by
  have hm := fun h hh => lineAt_spec (hl h hh)
  have hinj : ∀ a < n, ∀ b < n, wOfK (key KL a) = wOfK (key KL b) → a = b :=
    fun a ha b hb e => sort_distinct hsort a ha b hb (wOfK_inj (hm a ha).1 (hm b hb).1 e)
  have hA : ∀ h < n, nuW (mulVecT cA (wOfK (key KL h))) = wOfK (key KL (tab AL h)) ∧
      tab AL h < n := fun h hh => (line_img hcA hcB hCA hCB hl hh).1
  have hB : ∀ h < n, nuW (mulVecT cB (wOfK (key KL h))) = wOfK (key KL (tab BL h)) ∧
      tab BL h < n := fun h hh => (line_img hcA hcB hCA hCB hl hh).2
  obtain ⟨htot, hcnt⟩ := ordRun_facts hn.1 hNS hX0 hXN hord
  have h0 : BR (fun i => wOfK (key KL i)) AL BL (ordRun AL BL 0 0 1) 0 (lInit (nuW root)) := by
    refine ⟨⟨rfl, fun k hk => ?_⟩, ⟨fun k hk => ?_, fun y hy => ?_⟩, ⟨rfl, fun i hi => ?_⟩,
      ⟨rfl, fun i hi => ?_⟩⟩
    · have : k = 0 := by change k < 1 at hk; omega
      subst this
      change (#[nuW root])[0]! = wOfK (key KL 0)
      rw [← hr]
      rfl
    · have : k = 0 := by change k < 1 at hk; omega
      subst this
      change ((∅ : Std.HashMap W Nat).insert (nuW root) 0)[wOfK (key KL 0)]? = some 0
      rw [← hr]
      simp
    · simp only [lInit]
      rw [Std.HashMap.getElem?_insert]
      have : (nuW root == y) = false := by
        rw [beq_eq_false_iff_ne, hr]
        exact hy 0 (by change 0 < 1; omega)
      rw [this]
      simp
    · exact absurd hi (Nat.not_lt_zero _)
    · exact absurd hi (Nat.not_lt_zero _)
  have hfin := loop_sim (fA := fun x => nuW (mulVecT cA x)) (fB := fun x => nuW (mulVecT cB x))
    hinj hA hB (fun h hh => ⟨(hcnt h hh).1, (hcnt h hh).2.2.1, (hcnt h hh).2.2.2.1⟩) n 0 _
    (by omega) h0
  rw [Nat.zero_add, htot] at hfin
  obtain ⟨hk, -, ha, hb⟩ := hfin
  rw [lineBFS_eq]
  have htab : ∀ (T : Nat → Nat) (t : Table), (∀ i < n, tab T i < n) → TabR T n t →
      natTab t = (Array.ofFn (n := n) fun i => tab T i.val) := fun T t hT ht => by
    apply Array.ext
    · simp [natTab, ht.1]
    · intro i h1 h2
      have hi : i < n := by simpa using h2
      have := ht.2 i hi
      rw [getElem!_pos t i (by rw [ht.1]; exact hi)] at this
      simp only [natTab, Array.getElem_map, Array.getElem_ofFn, this]
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := hT i hi; omega)]
  refine ⟨?_, htab AL _ (fun h hh => (hA h hh).2) ha, htab BL _ (fun h hh => (hB h hh).2) hb⟩
  apply Array.ext
  · simp [hk.1]
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have := hk.2 i hi
    rw [getElem!_pos _ i (by rw [hk.1]; exact hi)] at this
    rw [this, Array.getElem_ofFn]

end CFSG.KS.ONLine

end
