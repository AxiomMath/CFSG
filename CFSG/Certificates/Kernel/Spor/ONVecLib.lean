module

public import Certificates.Data.Kernel.Spor.ONK
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
open CFSG.ONSchreier.Native
open CFSG.Sporadic.Th.Native (Table)

private theorem tn_shr (x k i : Nat) :
    (UInt64.ofNat (x >>> k)).toNat.testBit i = (decide (i < 64) && x.testBit (k + i)) := by
  rw [UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

private theorem tn_nat (x i : Nat) : (UInt64.ofNat x).toNat.testBit i = (decide (i < 64) && x.testBit i) := by
  rw [UInt64.toNat_ofNat', Nat.testBit_mod_two_pow]

private theorem u64_ext {a b : UInt64} (h : ∀ i < 64, a.toNat.testBit i = b.toNat.testBit i) : a = b := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · exact h i hi
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.toNat_lt (Nat.pow_le_pow_right (by omega)
      (by omega))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right
      (by omega) (by omega)))]

theorem add_ofV (a b : V) : (ofV a).add (ofV b) = ofV (a.add b) := by
  simp only [W.add, ofV, V.add, W.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply u64_ext <;> intro i hi <;>
    simp only [CFSG.Sporadic.Fi23.Native.addP, CFSG.Sporadic.Fi23.Native.addM, UInt64.toNat_or,
      UInt64.toNat_xor, UInt64.toNat_and, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and,
      tn_nat, Nat.testBit_shiftRight, hi, decide_true, Bool.true_and]

theorem neg_ofV (a : V) : (ofV a).neg = ofV a.neg := rfl

theorem zero_ofV : W.zero = ofV V.zero := rfl

private theorem u64_bit (x : UInt64) {r : Nat} (hr : r < 64) :
    (x >>> r.toUInt64 &&& 1 != 0) = x.toNat.testBit r := by
  have e : (x >>> r.toUInt64 &&& 1).toNat = x.toNat / 2 ^ r % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one, Nat.and_one_is_mod]
    have : (r.toUInt64).toNat % 64 = r := by
      rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : r < 2 ^ 64),
        Nat.mod_eq_of_lt hr]
    rw [this, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 := Nat.mod_lt (x.toNat / 2 ^ r) (by decide : 2 > 0)
  by_cases h : x.toNat / 2 ^ r % 2 = 1
  · have : (x >>> r.toUInt64 &&& 1) ≠ 0 := fun h' => by
      rw [h', UInt64.toNat_zero] at e
      omega
    simp [h, this]
  · have : (x >>> r.toUInt64 &&& 1) = 0 := UInt64.toNat_inj.mp (by rw [e, UInt64.toNat_zero]; omega)
    simp [h, this]

theorem bit_ofV (v : V) {t : Nat} (ht : t < 256) :
    (ofV v).bitP t = v.p.testBit t ∧ (ofV v).bitM t = v.m.testBit t := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 64 ∧ t = 64 * q + r :=
    ⟨t / 64, t % 64, Nat.mod_lt _ (by omega), (Nat.div_add_mod t 64).symm⟩
  have e1 : (64 * q + r) >>> 6 = q := by rw [Nat.shiftRight_eq_div_pow]; omega
  have e2 : (64 * q + r) &&& 63 = r := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 6]; omega
  unfold W.bitP W.bitM W.limbP W.limbM
  rw [e1, e2, u64_bit _ hr, u64_bit _ hr]
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hq with rfl | rfl | rfl | rfl <;>
    simp [ofV, tn_nat, hr, -UInt64.toNat_ofNat']

@[expose] noncomputable def vOf (X : Nat) : V := ⟨vP X, vM X⟩

theorem vP_vmk {p m : Nat} (hp : p < 2 ^ 256) : vP (vmk p m) = p := by
  change (p ||| m <<< 256) &&& mask 256 = p
  rw [PackFld.mask_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < 256
  · simp [hk, show ¬ k ≥ 256 by omega]
  · have : p.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hk, this]

theorem vM_vmk {p m : Nat} (hp : p < 2 ^ 256) : vM (vmk p m) = m := by
  change (p ||| m <<< 256) >>> 256 = m
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have : p.testBit (256 + k) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega)))
  simp [this]

theorem vmk_vP_vM (X : Nat) : vmk (vP X) (vM X) = X := by
  change (X &&& mask 256) ||| (X >>> 256) <<< 256 = X
  rw [PackFld.mask_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  by_cases hk : k < 256
  · simp [hk, show ¬ k ≥ 256 by omega]
  · simp [hk, show k ≥ 256 by omega, show 256 + (k - 256) = k by omega]

theorem vOf_vmk {p m : Nat} (hp : p < 2 ^ 256) : vOf (vmk p m) = ⟨p, m⟩ := by
  rw [vOf, vP_vmk hp, vM_vmk hp]

theorem canon_bits {X : Nat} (h : canon X = true) :
    vP X &&& vM X = 0 ∧ vP X < 2 ^ 154 ∧ vM X < 2 ^ 154 := by
  unfold canon at h
  simp only [PackFld.strictB_eqP, bAnd_iff] at h
  obtain ⟨h0, hp, hm⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, ?_, ?_⟩
  · have := Nat.blt_eq.mp hp
    rwa [PackFld.shl_eq, Nat.one_mul] at this
  · have := Nat.blt_eq.mp hm
    rwa [PackFld.shl_eq, Nat.one_mul] at this

theorem bit_testBit (x j : Nat) : bit x j = x.testBit j := by
  unfold bit
  have e : Nat.land (Nat.shiftRight x j) 1 = x / 2 ^ j % 2 := by
    change (x >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  cases h : decide (x / 2 ^ j % 2 = 1)
  · simp at h
    have : Nat.beq (x / 2 ^ j % 2) 1 = false := by
      cases e2 : Nat.beq (x / 2 ^ j % 2) 1
      · rfl
      · have := Nat.eq_of_beq_eq_true e2
        omega
    exact this
  · simp at h
    rw [h]
    rfl

private theorem u64_zero {a : UInt64} (h : ∀ i < 64, a.toNat.testBit i = false) : a = 0 :=
  u64_ext fun i hi => by rw [h i hi, UInt64.toNat_zero, Nat.zero_testBit]

theorem canon154_vOf {X : Nat} (h : canon X = true) : canon154 (ofV (vOf X)) = true := by
  obtain ⟨h0, hp, hm⟩ := canon_bits h
  have bp : ∀ i, 154 ≤ i → (vP X).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) hi))
  have bm : ∀ i, 154 ≤ i → (vM X).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hi))
  have b0 : ∀ i, ((vP X).testBit i && (vM X).testBit i) = false := fun i => by
    rw [← Nat.testBit_and, h0, Nat.zero_testBit]
  have w : ∀ k, UInt64.ofNat (vP X >>> k) &&& UInt64.ofNat (vM X >>> k) = 0 := fun k =>
    u64_zero fun i hi => by rw [UInt64.toNat_and, Nat.testBit_and, tn_shr, tn_shr]; simp [hi, b0]
  have w0 : UInt64.ofNat (vP X) &&& UInt64.ofNat (vM X) = 0 :=
    u64_zero fun i hi => by rw [UInt64.toNat_and, Nat.testBit_and, tn_nat, tn_nat]; simp [hi, b0]
  have s2 : ∀ Z, (∀ i, 154 ≤ i → Z.testBit i = false) → UInt64.ofNat (Z >>> 128) >>> 26 = 0 :=
    fun Z hZ => u64_zero fun i hi => by
      have : (26 : UInt64).toNat % 64 = 26 := rfl
      rw [UInt64.toNat_shiftRight, this, Nat.testBit_shiftRight, tn_shr, hZ _ (by omega)]
      simp
  have s3 : ∀ Z, (∀ i, 154 ≤ i → Z.testBit i = false) → UInt64.ofNat (Z >>> 192) = 0 :=
    fun Z hZ => u64_zero fun i hi => by rw [tn_shr, hZ _ (by omega)]; simp
  unfold canon154 W.wf
  simp only [ofV, vOf, w, w0, s2 _ bp, s2 _ bm, s3 _ bp, s3 _ bm]
  rfl

private theorem bits_eq_of_ofV {X Y : Nat} (h : ofV (vOf X) = ofV (vOf Y)) {t : Nat}
    (ht : t < 256) : (vP X).testBit t = (vP Y).testBit t ∧ (vM X).testBit t = (vM Y).testBit t := by
  have hx := bit_ofV (vOf X) ht
  have hy := bit_ofV (vOf Y) ht
  rw [h] at hx
  exact ⟨hx.1.symm.trans hy.1, hx.2.symm.trans hy.2⟩

theorem vOf_inj {X Y : Nat} (hX : canon X = true) (hY : canon Y = true)
    (h : ofV (vOf X) = ofV (vOf Y)) : X = Y := by
  obtain ⟨-, hpx, hmx⟩ := canon_bits hX
  obtain ⟨-, hpy, hmy⟩ := canon_bits hY
  have big : ∀ Z, Z < 2 ^ 154 → ∀ i, 154 ≤ i → Z.testBit i = false := fun Z hZ i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hZ (Nat.pow_le_pow_right (by omega) hi))
  have ep : vP X = vP Y := Nat.eq_of_testBit_eq fun i => by
    by_cases hi : i < 154
    · exact (bits_eq_of_ofV h (by omega)).1
    · rw [big _ hpx i (by omega), big _ hpy i (by omega)]
  have em : vM X = vM Y := Nat.eq_of_testBit_eq fun i => by
    by_cases hi : i < 154
    · exact (bits_eq_of_ofV h (by omega)).2
    · rw [big _ hmx i (by omega), big _ hmy i (by omega)]
  rw [← vmk_vP_vM X, ← vmk_vP_vM Y, ep, em]

theorem combW_ofV {Yw : Array W} {Yv : Array V} (r : V) : ∀ {d : Nat}, d ≤ 256 →
    (∀ j < d, Yw[j]! = ofV Yv[j]!) → combW d Yw (ofV r) = ofV (comb d Yv r)
  | 0, _, _ => by
    simp only [combW, comb, Nat.fold_zero]
    rfl
  | d + 1, hd, h => by
    have ih := combW_ofV r (d := d) (by omega) (fun j hj => h j (by omega))
    simp only [combW, comb] at ih ⊢
    rw [Nat.fold_succ, Nat.fold_succ, ih, (bit_ofV r (by omega : d < 256)).1,
      (bit_ofV r (by omega : d < 256)).2, h d (by omega)]
    by_cases h1 : r.p.testBit d = true
    · rw [ite_eq_left h1, ite_eq_left h1, add_ofV]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : r.m.testBit d = true
      · rw [ite_eq_left h2, ite_eq_left h2, W.sub, V.sub, neg_ofV, add_ofV]
      · rw [ite_eq_right h2, ite_eq_right h2]

private theorem nIfE (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem land_one_beq (y : Nat) : Nat.beq (Nat.land y 1) 1 = y.testBit 0 := by
  change Nat.beq (y &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

private theorem mvL_cons (c : Nat) (L : List Nat) (xp xm ap am : Nat) : mvL (c :: L) xp xm ap am =
    if xp.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vP c) (vM c)) (addM ap am (vP c) (vM c))
    else if xm.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vM c) (vP c)) (addM ap am (vM c) (vP c))
    else mvL L (xp >>> 1) (xm >>> 1) ap am := by
  have e : mvL (c :: L) xp xm ap am = strictN (vP c) fun cp => strictN (vM c) fun cm =>
      nIf(Nat.beq (Nat.land xp (nat_lit 1)) (nat_lit 1),
        strictN (addP ap am cp cm) fun ap' => strictN (addM ap am cp cm) fun am' =>
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
        nIf(Nat.beq (Nat.land xm (nat_lit 1)) (nat_lit 1),
          strictN (addP ap am cm cp) fun ap' => strictN (addM ap am cm cp) fun am' =>
            mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap am)) := rfl
  rw [e]
  simp only [PackFld.strictN_eqP, nIfE, land_one_beq]
  rfl

private theorem mvL_comb (L : List Nat) (r : V) : ∀ t j, j + t = L.length → ∀ acc : V,
    acc = Nat.fold j (fun k _ a => if r.p.testBit k then a.add (L.map vOf).toArray[k]!
      else if r.m.testBit k then a.sub (L.map vOf).toArray[k]! else a) V.zero →
    mvL (L.drop j) (r.p >>> j) (r.m >>> j) acc.p acc.m =
      vmk (comb L.length (L.map vOf).toArray r).p (comb L.length (L.map vOf).toArray r).m
  | 0, j, hj, acc, hacc => by
    rw [List.drop_eq_nil_of_le (by omega)]
    have : j = L.length := by omega
    subst this hacc
    rfl
  | t + 1, j, hj, acc, hacc => by
    have hjl : j < L.length := by omega
    have hY : (L.map vOf).toArray[j]! = vOf L[j] := by
      rw [getElem!_pos _ j (by simpa using hjl)]
      simp
    rw [List.drop_eq_getElem_cons hjl, mvL_cons, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      ← Nat.shiftRight_add, ← Nat.shiftRight_add, Nat.add_zero]
    have hfold : ∀ a', a' = (if r.p.testBit j then acc.add (vOf L[j])
        else if r.m.testBit j then acc.sub (vOf L[j]) else acc) →
        a' = Nat.fold (j + 1) (fun k _ a => if r.p.testBit k then a.add (L.map vOf).toArray[k]!
          else if r.m.testBit k then a.sub (L.map vOf).toArray[k]! else a) V.zero := by
      intro a' ha'
      rw [Nat.fold_succ, ← hacc, hY, ha']
    by_cases h1 : r.p.testBit j = true
    · rw [ite_eq_left h1]
      exact mvL_comb L r t (j + 1) (by omega) (acc.add (vOf L[j])) (hfold _ (by rw [ite_eq_left h1]))
    · rw [ite_eq_right h1]
      by_cases h2 : r.m.testBit j = true
      · rw [ite_eq_left h2]
        exact mvL_comb L r t (j + 1) (by omega) (acc.sub (vOf L[j]))
          (hfold _ (by rw [ite_eq_right h1, ite_eq_left h2]))
      · rw [ite_eq_right h2]
        exact mvL_comb L r t (j + 1) (by omega) acc (hfold _ (by rw [ite_eq_right h1, ite_eq_right h2]))

theorem mv_comb (L : List Nat) (X : Nat) :
    mv L X = vmk (comb L.length (L.map vOf).toArray (vOf X)).p
      (comb L.length (L.map vOf).toArray (vOf X)).m := by
  have := mvL_comb L (vOf X) L.length 0 (by omega) V.zero (by rw [Nat.fold_zero])
  rw [List.drop_zero, Nat.shiftRight_zero, Nat.shiftRight_zero] at this
  unfold mv
  rw [PackFld.strictN_eqP, PackFld.strictN_eqP]
  exact this

@[expose] def VB (B : Nat) (v : V) : Prop := ∀ i, B ≤ i → v.p.testBit i = false ∧ v.m.testBit i = false

theorem VB.add {B : Nat} {a b : V} (ha : VB B a) (hb : VB B b) : VB B (a.add b) := fun i hi => by
  simp [V.add, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, (ha i hi).1, (ha i hi).2,
    (hb i hi).1, (hb i hi).2]

theorem VB.neg {B : Nat} {a : V} (ha : VB B a) : VB B a.neg := fun i hi => ⟨(ha i hi).2, (ha i hi).1⟩

theorem VB.zero (B : Nat) : VB B V.zero := fun i _ => by simp [V.zero]

theorem VB.comb {B d : Nat} {Y : Array V} (r : V) (hY : ∀ j < d, VB B Y[j]!) : VB B (comb d Y r) := by
  induction d with
  | zero =>
    simp only [CFSG.F3.Native.comb, Nat.fold_zero]
    exact VB.zero B
  | succ d ih =>
    have ih' := ih (fun j hj => hY j (by omega))
    simp only [CFSG.F3.Native.comb] at ih' ⊢
    rw [Nat.fold_succ]
    by_cases h1 : r.p.testBit d = true
    · rw [ite_eq_left h1]
      exact ih'.add (hY d (by omega))
    · rw [ite_eq_right h1]
      by_cases h2 : r.m.testBit d = true
      · rw [ite_eq_left h2]
        exact ih'.add (hY d (by omega)).neg
      · rw [ite_eq_right h2]
        exact ih'

theorem VB.lt {B : Nat} {a : V} (h : VB B a) : a.p < 2 ^ B ∧ a.m < 2 ^ B :=
  ⟨Nat.lt_pow_two_of_testBit _ fun i hi => (h i hi).1,
    Nat.lt_pow_two_of_testBit _ fun i hi => (h i hi).2⟩

theorem VB.of_lt {B : Nat} {a : V} (hp : a.p < 2 ^ B) (hm : a.m < 2 ^ B) : VB B a := fun i hi =>
  ⟨Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) hi)),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hi))⟩

theorem vB_canon {X : Nat} (h : canon X = true) : VB 154 (vOf X) := by
  obtain ⟨-, hp, hm⟩ := canon_bits h
  exact VB.of_lt hp hm

theorem map_vOf_get {L : List Nat} {j : Nat} (hj : j < L.length) :
    (L.map vOf).toArray[j]! = vOf (L.getD j 0) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem vOf_mv {L : List Nat} (hL : ∀ j < L.length, canon (L.getD j 0) = true) (X : Nat) :
    vOf (mv L X) = comb L.length (L.map vOf).toArray (vOf X) := by
  have hb : VB 256 (comb L.length (L.map vOf).toArray (vOf X)) := VB.comb _ fun j hj => by
    rw [map_vOf_get hj]
    have := (vB_canon (hL j hj))
    exact fun i hi => this i (by omega)
  rw [mv_comb, vOf_vmk hb.lt.1]

theorem mulVecT_vOf {cA : Array W} {LA : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = ofV (vOf (LA.getD j 0)))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (X : Nat) :
    mulVecT cA (ofV (vOf X)) = ofV (vOf (mv LA X)) := by
  obtain ⟨-, hl, hc⟩ := hcA
  rw [vOf_mv (by rw [hl]; exact hCA), hl, mulVecT]
  exact combW_ofV _ (by omega) fun j hj => by rw [map_vOf_get (by omega), hc j hj]

private theorem bIfE (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem sortAt_spec {K SO SOI : Nat → Nat} {n i : Nat} (h : sortAt K SO SOI n i = true) :
    tab SO i < n ∧ tab SOI (tab SO i) = i ∧
      (i + 1 < n → key K (tab SO i) < key K (tab SO (i + 1))) := by
  unfold sortAt at h
  rw [PackFld.strictB_eqP, bAnd_iff, bAnd_iff, bIfE] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hi => ?_⟩
  rw [ite_eq_left (Nat.blt_eq.mpr hi)] at h3
  exact Nat.blt_eq.mp h3

theorem sort_distinct {n : Nat} {K SO SOI : Nat → Nat} (h : ∀ i < n, sortAt K SO SOI n i = true) :
    ∀ i < n, ∀ j < n, key K i = key K j → i = j := by
  have hs := fun i hi => sortAt_spec (h i hi)
  have hinc : ∀ j, j < n → ∀ i, i < j → key K (tab SO i) < key K (tab SO j) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hij
      have h5 := (hs j (by omega)).2.2 hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with h | h
      · exact Nat.lt_trans (ih (by omega) i h) h5
      · subst h
        exact h5
  have hinj : ∀ a < n, ∀ b < n, tab SO a = tab SO b → a = b := fun a ha b hb e => by
    rw [← (hs a ha).2.1, ← (hs b hb).2.1, e]
  have hsurj : ∀ b < n, ∃ i < n, tab SO i = b := by
    intro b hb
    apply Classical.byContradiction
    intro hne
    have hnd : (b :: (List.range n).map (tab SO)).Nodup := by
      rw [List.nodup_cons]
      refine ⟨fun hm => ?_, List.pairwise_map.2 (List.nodup_range.imp_of_mem fun ha hb' hab heq =>
        hab (hinj _ (List.mem_range.1 ha) _ (List.mem_range.1 hb') heq))⟩
      obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
      exact hne ⟨i, List.mem_range.1 hi, e⟩
    have hsub : (b :: (List.range n).map (tab SO)) ⊆ List.range n := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_range.2 hb
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        exact List.mem_range.2 (hs i (List.mem_range.1 hi)).1
    have := hnd.length_le_of_subset hsub
    simp only [List.length_cons, List.length_map, List.length_range] at this
    omega
  intro a ha b hb e
  obtain ⟨ia, hia, rfl⟩ := hsurj a ha
  obtain ⟨ib, hib, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy ia ib with hl | hl | hl
  · exact absurd e (Nat.ne_of_lt (hinc ib hib ia hl))
  · rw [hl]
  · exact absurd e.symm (Nat.ne_of_lt (hinc ia hia ib hl))

theorem ordImg_eq (a s : Nat) : ordImg a s = if a = s then s + 1 else if a < s then s else 0 := by
  unfold ordImg
  rw [nIfE, nIfE]
  by_cases h1 : a = s
  · subst h1
    simp [Nat.beq_refl]
  · have e1 : Nat.beq a s = false := by
      cases e : Nat.beq a s
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h1
    rw [e1, ite_eq_right h1]
    by_cases h2 : a < s
    · rw [Nat.blt_eq.mpr h2, ite_eq_left h2]
      rfl
    · have e2 : Nat.blt a s = false := by
        cases e : Nat.blt a s
        · rfl
        · exact absurd (Nat.blt_eq.mp e) h2
      rw [e2, ite_eq_right h2]
      rfl

theorem ordImg_ne {a s : Nat} (h : ordImg a s ≠ 0) : a ≤ s ∧ s ≤ ordImg a s ∧
    (a = s → ordImg a s = s + 1) ∧ (a < s → ordImg a s = s) := by
  rw [ordImg_eq] at h ⊢
  by_cases h1 : a = s
  · subst h1
    simp
  · rw [ite_eq_right h1] at h ⊢
    by_cases h2 : a < s
    · rw [ite_eq_left h2]
      exact ⟨by omega, by omega, fun e => absurd e h1, fun _ => rfl⟩
    · rw [ite_eq_right h2] at h
      exact absurd rfl h

theorem ordStep_eq (A B : Nat → Nat) (h s : Nat) : ordStep A B h s =
    if h < s then (if ordImg (tab A h) s = 0 then 0 else ordImg (tab B h) (ordImg (tab A h) s))
    else 0 := by
  unfold ordStep
  rw [nIfE, PackFld.strictN_eqP, nIfE]
  by_cases h1 : h < s
  · rw [Nat.blt_eq.mpr h1, ite_eq_left rfl, ite_eq_left h1]
    by_cases h2 : ordImg (tab A h) s = 0
    · rw [h2]
      rfl
    · have e2 : Nat.beq (ordImg (tab A h) s) 0 = false := by
        cases e : Nat.beq (ordImg (tab A h) s) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h2
      rw [e2, ite_eq_right h2]
      rfl
  · have e1 : Nat.blt h s = false := by
      cases e : Nat.blt h s
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h1
    rw [e1, ite_eq_right h1]
    rfl

theorem ordRun_succ (A B : Nat → Nat) : ∀ k lo s, ordRun A B lo (k + 1) s =
    ordStep A B (lo + k) (ordRun A B lo k s)
  | 0, lo, s => by
    change strictN (ordStep A B lo s) (fun s' => s') = _
    rw [PackFld.strictN_eqP]
    rfl
  | k + 1, lo, s => by
    have e : ∀ m, ordRun A B lo (m + 1) s = ordRun A B (lo + 1) m (ordStep A B lo s) := fun m => by
      change strictN (ordStep A B lo s) (fun s' => ordRun A B (Nat.succ lo) m s') = _
      rw [PackFld.strictN_eqP]
    rw [e, e, ordRun_succ A B k (lo + 1), Nat.add_right_comm, Nat.add_assoc]

theorem ordRun_add (A B : Nat → Nat) (lo s a : Nat) : ∀ b,
    ordRun A B lo (a + b) s = ordRun A B (lo + a) b (ordRun A B lo a s)
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, ordRun_succ, ordRun_succ, ordRun_add A B lo s a b, Nat.add_assoc]

theorem ordRun_zero (A B : Nat → Nat) : ∀ k lo, ordRun A B lo k 0 = 0
  | 0, _ => rfl
  | k + 1, lo => by
    rw [ordRun_succ, ordRun_zero A B k lo, ordStep_eq, ite_eq_right (Nat.not_lt_zero _)]

theorem ordRun_facts {A B NX : Nat → Nat} {n SL NS : Nat} (hn : 0 < n) (hNS : NS * SL = n)
    (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true) :
    ordRun A B 0 n 1 = n ∧ ∀ h < n, h < ordRun A B 0 h 1 ∧ ordRun A B 0 h 1 ≤ n ∧
      ordRun A B 0 (h + 1) 1 = ordStep A B h (ordRun A B 0 h 1) ∧ ordStep A B h (ordRun A B 0 h 1) ≠ 0 ∧
      ordRun A B 0 (h + 1) 1 ≤ n := by
  have hsl : ∀ s ≤ NS, ordRun A B 0 (s * SL) 1 = NX s := by
    intro s
    induction s with
    | zero =>
      intro _
      rw [Nat.zero_mul, hX0]
      rfl
    | succ s ih =>
      intro hs
      rw [Nat.succ_mul, ordRun_add, ih (by omega), Nat.zero_add]
      exact Nat.eq_of_beq_eq_true (hord s (by omega))
  have htot : ordRun A B 0 n 1 = n := by rw [← hNS, hsl NS (Nat.le_refl _), hXN, hNS]
  have hnz : ∀ h ≤ n, ordRun A B 0 h 1 ≠ 0 := by
    intro h hh e
    have := ordRun_add A B 0 1 h (n - h)
    rw [Nat.add_sub_cancel' hh, htot, e, ordRun_zero] at this
    omega
  have hmono : ∀ h < n, ordRun A B 0 h 1 ≤ ordRun A B 0 (h + 1) 1 ∧ h < ordRun A B 0 h 1 := by
    intro h hh
    have hz := hnz (h + 1) (by omega)
    rw [ordRun_succ, Nat.zero_add] at hz ⊢
    rw [ordStep_eq] at hz ⊢
    by_cases h1 : h < ordRun A B 0 h 1
    · rw [ite_eq_left h1] at hz ⊢
      by_cases h2 : ordImg (tab A h) (ordRun A B 0 h 1) = 0
      · rw [ite_eq_left h2] at hz
        exact absurd rfl hz
      · rw [ite_eq_right h2] at hz ⊢
        exact ⟨Nat.le_trans (ordImg_ne h2).2.1 (ordImg_ne hz).2.1, h1⟩
    · rw [ite_eq_right h1] at hz
      exact absurd rfl hz
  have hle : ∀ h ≤ n, ordRun A B 0 h 1 ≤ n := by
    intro h hh
    have key : ∀ t, h + t ≤ n → ordRun A B 0 h 1 ≤ ordRun A B 0 (h + t) 1 := by
      intro t
      induction t with
      | zero => intro _; exact Nat.le_refl _
      | succ t ih =>
        intro ht
        exact Nat.le_trans (ih (by omega)) (hmono (h + t) (by omega)).1
    have := key (n - h) (by omega)
    rwa [Nat.add_sub_cancel' hh, htot] at this
  refine ⟨htot, fun h hh => ⟨(hmono h hh).2, hle h (by omega), ?_, ?_, hle (h + 1) (by omega)⟩⟩
  · rw [ordRun_succ, Nat.zero_add]
  · have := hnz (h + 1) (by omega)
    rwa [ordRun_succ, Nat.zero_add] at this

private abbrev BSt := Array W × Std.HashMap W Nat × Table × Table

private def bfsBody (cA cB : Array W) (h : Nat) (s : BSt) : Id (ForInStep BSt) :=
  if h < s.1.size then
    match s.2.1[mulVecT cA s.1[h]!]? with
    | some k =>
      match s.2.1[mulVecT cB s.1[h]!]? with
      | some k1 =>
        pure (ForInStep.yield (s.1, s.2.1, s.2.2.1.push (UInt32.ofNat k),
          s.2.2.2.push (UInt32.ofNat k1)))
      | none =>
        pure (ForInStep.yield (s.1.push (mulVecT cB s.1[h]!),
          s.2.1.insert (mulVecT cB s.1[h]!) s.1.size, s.2.2.1.push (UInt32.ofNat k),
          s.2.2.2.push (UInt32.ofNat s.1.size)))
    | none =>
      match (s.2.1.insert (mulVecT cA s.1[h]!) s.1.size)[mulVecT cB s.1[h]!]? with
      | some k =>
        pure (ForInStep.yield (s.1.push (mulVecT cA s.1[h]!),
          s.2.1.insert (mulVecT cA s.1[h]!) s.1.size, s.2.2.1.push (UInt32.ofNat s.1.size),
          s.2.2.2.push (UInt32.ofNat k)))
      | none =>
        pure (ForInStep.yield ((s.1.push (mulVecT cA s.1[h]!)).push (mulVecT cB s.1[h]!),
          (s.2.1.insert (mulVecT cA s.1[h]!) s.1.size).insert (mulVecT cB s.1[h]!)
            (s.1.push (mulVecT cA s.1[h]!)).size,
          s.2.2.1.push (UInt32.ofNat s.1.size),
          s.2.2.2.push (UInt32.ofNat (s.1.push (mulVecT cA s.1[h]!)).size)))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

private theorem orbitBFS_eq (cA cB : Array W) (v₀ : W) (cap : Nat) : orbitBFS cA cB v₀ cap =
    ⟨(Id.run (forIn (List.range' 0 cap) ((#[v₀], (∅ : Std.HashMap W Nat).insert v₀ 0, #[], #[]) : BSt)
      (bfsBody cA cB))).1,
     (Id.run (forIn (List.range' 0 cap) ((#[v₀], (∅ : Std.HashMap W Nat).insert v₀ 0, #[], #[]) : BSt)
      (bfsBody cA cB))).2.2.1,
     (Id.run (forIn (List.range' 0 cap) ((#[v₀], (∅ : Std.HashMap W Nat).insert v₀ 0, #[], #[]) : BSt)
      (bfsBody cA cB))).2.2.2⟩ := by
  simp only [orbitBFS, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : [:cap].size = cap := by simp [Std.Legacy.Range.size]
  rw [hsz]
  rfl

section Sim

variable (v : Nat → W) (n : Nat)

private def KeysR (c : Nat) (keys : Array W) : Prop := keys.size = c ∧ ∀ k < c, keys[k]! = v k

private def IdxR (c : Nat) (idx : Std.HashMap W Nat) : Prop :=
  (∀ k < c, idx[v k]? = some k) ∧ ∀ y, (∀ k < c, v k ≠ y) → idx[y]? = none

private def TabR (T : Nat → Nat) (h : Nat) (t : Table) : Prop :=
  t.size = h ∧ ∀ i < h, t[i]! = UInt32.ofNat (tab T i)

private def BR (A B : Nat → Nat) (c h : Nat) (s : BSt) : Prop :=
  KeysR v c s.1 ∧ IdxR v c s.2.1 ∧ TabR A h s.2.2.1 ∧ TabR B h s.2.2.2

variable {v n}

private theorem keys_push {c : Nat} {keys : Array W} (hk : KeysR v c keys) : KeysR v (c + 1) (keys.push (v c)) := by
  refine ⟨by rw [Array.size_push, hk.1], fun k hk' => ?_⟩
  rw [getElem!_pos _ k (by rw [Array.size_push, hk.1]; exact hk'), Array.getElem_push]
  by_cases e : k < keys.size
  · rw [dite_eq_left e, ← getElem!_pos keys k e]
    exact hk.2 k (by rw [hk.1] at e; exact e)
  · rw [dite_eq_right e]
    have : k = c := by rw [hk.1] at e; omega
    rw [this]

private theorem idx_insert {c : Nat} {idx : Std.HashMap W Nat} (hi : IdxR v c idx) (hc : c < n)
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

private theorem idx_old {c a : Nat} {idx : Std.HashMap W Nat} (hi : IdxR v c idx) (ha : a < c) :
    idx[v a]? = some a := hi.1 a ha

private theorem idx_new {c : Nat} {idx : Std.HashMap W Nat} (hi : IdxR v c idx) (hc : c < n)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b) : idx[v c]? = none :=
  hi.2 _ fun k hk e => by have := hinj k (by omega) c hc e; omega

private theorem tab_push {T : Nat → Nat} {h : Nat} {t : Table} (ht : TabR T h t) :
    TabR T (h + 1) (t.push (UInt32.ofNat (tab T h))) := by
  refine ⟨by rw [Array.size_push, ht.1], fun i hi => ?_⟩
  rw [getElem!_pos _ i (by rw [Array.size_push, ht.1]; exact hi), Array.getElem_push]
  by_cases e : i < t.size
  · rw [dite_eq_left e, ← getElem!_pos t i e]
    exact ht.2 i (by rw [ht.1] at e; exact e)
  · rw [dite_eq_right e]
    have : i = h := by rw [ht.1] at e; omega
    rw [this]

private theorem body_step {cA cB : Array W} {A B : Nat → Nat} {c h : Nat} {s : BSt}
    (hs : BR v A B c h s) (hhc : h < c)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b)
    (hA : mulVecT cA (v h) = v (tab A h)) (hB : mulVecT cB (v h) = v (tab B h))
    (hAn : tab A h < n) (hBn : tab B h < n) (hord : ordStep A B h c ≠ 0) :
    ∃ s', bfsBody cA cB h s = pure (ForInStep.yield s') ∧ BR v A B (ordStep A B h c) (h + 1) s' := by
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
  unfold bfsBody
  rw [ite_eq_left hsz, hx, hA, hB, hk.1]
  rcases Nat.lt_or_eq_of_le hac with hlt | heq
  ·
    rw [idx_old hi hlt]
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
  ·
    rw [hA1 heq] at hbc hB1 hB2 ⊢
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

private theorem loop_sim {cA cB : Array W} {A B : Nat → Nat}
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b)
    (hA : ∀ h < n, mulVecT cA (v h) = v (tab A h) ∧ tab A h < n)
    (hB : ∀ h < n, mulVecT cB (v h) = v (tab B h) ∧ tab B h < n)
    (hcnt : ∀ h < n, h < ordRun A B 0 h 1 ∧
      ordRun A B 0 (h + 1) 1 = ordStep A B h (ordRun A B 0 h 1) ∧ ordStep A B h (ordRun A B 0 h 1) ≠ 0) :
    ∀ r h (s : BSt), h + r ≤ n → BR v A B (ordRun A B 0 h 1) h s →
      BR v A B (ordRun A B 0 (h + r) 1) (h + r) (Id.run (forIn (List.range' h r) s (bfsBody cA cB)))
  | 0, h, s, _, hs => hs
  | r + 1, h, s, hr, hs => by
    obtain ⟨h1, h2, h3⟩ := hcnt h (by omega)
    obtain ⟨s', e, hs'⟩ := body_step hs h1 hinj (hA h (by omega)).1 (hB h (by omega)).1
      (hA h (by omega)).2 (hB h (by omega)).2 h3
    rw [← h2] at hs'
    have ih := loop_sim hinj hA hB hcnt r (h + 1) s' (by omega) hs'
    rw [List.range'_succ, List.forIn_cons, e, show h + (r + 1) = h + 1 + r by omega]
    exact ih

end Sim

theorem mvAt_spec {K A B : Nat → Nat} {LA LB : List Nat} {n h : Nat}
    (H : mvAt K LA LB A B n h = true) : canon (key K h) = true ∧ tab A h < n ∧ tab B h < n ∧
      key K (tab A h) = mv LA (key K h) ∧ key K (tab B h) = mv LB (key K h) := by
  unfold mvAt at H
  simp only [PackFld.strictB_eqP, bAnd_iff] at H
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  exact ⟨h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem bfs_sim {cA cB : Array W} {root : W} {n SL NS : Nat}
    {K A B SO SOI NX : Nat → Nat} {LA LB : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = ofV (vOf (LA.getD j 0)))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = ofV (vOf (LB.getD j 0)))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hr : root = ofV (vOf (key K 0))) (hn : 0 < n ∧ n < 2 ^ 18)
    (hmv : ∀ h < n, mvAt K LA LB A B n h = true)
    (hNS : NS * SL = n) (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true)
    (hsort : ∀ i < n, sortAt K SO SOI n i = true) :
    (orbitBFS cA cB root n).keys = (Array.ofFn (n := n) fun i => ofV (vOf (key K i.val))) ∧
      natTab (orbitBFS cA cB root n).alpha = (Array.ofFn (n := n) fun i => tab A i.val) ∧
      natTab (orbitBFS cA cB root n).beta = (Array.ofFn (n := n) fun i => tab B i.val) := by
  have hm := fun h hh => mvAt_spec (hmv h hh)
  have hinj : ∀ a < n, ∀ b < n, ofV (vOf (key K a)) = ofV (vOf (key K b)) → a = b :=
    fun a ha b hb e => sort_distinct hsort a ha b hb (vOf_inj (hm a ha).1 (hm b hb).1 e)
  have hA : ∀ h < n, mulVecT cA (ofV (vOf (key K h))) = ofV (vOf (key K (tab A h))) ∧
      tab A h < n :=
    fun h hh => ⟨by rw [mulVecT_vOf hcA hCA, (hm h hh).2.2.2.1], (hm h hh).2.1⟩
  have hB : ∀ h < n, mulVecT cB (ofV (vOf (key K h))) = ofV (vOf (key K (tab B h))) ∧
      tab B h < n :=
    fun h hh => ⟨by rw [mulVecT_vOf hcB hCB, (hm h hh).2.2.2.2], (hm h hh).2.2.1⟩
  obtain ⟨htot, hcnt⟩ := ordRun_facts hn.1 hNS hX0 hXN hord
  have h0 : BR (fun i => ofV (vOf (key K i))) A B (ordRun A B 0 0 1) 0
      ((#[root], (∅ : Std.HashMap W Nat).insert root 0, #[], #[]) : BSt) := by
    refine ⟨⟨rfl, fun k hk => ?_⟩, ⟨fun k hk => ?_, fun y hy => ?_⟩, ⟨rfl, fun i hi => ?_⟩,
      ⟨rfl, fun i hi => ?_⟩⟩
    · have : k = 0 := by change k < 1 at hk; omega
      subst this
      rw [hr]
      rfl
    · have : k = 0 := by change k < 1 at hk; omega
      subst this
      rw [hr]
      simp
    · rw [Std.HashMap.getElem?_insert]
      have : (root == y) = false := by
        rw [beq_eq_false_iff_ne, hr]
        exact hy 0 (by change 0 < 1; omega)
      rw [this]
      simp
    · exact absurd hi (Nat.not_lt_zero _)
    · exact absurd hi (Nat.not_lt_zero _)
  have hfin := loop_sim hinj hA hB (fun h hh => ⟨(hcnt h hh).1, (hcnt h hh).2.2.1,
    (hcnt h hh).2.2.2.1⟩) n 0 _ (by omega) h0
  rw [Nat.zero_add, htot] at hfin
  obtain ⟨hk, -, ha, hb⟩ := hfin
  rw [orbitBFS_eq]
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
  refine ⟨?_, htab A _ (fun h hh => (hA h hh).2) ha, htab B _ (fun h hh => (hB h hh).2) hb⟩
  apply Array.ext
  · simp [hk.1]
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have := hk.2 i hi
    rw [getElem!_pos _ i (by rw [hk.1]; exact hi)] at this
    rw [this, Array.getElem_ofFn]

end CFSG.KS.ON

end
