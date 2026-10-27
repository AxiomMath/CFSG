module

public import Certificates.Data.Kernel.Fi24Pl.Defs
public import Certificates.Data.Fi24Rank.PlanesCheck
import CFSG.Certificates.Kernel.Spor.Fi24FixSound
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.Fi24PlS

open CFSG.KC.Enum CFSG.KC.Fi24Pl CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative (commAtN)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem pg_eq (p x : Nat) : pg 9 511 p x = (p >>> (9 * x)) % 512 := by
  change Nat.land (Nat.shiftRight p (Nat.mul 9 x)) 511 = _
  change p >>> (9 * x) &&& (2 ^ 9 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ 9

theorem bp_lt {r : Nat} (hr : r < 6) : bp r < 504 := by
  interval_cases r <;> decide

section Arrays

variable {F : Nat} {A : Array (Array Nat)}

theorem basis_facts (h : basisK F = true) {k x : Nat} (hk : k < 5) (hx : x < 504) :
    aK F k x < 504 ∧ aK F k (aK F k (aK F k x)) = x := by
  have h1 := (bAnd_iff _ _).1 (allN_spec (allN_spec h k hk) x hx)
  exact ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem aPow_lt (h : basisK F = true) {k : Nat} (hk : k < 5) :
    ∀ (d : Nat) {x : Nat}, x < 504 → aPow F k d x < 504
  | 0, _, hx => hx
  | d + 1, _, hx => (basis_facts h hk (aPow_lt h hk d hx)).1

variable (hA : ∀ k < 5, ∀ x < 504, (A[k]!)[x]! = aK F k x)
include hA

theorem powA_get (h : basisK F = true) {k : Nat} (hk : k < 5) :
    ∀ (d : Nat) {x : Nat}, x < 504 → (powA 504 A[k]! d)[x]! = aPow F k d x
  | 0, x, hx => idA_get hx
  | d + 1, x, hx => by
    change (compA 504 A[k]! (powA 504 A[k]! d))[x]! = aK F k (aPow F k d x)
    rw [compA_get hx, powA_get h hk d hx, hA k hk _ (aPow_lt h hk d hx)]

theorem iotaA_get (h : basisK F = true) {i x : Nat} (hx : x < 504) :
    (iotaA 504 A i)[x]! = iotaPt F i x := by
  have l4 := aPow_lt h (k := 4) (by decide) (dig i 4) hx
  have l3 := aPow_lt h (k := 3) (by decide) (dig i 3) l4
  have l2 := aPow_lt h (k := 2) (by decide) (dig i 2) l3
  have l1 := aPow_lt h (k := 1) (by decide) (dig i 1) l2
  unfold iotaA
  rw [compA_get hx, compA_get hx, compA_get hx, compA_get hx,
    powA_get hA h (by decide) _ hx, powA_get hA h (by decide) _ l4,
    powA_get hA h (by decide) _ l3, powA_get hA h (by decide) _ l2,
    powA_get hA h (by decide) _ l1]
  rfl

theorem iotas_get {i : Nat} (hi : i < 243) : (iotas 504 A)[i]! = iotaA 504 A i := by
  unfold iotas
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

end Arrays

variable {n : Nat}

theorem rep_of_cube {a : Array Nat} (hlt : ∀ x < n, a[x]! < n)
    (hc : ∀ x < n, a[a[a[x]!]!]! = x) : Rep n a (permOfArr n a) := by
  have hinj : ∀ i < n, ∀ j < n, a[i]! = a[j]! → i = j := fun i hi j hj e => by
    rw [← hc i hi, ← hc j hj, e]
  have hcd : (∀ i < n, a[i]! < n) ∧ ∀ i < n, ∀ j < n, a[i]! = a[j]! → i = j := ⟨hlt, hinj⟩
  intro x
  rw [permOfArr, dite_eq_left hcd]
  rfl

theorem rep_powA {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    ∀ d : Nat, Rep n (powA n t d) (g ^ d)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | d + 1 => by
    rw [pow_succ']
    exact rep_compA ht (rep_powA ht d)

def Nrm (N : Subgroup (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ y ∈ N, g * y * g⁻¹ ∈ N

theorem Nrm.mul {N : Subgroup (Equiv.Perm (Fin n))} {g h : Equiv.Perm (Fin n)} (hg : Nrm N g)
    (hh : Nrm N h) : Nrm N (g * h) := fun y hy => by
  have e : g * h * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ := by group
  rw [e]
  exact hg _ (hh y hy)

theorem Nrm.pow {N : Subgroup (Equiv.Perm (Fin n))} {g : Equiv.Perm (Fin n)} (hg : Nrm N g) :
    ∀ d : Nat, Nrm N (g ^ d)
  | 0 => fun y hy => by simpa using hy
  | d + 1 => by
    rw [pow_succ']
    exact hg.mul (Nrm.pow hg d)

theorem Nrm.of_gens {N : Subgroup (Equiv.Perm (Fin n))} {S : Set (Equiv.Perm (Fin n))}
    (hN : N ≤ Subgroup.closure S) {g : Equiv.Perm (Fin n)} (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ N) :
    Nrm N g := by
  suffices H : ∀ y ∈ Subgroup.closure S, g * y * g⁻¹ ∈ N from fun y hy => H y (hN hy)
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x z _ _ hx hz =>
    have e : g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact N.mul_mem hx hz
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact N.inv_mem hx

section Main

variable {F : Nat} {A : Array (Array Nat)} {IK V T G MK BT : Nat → Nat} {P : Array (Array Nat)}
  {N : Subgroup (Equiv.Perm (Fin 504))} {Tp Gp : Nat → Equiv.Perm (Fin 504)}

theorem bitK_iff (hinv : invK IK V = true) {i : Nat} (hi : i < 243) {q : Nat}
    {X Y : Equiv.Perm (Fin 504)} (hX : ∀ x : Fin 504, pg 9 511 (IK i) x = (X x : Nat))
    (hY : ∀ x : Fin 504, pg 9 511 q x = (Y x : Nat)) :
    bitK IK V q i = true ↔ ∀ r < 6, ∀ h : bp r < 504,
      ((X * Y * X⁻¹) ⟨bp r, h⟩ : Nat) = (Y ⟨bp r, h⟩ : Nat) := by
  have hv : ∀ r < 6, ∃ hv : pg 9 511 (V i) r < 504, ∀ h : bp r < 504,
      X⁻¹ ⟨bp r, h⟩ = ⟨pg 9 511 (V i) r, hv⟩ := by
    intro r hr
    have h1 := allN_spec hinv i hi
    rw [strictB_eq, strictB_eq] at h1
    have h2 := allN_spec h1 r hr
    rw [strictB_eq] at h2
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    have hlt := Nat.blt_eq.mp h3
    refine ⟨hlt, fun h => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [← hX, Nat.eq_of_beq_eq_true h4]
  unfold bitK
  rw [strictB_eq, strictB_eq]
  constructor
  · intro hb r hr h
    obtain ⟨hvl, hvr⟩ := hv r hr
    have h1 := Nat.eq_of_beq_eq_true (allN_spec hb r hr)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hvr h, ← hX, ← hY, ← hY]
    exact h1
  · intro H
    refine CFSG.KC.BfsPin.allN_intro fun r hr => ?_
    obtain ⟨hvl, hvr⟩ := hv r hr
    have h1 := H r hr (bp_lt hr)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hvr, ← hX, ← hY, ← hY] at h1
    have e : pg 9 511 (IK i) (pg 9 511 q (pg 9 511 (V i) r)) = pg 9 511 q (bp r) := h1
    rw [e]
    exact Nat.beq_refl _

@[expose] def Xp (aP : Nat → Equiv.Perm (Fin 504)) (i : Nat) : Equiv.Perm (Fin 504) :=
  aP 0 ^ dig i 0 * (aP 1 ^ dig i 1 * (aP 2 ^ dig i 2 * (aP 3 ^ dig i 3 * aP 4 ^ dig i 4)))

theorem rep_iotaA {aP : Nat → Equiv.Perm (Fin 504)} (hr : ∀ k < 5, Rep 504 A[k]! (aP k))
    (i : Nat) : Rep 504 (iotaA 504 A i) (Xp aP i) := by
  unfold iotaA Xp
  exact rep_compA (rep_powA (hr 0 (by decide)) _) (rep_compA (rep_powA (hr 1 (by decide)) _)
    (rep_compA (rep_powA (hr 2 (by decide)) _) (rep_compA (rep_powA (hr 3 (by decide)) _)
      (rep_powA (hr 4 (by decide)) _))))

theorem commAtN_iff {p x : Array Nat} {Y X : Equiv.Perm (Fin 504)} (hp : Rep 504 p Y)
    (hx : Rep 504 x X) : commAtN 504 p x = true ↔ Y * X = X * Y := by
  unfold commAtN
  rw [allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun k => Fin.ext ?_
    have h1 := H k k.2
    rw [beq_iff_eq, hx.apply k.2, hp.apply (X _).2, hp.apply k.2, hx.apply (Y _).2] at h1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact h1
  · intro H k hk
    rw [beq_iff_eq, hx.apply hk, hp.apply (X _).2, hp.apply hk, hx.apply (Y _).2]
    have := congrArg (fun g : Equiv.Perm (Fin 504) => (g ⟨k, hk⟩ : Nat)) H
    simpa only [Equiv.Perm.mul_apply] using this

variable (hA : ∀ k < 5, ∀ x < 504, (A[k]!)[x]! = aK F k x) (hbasis : basisK F = true)
  (hiota : ∀ i < 243, iotaK F IK i = true) (hinv : invK IK V = true)
  (hnorm : normK F G T MK = true) (hrow : ∀ t < 4096, rowK IK V T BT t = true)
  (hfin : finalK BT = true)
  (hPs : P.size = 4096) (hPT : ∀ t < 4096, ∀ x < 504, (P[t]!)[x]! = pg 9 511 (T t) x)
  (hTp : ∀ t < 4096, ∀ x : Fin 504, pg 9 511 (T t) x = (Tp t x : Nat))
  (hTmem : ∀ t < 4096, Tp t ∈ N) (hNmem : ∀ y ∈ N, ∃ t < 4096, Tp t = y)
  (hGp : ∀ j < 12, ∀ x : Fin 504, pg 9 511 (G j) x = (Gp j x : Nat))
  (hNgen : N ≤ Subgroup.closure (Gp '' {j | j < 12}))
  (hkeys : ∀ a < 4096, ∀ b < 4096, (∀ r < 6, pg 9 511 (T a) (bp r) = pg 9 511 (T b) (bp r)) →
    a = b)
  (hT0 : ∀ x < 504, pg 9 511 (T 0) x = x)

include hA hbasis in
theorem rep_basis {k : Nat} (hk : k < 5) : Rep 504 A[k]! (permOfArr 504 A[k]!) := by
  refine rep_of_cube (fun x hx => ?_) (fun x hx => ?_)
  · rw [hA k hk x hx]
    exact (basis_facts hbasis hk hx).1
  · have l1 := (basis_facts hbasis hk hx).1
    have l2 := (basis_facts hbasis hk l1).1
    rw [hA k hk x hx, hA k hk _ l1, hA k hk _ l2]
    exact (basis_facts hbasis hk hx).2

include hA hbasis hnorm hTp hTmem hGp hNgen in
theorem nrm_basis {k : Nat} (hk : k < 5) : Nrm N (permOfArr 504 A[k]!) := by
  have ha := rep_basis hA hbasis hk
  refine Nrm.of_gens hNgen ?_
  rintro _ ⟨j, hj, rfl⟩
  have h1 := allN_spec (allN_spec hnorm k hk) j hj
  rw [strictB_eq] at h1
  obtain ⟨hm, h2⟩ := (bAnd_iff _ _).1 h1
  rw [strictB_eq, strictB_eq] at h2
  have hm' := Nat.blt_eq.mp hm
  have e : permOfArr 504 A[k]! * Gp j = Tp (mIdx MK k j) * permOfArr 504 A[k]! := by
    refine Equiv.ext fun x => Fin.ext ?_
    have h3 := Nat.eq_of_beq_eq_true (allN_spec h2 x x.2)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ha.apply (Gp j x).2, ← hGp j hj,
      hA k hk _ (by rw [hGp j hj]; exact (Gp j x).2), h3, ← hTp _ hm',
      ← hA k hk x x.2, ha.apply x.2]
  rw [e, mul_inv_cancel_right]
  exact hTmem _ hm'

include hA hbasis hnorm hTp hTmem hGp hNgen in
theorem nrm_iota (i : Nat) : Nrm N (Xp (fun k => permOfArr 504 A[k]!) i) := by
  unfold Xp
  exact ((nrm_basis hA hbasis hnorm hTp hTmem hGp hNgen (by decide)).pow _).mul
    (((nrm_basis hA hbasis hnorm hTp hTmem hGp hNgen (by decide)).pow _).mul
    (((nrm_basis hA hbasis hnorm hTp hTmem hGp hNgen (by decide)).pow _).mul
    (((nrm_basis hA hbasis hnorm hTp hTmem hGp hNgen (by decide)).pow _).mul
    ((nrm_basis hA hbasis hnorm hTp hTmem hGp hNgen (by decide)).pow _))))

include hA hbasis hiota in
theorem pg_iota {i : Nat} (hi : i < 243) (x : Fin 504) :
    pg 9 511 (IK i) x = (Xp (fun k => permOfArr 504 A[k]!) i x : Nat) := by
  have h1 := hiota i hi
  unfold iotaK at h1
  rw [strictB_eq] at h1
  rw [Nat.eq_of_beq_eq_true (allN_spec h1 x x.2), ← iotaA_get hA hbasis x.2]
  exact (rep_iotaA (fun k hk => rep_basis hA hbasis hk) i).apply x.2

include hA hbasis hiota hinv hnorm hTp hTmem hNmem hGp hNgen hkeys in
theorem comm_iff {t i : Nat} (ht : t < 4096) (hi : i < 243) :
    Tp t * Xp (fun k => permOfArr 504 A[k]!) i = Xp (fun k => permOfArr 504 A[k]!) i * Tp t ↔
      bitK IK V (T t) i = true := by
  set X := Xp (fun k => permOfArr 504 A[k]!) i
  rw [bitK_iff hinv hi (pg_iota hA hbasis hiota hi) (hTp t ht)]
  constructor
  · intro H r _ h
    rw [← H, mul_inv_cancel_right]
  · intro H
    obtain ⟨t', ht', e⟩ := hNmem _ (nrm_iota hA hbasis hnorm hTp hTmem hGp hNgen i _ (hTmem t ht))
    have htt : t' = t := hkeys t' ht' t ht fun r hr => by
      rw [hTp t' ht' ⟨bp r, bp_lt hr⟩, hTp t ht ⟨bp r, bp_lt hr⟩, e]
      exact H r hr (bp_lt hr)
    subst htt
    have e2 : X * Tp t' = Tp t' * X := by
      calc X * Tp t' = X * Tp t' * X⁻¹ * X := by group
        _ = Tp t' * X := by rw [← e]
    exact e2.symm

theorem fld_one (b i : Nat) : fld(b, i, nat_lit 1) = b / 2 ^ i % 2 := by
  change (b >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, beq_iff_eq])

theorem fld_one_eq (b i : Nat) :
    fld(b, i, nat_lit 1) = if Nat.testBit b i = true then 1 else 0 := by
  rw [fld_one, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with h | h <;> simp [h]

theorem countP_finRange (f : Nat → Bool) : ∀ m : Nat,
    (List.finRange m).countP (fun i => f i.val) = ∑ i ∈ Finset.range m, if f i = true then 1 else 0
  | 0 => by simp
  | m + 1 => by
    rw [List.finRange_succ_last, List.countP_append, List.countP_map, Finset.sum_range_succ,
      ← countP_finRange f m]
    simp [Function.comp_def]

theorem sumN_eq (g : Nat → Nat) : ∀ m : Nat, CFSG.KLie.CT.sumN m g = ∑ i ∈ Finset.range m, g i
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ, ← sumN_eq g m]
    exact Nat.add_comm _ _

theorem popK_eq (b : Nat) :
    popK b = (List.finRange 243).countP (fun i => Nat.testBit b i.val) := by
  rw [countP_finRange (fun i => Nat.testBit b i), popK, sumN_eq]
  exact Finset.sum_congr rfl fun i _ => fld_one_eq b i

theorem bits_eq {b c : Nat} (hb : b >>> 243 = 0) (hc : c >>> 243 = 0)
    (h : ∀ i < 243, Nat.testBit b i = Nat.testBit c i) : b = c := by
  have lt : ∀ x : Nat, x >>> 243 = 0 → x < 2 ^ 243 := fun x hx => by
    rw [Nat.shiftRight_eq_div_pow] at hx
    exact (Nat.div_eq_zero_iff_lt (by positivity)).1 hx
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases Nat.lt_or_ge i 243 with hi | hi
  · exact h i hi
  · have p : 2 ^ 243 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt b hb) p),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt c hc) p)]

theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

theorem band_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nblt (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_eq])

theorem nble (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.ble_eq, decide_eq_true_eq])

include hrow in
theorem row_bits {t : Nat} (ht : t < 4096) :
    BT t >>> 243 = 0 ∧ ∀ i < 243, Nat.testBit (BT t) i = bitK IK V (T t) i := by
  have h := hrow t ht
  unfold rowK at h
  rw [strictB_eq, strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi => ?_⟩
  have h3 := Nat.eq_of_beq_eq_true (allN_spec h2 i hi)
  rw [fld_one_eq] at h3
  cases hb : Nat.testBit (BT t) i <;> cases hc : bitK IK V (T t) i <;> rw [hb, hc] at h3 <;>
    revert h3 <;> decide

include hA hbasis hiota hinv hnorm hrow hPs hPT hTp hTmem hNmem hGp hNgen hkeys in
theorem pat_get {t i : Nat} (ht : t < 4096) (hi : i < 243) :
    ((fi24PlRows P (iotas 504 A))[t]!)[i]! = Nat.testBit (BT t) i := by
  have hrP : Rep 504 P[t]! (Tp t) := fun x => (hPT t ht x x.2).trans (hTp t ht x)
  have hrI : Rep 504 (iotas 504 A)[i]! (Xp (fun k => permOfArr 504 A[k]!) i) := by
    rw [iotas_get hA hi]
    exact rep_iotaA (fun k hk => rep_basis hA hbasis hk) i
  have hIs : (iotas 504 A).size = 243 := by simp [iotas]
  unfold fi24PlRows
  rw [getElem!_pos _ t (by rw [Array.size_map, hPs]; exact ht), Array.getElem_map,
    ← getElem!_pos P t (by rw [hPs]; exact ht)]
  unfold fi24PlRow
  rw [getElem!_pos _ i (by rw [Array.size_map, hIs]; exact hi), Array.getElem_map,
    ← getElem!_pos (iotas 504 A) i (by rw [hIs]; exact hi), (row_bits hrow ht).2 i hi]
  exact Bool.eq_iff_iff.mpr ((commAtN_iff hrP hrI).trans
    (comm_iff hA hbasis hiota hinv hnorm hTp hTmem hNmem hGp hNgen hkeys ht hi))

include hTp hkeys hT0 in
theorem tp_eq_one_iff {s : Nat} (hs : s < 4096) : Tp s = 1 ↔ s = 0 := by
  have h0 : Tp 0 = 1 := Equiv.ext fun x => Fin.ext (by rw [← hTp 0 (by decide), hT0 x x.2]; rfl)
  constructor
  · intro h
    exact hkeys s hs 0 (by decide) fun r hr => by
      rw [hTp s hs ⟨bp r, bp_lt hr⟩, hTp 0 (by decide) ⟨bp r, bp_lt hr⟩, h, h0]
  · rintro rfl
    exact h0

include hA hbasis hiota hinv hnorm hrow hfin hPs hPT hTp hTmem hNmem hGp hNgen hkeys hT0 in
theorem planesCheck_of : fi24PlCheck P (fi24PlRows P (iotas 504 A)) (idA 504) = true := by
  set R := fi24PlRows P (iotas 504 A) with hRdef
  have hR : ∀ t < 4096, ∀ i < 243, (R[t]!)[i]! = Nat.testBit (BT t) i := fun t ht i hi =>
    pat_get hA hbasis hiota hinv hnorm hrow hPs hPT hTp hTmem hNmem hGp hNgen hkeys ht hi
  have hrP : ∀ t < 4096, Rep 504 P[t]! (Tp t) := fun t ht x => (hPT t ht x x.2).trans (hTp t ht x)
  have hcnt : ∀ t < 4096, fi24PlCnt R[t]! = popK (BT t) := fun t ht => by
    unfold fi24PlCnt
    rw [popK_eq]
    congr 1
    funext i
    exact hR t ht i i.2
  have hid : ∀ s < 4096, eqA 504 P[s]! (idA 504) = (s == 0) := fun s hs =>
    Bool.eq_iff_iff.mpr (by
      rw [eqA_iff (hrP s hs) rep_idA, tp_eq_one_iff hTp hkeys hT0 hs, beq_iff_eq])
  have hbits : ∀ s < 4096, ∀ t < 4096,
      (allLt 243 fun i => (R[s]!)[i]! == (R[t]!)[i]!) = (BT s == BT t) := fun s hs t ht =>
    Bool.eq_iff_iff.mpr (by
      rw [allLt_iff, beq_iff_eq]
      constructor
      · intro H
        refine bits_eq (row_bits hrow hs).1 (row_bits hrow ht).1 fun i hi => ?_
        have := H i hi
        rwa [hR s hs i hi, hR t ht i hi, beq_iff_eq] at this
      · intro H i hi
        rw [hR s hs i hi, hR t ht i hi, H, beq_self_eq_true])
  have hsame : ∀ t < 4096, fi24PlSame P R (idA 504) R[t]! = sameK BT (BT t) := fun t ht => by
    unfold fi24PlSame
    have e : (fun s : Fin 4096 => eqA 504 P[s.val]! (idA 504) ||
        allLt 243 fun i => (R[s.val]!)[i]! == (R[t]!)[i]!) =
        fun s => (s.val == 0) || (BT s.val == BT t) := by
      funext s
      rw [hid s s.2, hbits s s.2 t ht]
    have e2 := countP_finRange (fun s => (s == 0) || (BT s == BT t)) 4096
    rw [e, e2, sameK, CFSG.KC.Fi24FixS.sumBelow_eq _ _ _ (by decide)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [orB_eq, nbeq, nbeq]
    cases (s == 0 || BT s == BT t) <;> rfl
  unfold fi24PlCheck
  rw [allLt_iff]
  intro t ht
  have hf := allN_spec hfin t ht
  unfold finalAt at hf
  rw [strictB_eq, strictB_eq, orB_eq, orB_eq] at hf
  dsimp only
  rw [hcnt t ht, hsame t ht, hid t ht]
  rw [band_eq, nbeq, nbeq, nblt, nble] at hf
  rw [Bool.or_assoc]
  exact hf

end Main

end CFSG.KC.Fi24PlS

end
