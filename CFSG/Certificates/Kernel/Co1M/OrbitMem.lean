module

public import Certificates.Data.Kernel.VecK
public import Certificates.Data.CFSGNative.HS.Cert
public import Certificates.Data.CFSGNative.Co1.Odd
import CFSG.Certificates.Kernel.VecKOrbit

public section

namespace CFSG.KC.Co1M

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.VecK CFSG.KC.M1F2 CFSG.KC.Co1F2
  CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def orbBsK (n : Nat) (S : Nat → Nat) (w b : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun k => k)
    (fun i ih k => ih (nIf(andB (Nat.blt (Nat.add k (pw2 i)) n)
      (Nat.ble (S (Nat.add k (pw2 i))) w), Nat.add k (pw2 i), k))) b

@[expose] noncomputable def orbMemK (n : Nat) (S : Nat → Nat) (b w : Nat) : Bool :=
  Nat.beq (S (orbBsK n S w b (nat_lit 0))) w

private theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

private theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem orbBsK_succ (n : Nat) (S : Nat → Nat) (w i k : Nat) :
    orbBsK n S w (i + 1) k =
      orbBsK n S w i (if k + 2 ^ i < n ∧ S (k + 2 ^ i) ≤ w then k + 2 ^ i else k) := by
  change orbBsK n S w i (nIf(andB (Nat.blt (Nat.add k (pw2 i)) n)
      (Nat.ble (S (Nat.add k (pw2 i))) w), Nat.add k (pw2 i), k)) = _
  rw [nIf_eq, andB_eq, pw2_eq]
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq]

theorem orbBsK_lt {n : Nat} {S : Nat → Nat} {w : Nat} :
    ∀ i k, k < n → orbBsK n S w i k < n := by
  intro i
  induction i with
  | zero => exact fun k hk => hk
  | succ i ih =>
    intro k hk
    rw [orbBsK_succ]
    apply ih
    split
    · next hc => exact hc.1
    · exact hk

theorem orbBsK_find {n : Nat} {S : Nat → Nat} {w j : Nat}
    (hS : ∀ x y, x < y → y < n → S x < S y) (hj : j < n) (hw : S j = w) :
    ∀ i k, k ≤ j → j < k + 2 ^ i → orbBsK n S w i k = j := by
  intro i
  induction i with
  | zero =>
    intro k h1 h2
    change k = j
    rw [Nat.pow_zero] at h2
    omega
  | succ i ih =>
    intro k h1 h2
    rw [Nat.pow_succ] at h2
    rw [orbBsK_succ]
    by_cases hc : k + 2 ^ i ≤ j
    · have hle : S (k + 2 ^ i) ≤ w := by
        rcases Nat.lt_or_eq_of_le hc with h | h
        · exact hw ▸ Nat.le_of_lt (hS _ _ h hj)
        · rw [h, hw]
      rw [ite_eq_left ⟨by omega, hle⟩]
      exact ih _ hc (by omega)
    · have hn : ¬(k + 2 ^ i < n ∧ S (k + 2 ^ i) ≤ w) := by
        rintro ⟨h3, h4⟩
        have := hS j (k + 2 ^ i) (by omega) h3
        omega
      rw [ite_eq_right hn]
      exact ih _ h1 (by omega)

theorem orbit_twin (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    {P AT BT FO S IP SP : Nat → Nat} (b : Nat)
    (_hA : D.seedA = String.ofList csA) (_hB : D.seedB = String.ofList csB)
    (_hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (_hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (_hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (_horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (_hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (_hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (_hb : Nat.ble D.n (pw2 b) = true) :
    (D.orbit ()).pts.size = D.n ∧ (∀ i < D.n, (D.orbit ()).pts[i]! = lk P (nat_lit 32) i) ∧
      ∀ w, CFSG.Sporadic.Co1.OddNative.inPts (D.orbit ()).pts (posTable D.d (D.orbit ()).pts)
        D.n w = orbMemK D.n (lk S (nat_lit 32)) b w := by
  have hO := VecK.orbit_eq D _hA _hB _hseed _hn _hP0 _horb _hbfs _hsort
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, pw2_eq] at _hn
  have hb : D.n ≤ 2 ^ b := by
    rw [pw2_eq] at _hb
    exact Nat.le_of_ble_eq_true _hb
  have hsz : (D.orbit ()).pts.size = D.n := by rw [hO]; simp
  have hget : ∀ i < D.n, (D.orbit ()).pts[i]! = lk P 32 i := by
    intro i hi
    rw [hO, getElem!_pos _ i (by simpa using hi)]
    simp
  refine ⟨hsz, hget, fun w => ?_⟩
  have hsort := fun h hh => VecK.sortAt_iff.1 (_hsort h hh)
  have hinj := VecK.P_inj_of_sort _hsort
  have hS : ∀ x y, x < y → y < D.n → lk S 32 x < lk S 32 y := by
    intro x y hxy hy
    induction y with
    | zero => omega
    | succ y ih =>
      have hy' := (hsort y (by omega)).2.2.2
      rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with h1 | h1
      · rcases hy' with h2 | h2
        · omega
        · exact (ih h1 (by omega)).trans h2
      · subst h1
        rcases hy' with h2 | h2
        · omega
        · exact h2
  have hin : CFSG.Sporadic.Co1.OddNative.inPts (D.orbit ()).pts (posTable D.d (D.orbit ()).pts)
      D.n w = true ↔ ∃ i < D.n, lk P 32 i = w := by
    unfold CFSG.Sporadic.Co1.OddNative.inPts
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, by rw [← hget _ h1]; exact h2⟩
    · rintro ⟨i, hi, rfl⟩
      have hpos := CFSG.KC.PosTable.posTable_get (d := D.d) (pts := (D.orbit ()).pts)
        (fun j hj => by
          rw [hget j (by omega)]
          exact (VecK.orbAt_iff.1 (_horb j (by omega))).1)
        (fun j hj k hk e => hinj j (by omega) k (by omega)
          (by rwa [hget j (by omega), hget k (by omega)] at e))
        (by omega) (i := i) (by omega)
      rw [← hget i hi, hpos]
      exact ⟨hi, rfl⟩
  have hmem : orbMemK D.n (lk S 32) b w = true ↔ ∃ r < D.n, lk S 32 r = w := by
    unfold orbMemK
    rw [Nat.beq_eq]
    constructor
    · intro h
      exact ⟨_, orbBsK_lt b 0 _hn.1, h⟩
    · rintro ⟨r, hr, rfl⟩
      rw [orbBsK_find hS hr rfl b 0 (Nat.zero_le _) (by omega)]
  have hset : (∃ i < D.n, lk P 32 i = w) ↔ ∃ r < D.n, lk S 32 r = w := by
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨lk IP 32 i, (hsort i hi).1, (hsort i hi).2.1⟩
    · rintro ⟨r, hr, rfl⟩
      have hsurj : ∃ i < D.n, lk IP 32 i = r := by
        refine Classical.byContradiction fun hne => ?_
        have hnd : ((List.range D.n).map fun i => lk IP 32 i).Nodup := by
          rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
          refine List.Pairwise.imp_of_mem (fun {i j} hi hj hij e => ?_) List.nodup_range
          rw [List.mem_range] at hi hj
          apply hij
          apply hinj i hi j hj
          rw [← (hsort i hi).2.1, ← (hsort j hj).2.1, e]
        have hsub : ((List.range D.n).map fun i => lk IP 32 i) ⊆ (List.range D.n).erase r := by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
          rw [List.mem_range] at hi
          rw [List.mem_erase_of_ne (fun e => hne ⟨i, hi, e⟩), List.mem_range]
          exact (hsort i hi).1
        have hlen := List.Nodup.length_le_of_subset hnd hsub
        rw [List.length_map, List.length_range,
          List.length_erase_of_mem (List.mem_range.2 hr), List.length_range] at hlen
        omega
      obtain ⟨i, hi, e⟩ := hsurj
      exact ⟨i, hi, by rw [← (hsort i hi).2.1, e]⟩
  rw [Bool.eq_iff_iff, hin, hmem]
  exact hset

end CFSG.KC.Co1M

end
