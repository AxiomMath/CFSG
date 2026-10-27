module

public import Certificates.Data.Kernel.Co2R3K
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Co2R3KSnd.OrbLoop
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Co2R3.Snd

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Sporadic.Co2Rank3.Native

theorem band_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem bif_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c
  · exact ⟨fun h' => (by cases h'), fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => (by cases h')⟩

theorem beq_t {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ble_t {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem blt_t {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem beq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [Nat.beq_eq]
  exact h

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem mask12 : CFSG.KS.mask 12 = 4095 := by decide

theorem unpack12_eq (n A : Nat) : unpack n 12 A = Array.ofFn (n := n) fun i => at12 A i.val := by
  show (Array.ofFn (n := n) fun i => pg 12 (CFSG.KS.mask 12) A i.val) = _
  rw [mask12]
  rfl

theorem unpack12_get {n x : Nat} (A : Nat) (hx : x < n) : (unpack n 12 A)[x]! = at12 A x := by
  rw [unpack12_eq, getElem!_pos (Array.ofFn (n := n) fun i => at12 A i.val) x
    (by rw [Array.size_ofFn]; exact hx), Array.getElem_ofFn]

theorem orbKey_eq (m D P V Q y : Nat) :
    orbKey m D P V Q y = key m (at12 D) (at12 P) (at12 V) (at12 Q) y := by
  unfold orbKey key
  rw [nIf_eq]
  by_cases hb : at12 D y = 1
  · rw [if_pos (beq_true hb), if_pos hb]
    rfl
  · rw [if_neg (fun h' => hb (beq_t h')), if_neg hb]
    rfl

private theorem orbPt_spec {n m : Nat} {G : Nat → Nat} {L D P V Q y : Nat}
    (h : orbPtK n m G L D P V Q y = true) :
    1 ≤ at12 D y ∧ (at12 D y = 1 → at12 L y = y ∧ at12 P y = 0 ∧ at12 V y = 0 ∧
      ∀ v < y, at12 Q v < at12 Q y) ∧
    (at12 D y ≠ 1 → at12 V y < m ∧ at12 P y < n ∧ at12 (G (at12 V y)) (at12 P y) = y ∧
      at12 L y = at12 L (at12 P y) ∧ at12 D y = at12 D (at12 P y) + 1 ∧
      at12 Q (at12 P y) < at12 Q y) := by
  unfold orbPtK at h
  obtain ⟨h1, h2⟩ := band_true h
  refine ⟨ble_t h1, fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨e1, h4⟩ := band_true ((bif_true h2).1 (beq_true hd))
    obtain ⟨e2, h5⟩ := band_true h4
    obtain ⟨e3, h6⟩ := band_true h5
    exact ⟨beq_t e1, beq_t e2, beq_t e3, fun v hv => blt_t (allN_iff.1 h6 v hv)⟩
  · obtain ⟨e1, h4⟩ := band_true ((bif_true h2).2 (beq_false hd))
    obtain ⟨e2, h5⟩ := band_true h4
    obtain ⟨e3, h6⟩ := band_true h5
    obtain ⟨e4, h7⟩ := band_true h6
    obtain ⟨e5, e6⟩ := band_true h7
    exact ⟨blt_t e1, blt_t e2, beq_t e3, beq_t e4, beq_t e5, blt_t e6⟩

private theorem orbEdge_spec {n m : Nat} {G : Nat → Nat} {D P V Q k x : Nat}
    (h : orbEdgeK n m G D P V Q k x = true) (hy : at12 (G k) x < n) :
    (at12 D (at12 (G k) x) = 1 → at12 Q (at12 (G k) x) ≤ at12 Q x) ∧
    (at12 D (at12 (G k) x) ≠ 1 → key m (at12 D) (at12 P) (at12 V) (at12 Q) (at12 (G k) x) ≤
      at12 Q x * (m + 1) + k + 1) := by
  unfold orbEdgeK at h
  rw [strictB_eq] at h
  have h1 := (bif_true h).1 (blt_true hy)
  refine ⟨fun hd => ble_t ((bif_true h1).1 (beq_true hd)), fun hd => ?_⟩
  have h2 := ble_t ((bif_true h1).2 (beq_false hd))
  rw [orbKey_eq] at h2
  exact h2

theorem facts_of_orbReplayK {n m : Nat} {G : Nat → Nat} {L D P V O Q : Nat}
    (h : orbReplayK n m G L D P V O Q = true) :
    Facts n m (fun k x => at12 (G k) x) (at12 L) (at12 D) (at12 P) (at12 V) (at12 O)
      (at12 Q) := by
  unfold orbReplayK at h
  obtain ⟨h1, h'⟩ := band_true h
  obtain ⟨h2, h''⟩ := band_true h'
  obtain ⟨h3, h4⟩ := band_true h''
  refine ⟨fun i hi => blt_t (band_true (allN_iff.1 h1 i hi)).1,
    fun i hi => beq_t (band_true (allN_iff.1 h1 i hi)).2,
    fun y hy => (orbPt_spec (allN_iff.1 h2 y hy)).1,
    fun y hy hd => (orbPt_spec (allN_iff.1 h2 y hy)).2.1 hd,
    fun y hy hd => (orbPt_spec (allN_iff.1 h2 y hy)).2.2 hd, fun i hi => ?_,
    fun k hk x hx hy => orbEdge_spec (allN_iff.1 (allN_iff.1 h4 k hk) x hx) hy⟩
  have e := blt_t (allN_iff.1 h3 i (show i < n - 1 by omega))
  rw [orbKey_eq, orbKey_eq] at e
  exact e

theorem orbitSearch_eq_unpack {n m : Nat} {gens : Array (Array Nat)} {G : Nat → Nat}
    {L D P V O Q : Nat} (hgs : gens.size = m) (hG : ∀ k < m, gens[k]! = unpack n 12 (G k))
    (h : orbReplayK n m G L D P V O Q = true) :
    orbitSearch n gens = (unpack n 12 L, unpack n 12 D, unpack n 12 P, unpack n 12 V) := by
  rw [orbitSearch_eq_of_facts hgs (fun k hk x hx => by rw [hG k hk, unpack12_get _ hx])
    (facts_of_orbReplayK h), unpack12_eq, unpack12_eq, unpack12_eq, unpack12_eq]

end CFSG.KC.Co2R3.Snd

end
