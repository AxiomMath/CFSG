module

public import Certificates.Data.Kernel.Misc.Lines
public import Certificates.Data.CFSGNative.Fischer.Hyperoval
public import CFSG.Certificates.Kernel.Misc.T46Defs
public import CFSG.Certificates.Kernel.Spor.PK.T46Pk
import CFSG.Certificates.Kernel.Misc.LinesAlg
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

set_option exponentiation.threshold 1000

namespace CFSG.KC.Misc.Lines

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KS.PK CFSG.KC.Misc.Polar CFSG.KC.LQT.P

@[expose] def tvTabsG (U : Array Nat) : Array Table :=
  Array.ofFn (n := 693) fun p => tvTableG U U[p.val]!

@[expose] def perpTabG (U : Array Nat) : Array Flags :=
  Array.ofFn (n := 693) fun x =>
    let T := (tvTabsG U)[x.val]!
    Array.ofFn (n := 693) fun y => ap T y.val == y.val

theorem bitK_eq_testBit (S i : Nat) : bitK S i = S.testBit i := by
  unfold bitK
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e : Nat.land (Nat.shiftRight S i) 1 = S / 2 ^ i % 2 := by
    rw [show Nat.land (Nat.shiftRight S i) 1 = (S >>> i) &&& 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [e, Bool.eq_iff_iff]
  simp

theorem hermR_eq_hermC (c d : Nat) : hermR c d = hermC c d := by
  have h : hermR c d = (List.range 6).foldl
      (fun acc i => Nat.xor acc (f4K (crdK c i) (f4K (crdK d i) (crdK d i)))) 0 := rfl
  rw [h]
  unfold hermC
  simp only [f4K_eq, crdK_eq]
  rfl

theorem nat_beq_eq_false_iff (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · exact Nat.ne_of_beq_eq_false
  · intro h
    cases hh : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem isPt_iff (c : Nat) : isPt c = true ↔ c ≠ 0 ∧ hermC c c = 0 ∧ normC c = c := by
  unfold isPt
  simp only [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, hermR_eq_hermC,
    normK_eq, nat_beq_eq_false_iff]

theorem posK_spec {UL : List Nat} {UP PP : Nat} (h : posK UL UP PP = true) :
    (∀ c ∈ UL, isPt c = true) ∧ ∀ c < 4096,
      (fd 10 PP c < 693 ∧ fd 12 UP (fd 10 PP c) = c) ∨ (fd 10 PP c = 693 ∧ ¬ isPt c = true) := by
  unfold posK at h
  simp only [andB_eq, letB_eq, orB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true,
    allN_lqt_iff, allL_lqt_iff, Nat.blt_eq, Nat.beq_eq, at'_eq, Bool.not_eq_true'] at h
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨h1, fun c hc => ?_⟩
  rcases h3 c hc with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · exact Or.inl ⟨h4, h5⟩
  · exact Or.inr ⟨h4, by rw [h5]; simp⟩

theorem perpK_spec {UP : Nat} {PB : Nat → Nat} (h : ∀ k < 21, perpK UP PB (33 * k) 33 = true) :
    ∀ x < 693, PB x < 2 ^ 693 ∧
      ∀ y < 693, bitK (PB x) y = true ↔ hermC (fd 12 UP y) (fd 12 UP x) = 0 := by
  intro x hx
  have hk : x / 33 < 21 := by omega
  have h1 := h (x / 33) hk
  unfold perpK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (x % 33) (by omega)
  have e : 33 * (x / 33) + x % 33 = x := by omega
  simp only [Nat.add_eq, e, letB_eq, impB_eq, andB_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', allN_lqt_iff, Nat.blt_eq, at'_eq] at h2
  have hxb : Nat.blt x 693 = true := Nat.blt_eq.mpr hx
  rcases h2 with h2 | ⟨h3, h4⟩
  · rw [hxb] at h2
    exact absurd h2 (by simp)
  have e2 : Nat.shiftLeft 1 693 = 2 ^ 693 := Nat.one_shiftLeft 693
  refine ⟨h3.trans_eq e2, fun y hy => ?_⟩
  have h5 := h4 y hy
  rw [hermR_eq_hermC] at h5
  cases hb : bitK (PB x) y
  · rw [hb] at h5
    simp only [notB_eq, Bool.not_eq_true', nat_beq_eq_false_iff] at h5
    simp [h5]
  · rw [hb] at h5
    simp only [Nat.beq_eq] at h5
    simp [h5]

structure Pts (UL : List Nat) (UP PP : Nat) : Prop where
  len : UL.length = 693
  fd12 : ∀ i < 693, fd 12 UP i = UL.getD i 0
  mono : ∀ i j, i < j → j < 693 → UL.getD i 0 < UL.getD j 0
  lt : ∀ i < 693, UL.getD i 0 < 4096
  pt : ∀ i < 693, isPt (UL.getD i 0) = true
  pos : ∀ c < 4096, (fd 10 PP c < 693 ∧ fd 12 UP (fd 10 PP c) = c) ∨
    (fd 10 PP c = 693 ∧ ¬ isPt c = true)

private theorem mono_of_succ {UL : List Nat} (hinc : ∀ i < 692, UL.getD i 0 < UL.getD (i + 1) 0) :
    ∀ i j, i < j → j < 693 → UL.getD i 0 < UL.getD j 0 := by
  intro i j
  induction j with
  | zero => intro hi; omega
  | succ j ih =>
    intro hij hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact Nat.lt_trans (ih h (by omega)) (hinc j (by omega))
    · subst h; exact hinc i (by omega)

theorem Pts.of {UL : List Nat} {UP PP : Nat} (hp : ptsK UL UP = true)
    (hpos : posK UL UP PP = true) : Pts UL UP PP := by
  obtain ⟨hlen, -, hfd, hinc, -⟩ := ptsK_spec hp
  obtain ⟨hall, hpos'⟩ := posK_spec hpos
  refine ⟨hlen, hfd, mono_of_succ hinc, fun i hi => ?_, fun i hi => ?_, hpos'⟩
  · rw [← hfd i hi]
    have := fd_lt 12 UP i
    omega
  · apply hall
    have : UL.getD i 0 = UL[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, hlen ▸ hi]
    rw [this]
    exact List.getElem_mem _

namespace Pts

variable {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP)
include H

theorem getD_inj {i j : Nat} (hi : i < 693) (hj : j < 693) (h : UL.getD i 0 = UL.getD j 0) :
    i = j := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd h (Nat.ne_of_lt (H.mono i j h' hj))
  · exact h'
  · exact absurd h (Nat.ne_of_gt (H.mono j i h' hi))

theorem pos_getD {i : Nat} (hi : i < 693) : fd 10 PP (UL.getD i 0) = i := by
  rcases H.pos _ (H.lt i hi) with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact H.getD_inj h1 hi (by rw [← H.fd12 _ h1]; exact h2)
  · exact absurd (H.pt i hi) h2

theorem eq_of_pos {c y : Nat} (hc : c < 4096) (hy : y < 693) (h : fd 10 PP c = y) :
    c = UL.getD y 0 := by
  rcases H.pos c hc with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [h] at h2
    rw [← h2, H.fd12 y hy]
  · omega

theorem nodup : UL.Nodup := by
  have hl := H.len
  have : UL.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have := H.mono i j hij (by omega)
    simpa [List.getD_eq_getElem?_getD, hi, hj] using this
  exact this.nodup

theorem uPosG_get {c : Nat} (hc : c < 4096) : (uPosG UL.toArray)[c]! = fd 10 PP c := by
  have hl := H.len
  unfold uPosG
  rw [getElem!_pos _ _ (by simpa using hc), Array.getElem_ofFn]
  show UL.toArray.toList.idxOf c = _
  rw [List.toList_toArray]
  rcases H.pos c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hk : fd 10 PP c < UL.length := by omega
    have h3 := H.nodup.idxOf_getElem (fd 10 PP c) hk
    have h4 : UL[fd 10 PP c] = c := by
      rw [List.getElem_eq_getD 0, ← H.fd12 _ h1, h2]
    rw [h4] at h3
    exact h3
  · rw [h1]
    have hn : c ∉ UL := by
      intro hm
      apply h2
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
      have hi' : i < 693 := by omega
      rw [← e]
      have := H.pt i hi'
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [List.idxOf_eq_length hn, H.len]

end Pts

theorem ap_tvTableG (U : Array Nat) (v : Nat) {i : Nat} (hi : i < 693) :
    ap (tvTableG U v) i = (UInt32.ofNat ((uPosG U)[normC (tvC v U[i]!)]!)).toNat := by
  have h1 : (tvTableG U v)[i]! = UInt32.ofNat ((uPosG U)[normC (tvC v U[i]!)]!) := by
    unfold tvTableG
    rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
  unfold ap
  rw [h1]

theorem perpTabG_getElem (U : Array Nat) {x y : Nat} (hx : x < 693) (hy : y < 693) :
    ((perpTabG U)[x]!)[y]! = (ap (tvTableG U U[x]!) y == y) := by
  unfold perpTabG
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  dsimp only
  rw [getElem!_pos _ y (by simpa using hy), Array.getElem_ofFn]
  unfold tvTabsG
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem perpTabG_get {U : Array Nat} {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat}
    (hU : U = UL.toArray) (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) :
    ∀ x < 693, ∀ y < 693, ((perpTabG U)[x]!)[y]! = bitK (PB x) y := by
  subst hU
  have H := Pts.of hp hpos
  intro x hx y hy
  have hbit := (perpK_spec hperp x hx).2 y hy
  rw [H.fd12 y hy, H.fd12 x hx] at hbit
  rw [perpTabG_getElem _ hx hy, ap_tvTableG _ _ hy]
  have hxl : UL.toArray[x]! = UL.getD x 0 := by
    simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hyl : UL.toArray[y]! = UL.getD y 0 := by
    simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [hxl, hyl]
  have hcx := H.lt x hx
  have hcy := H.lt y hy
  obtain ⟨hy0, hyi, hyn⟩ := (isPt_iff _).1 (H.pt y hy)
  set z := normC (tvC (UL.getD x 0) (UL.getD y 0)) with hz
  have hzlt : z < 4096 := normC_lt _
  have hup : (uPosG UL.toArray)[z]! = fd 10 PP z := H.uPosG_get hzlt
  rw [hup]
  have hf : fd 10 PP z < 1024 := fd_lt 10 PP z
  have hv : (UInt32.ofNat (fd 10 PP z)).toNat = fd 10 PP z := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [hv, Bool.eq_iff_iff, hbit, beq_iff_eq]
  rw [← normC_tvC_eq_iff hcy hcx hy0 hyi hyn]
  constructor
  · intro h
    exact H.eq_of_pos hzlt hy h
  · intro h
    rw [← hz] at h
    rw [h]
    exact H.pos_getD hy

theorem normTab_get {c : Nat} (hc : c < 4096) : (normTab ())[c]! = normC c := by
  unfold normTab
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem scaleTab_get (a : Nat) {c : Nat} (hc : c < 4096) : (scaleTab a)[c]! = scaleC a c := by
  unfold scaleTab
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem list_toArray_getElem! (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem ap_tvTabsG_zero {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) {q : Nat} (hq : q < 693) :
    ap ((tvTabsG UL.toArray)[0]!) q =
      fd 10 PP (normC (tvC (fd 12 UP 0) (fd 12 UP q))) := by
  have h0 : (tvTabsG UL.toArray)[0]! = tvTableG UL.toArray UL.toArray[0]! := by
    unfold tvTabsG
    rw [getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  rw [h0, ap_tvTableG _ _ hq, list_toArray_getElem! UL 0, list_toArray_getElem! UL q,
    ← H.fd12 0 (by norm_num), ← H.fd12 q hq, H.uPosG_get (normC_lt _)]
  have hf : fd 10 PP (normC (tvC (fd 12 UP 0) (fd 12 UP q))) < 1024 := fd_lt 10 PP _
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

end CFSG.KC.Misc.Lines

end
