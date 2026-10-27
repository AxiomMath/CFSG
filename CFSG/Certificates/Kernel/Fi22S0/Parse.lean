module

public import Certificates.Data.E27.Fi22S0
public import CFSG.Certificates.Kernel.LyS0.Parse
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.Fi22S0Parse

open CFSG.KD.LyS0 CFSG.Sporadic.Fi22.S0 CFSG.KS.LyS0Parse

theorem listT_spec {f : Nat → Nat} : ∀ {l : List Nat} {k n : Nat}, listT f l k n = true →
    l.length + k = n ∧ ∀ m < l.length, l[m]! = f (k + m)
  | [], k, n, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun m hm => absurd hm (by simp)⟩
  | x :: l, k, n, h => by
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨e1, e2⟩ := listT_spec h2
    refine ⟨by simp only [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ m =>
      rw [List.getElem!_cons_succ, e2 m (by simpa using hm)]
      congr 1
      omega

theorem parseNats_of {f : Nat → Nat} {cs : List Char} {n : Nat} (h : parseOK f cs n = true) :
    (parseNats (String.ofList cs)).size = n ∧
      ∀ m < n, (parseNats (String.ofList cs))[m]! = f m := by
  unfold parseOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := listT_spec h2
  have hp : parseNats (String.ofList cs) = (natsL cs).toArray := parse_ofList h1
  rw [hp]
  refine ⟨by simpa using e1, fun m hm => ?_⟩
  rw [List.getElem!_toArray, e2 m (by omega), Nat.zero_add]

theorem pairsOf_eq {a : Array Nat} {m : Nat} {f : Nat → Nat} (hs : a.size = 2 * m)
    (ha : ∀ k < 2 * m, a[k]! = f k) :
    pairsOf a = Array.ofFn (n := m) fun i => (f (2 * i.val), f (2 * i.val + 1)) := by
  unfold pairsOf
  have hm : a.size / 2 = m := by omega
  apply Array.ext
  · simp [hm]
  · intro i h1 h2
    simp only [Array.getElem_ofFn]
    rw [ha _ (by simp at h2; omega), ha _ (by simp at h2; omega)]

theorem ops_of {f : Nat → Nat} {cs : List Char} (hc : opsStr = String.ofList cs)
    (h : parseOK f cs 1134 = true) :
    ops () = Array.ofFn (n := 567) fun t => (f (2 * t.val), f (2 * t.val + 1)) := by
  obtain ⟨h1, h2⟩ := parseNats_of h
  have e : ops () = pairsOf (parseNats opsStr) := by unfold ops; exact rfl
  rw [e, hc, pairsOf_eq (m := 567) h1 h2]

theorem par_of {f : Nat → Nat} {cs : List Char} (hc : parStr = String.ofList cs)
    (h : parseOK f cs 39366 = true) :
    par () = Array.ofFn (n := 19683) fun i => (f (2 * i.val), f (2 * i.val + 1)) := by
  obtain ⟨h1, h2⟩ := parseNats_of h
  have e : par () = pairsOf (parseNats parStr) := by unfold par; exact rfl
  rw [e, hc, pairsOf_eq (m := 19683) h1 h2]

theorem L_of {f : Nat → Nat} {cs : List Char} (hc : LStr = String.ofList cs)
    (h : parseOK f cs 59049 = true) :
    L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i =>
      f (19683 * j.val + i.val) := by
  obtain ⟨-, h2⟩ := parseNats_of h
  have e : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := nS) fun i =>
      (parseNats LStr)[j.val * nS + i.val]! := by unfold L; exact rfl
  rw [e, hc]
  apply Array.ext
  · simp
  · intro j hj1 hj2
    simp only [Array.getElem_ofFn]
    apply Array.ext
    · simp [nS]
    · intro i hi1 hi2
      simp only [Array.getElem_ofFn]
      have hj : j < 3 := by simpa using hj1
      have hi : i < 19683 := by simpa [nS] using hi1
      rw [h2 _ (by unfold nS; omega)]
      unfold nS
      rw [Nat.mul_comm]

end CFSG.KS.Fi22S0Parse

end
