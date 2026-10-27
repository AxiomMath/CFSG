module

public import Certificates.Data.Kernel.Misc.IdxMul
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.IdxMul

open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.Loop (strictN)
open CFSG.KC.Ord (andB notB)
open CFSG.KC.LQT.P (impB andB_iff notB_iff impB_iff beq_iff)

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem land_one_eq (m p : ℕ) : Nat.land (Nat.shiftRight m p) 1 = if m.testBit p then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight m p) 1 = m / 2 ^ p % 2 := by
    change (m >>> p) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  split <;> rename_i h <;> simp at h <;> omega

theorem bitB_iff (m x : ℕ) : bitB m x = true ↔ m.testBit x = true := by
  unfold bitB
  rw [beq_iff, land_one_eq]
  split <;> simp_all

theorem ndMask_testBit : ∀ (l : List ℕ) (m : ℕ), l.Nodup → (∀ x ∈ l, m.testBit x = false) →
    ∀ x, (ndMask l m).testBit x = (m.testBit x || decide (x ∈ l))
  | [], m, _, _, x => by simp [ndMask]
  | p :: l, m, hnd, hb, x => by
    have hp : m.testBit p = false := hb p (by simp)
    have hb0 : Nat.beq (Nat.land (Nat.shiftRight m p) 1) 0 = true := by
      rw [beq_iff, land_one_eq, hp]
      rfl
    have e : ndMask (p :: l) m = ndMask l (Nat.lor m (Nat.shiftLeft 1 p)) := by
      change Bool.rec (motive := fun _ => ℕ) 0 (ndMask l (Nat.lor m (Nat.shiftLeft 1 p)))
        (Nat.beq (Nat.land (Nat.shiftRight m p) 1) 0) = _
      rw [hb0]
    obtain ⟨hpl, hnd'⟩ := List.nodup_cons.1 hnd
    have bitL : ∀ y, (Nat.lor m (Nat.shiftLeft 1 p)).testBit y = (m.testBit y || decide (p = y)) := by
      intro y
      change (m ||| 1 <<< p).testBit y = _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    rw [e, ndMask_testBit l _ hnd' (fun y hy => by
      rw [bitL, hb y (by simp [hy])]
      simp only [Bool.false_or, decide_eq_false_iff_not]
      rintro rfl
      exact hpl hy) x, bitL]
    simp only [List.mem_cons]
    by_cases h1 : x = p
    · subst h1
      simp
    · have h2 : ¬ p = x := fun h => h1 h.symm
      simp [h1, h2]

theorem ndMask_mem {l : List ℕ} (hnd : l.Nodup) {x : ℕ} (hx : x ∈ l) :
    (ndMask l 0).testBit x = true := by
  rw [ndMask_testBit l 0 hnd (fun y _ => Nat.zero_testBit y) x]
  simp [hx]

theorem mulK_succ {b c d T PL f i j : ℕ} (hj : j ≠ 0) :
    mulK b c d T PL (f + 1) i j =
      stepF b d T (mulK b c d T PL f i (pg c (mask c) PL j / d)) (pg c (mask c) PL j % d) := by
  have hb : Nat.beq j 0 = false := by
    cases h : Nat.beq j 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hj
  change Bool.rec (motive := fun _ => ℕ) (strictN (pg c (mask c) PL j) fun r =>
      strictN (mulK b c d T PL f i (Nat.div r d)) fun x => stepF b d T x (Nat.mod r d)) i
      (Nat.beq j 0) = _
  rw [hb, strictN_eq, strictN_eq]
  rfl

theorem plAt_spec {c d pb PL Par f : ℕ} : ∀ (P : List (List ℤ)) (j0 : ℕ),
    plAt c d pb PL Par f P j0 = true → ∀ k < P.length,
      (P.getD k []).length < f ∧ (∀ l ∈ P.getD k [], 1 ≤ l ∧ l ≤ (d : ℤ)) ∧
      (j0 + k ≠ 0 → pg c (mask c) PL (j0 + k) =
        d * pg pb (mask pb) Par (j0 + k) + (((P.getD k []).getLastD 0).toNat - 1))
  | [], _, _, k, hk => absurd hk (by simp)
  | w :: P, j0, h, k, hk => by
    have h' : andB (andB (andB (Nat.blt w.length f)
        (w.all fun l => decide (1 ≤ l ∧ l ≤ (d : ℤ))))
      (impB (notB (Nat.beq j0 0))
        (Nat.beq (pg c (mask c) PL j0)
          (Nat.add (Nat.mul d (pg pb (mask pb) Par j0)) (Nat.sub (w.getLastD 0).toNat 1)))))
      (plAt c d pb PL Par f P (Nat.succ j0)) = true := h
    rw [andB_iff, andB_iff, andB_iff, impB_iff, notB_iff, Nat.blt_eq, List.all_eq_true] at h'
    obtain ⟨⟨⟨hl, hw⟩, hp⟩, hr⟩ := h'
    cases k with
    | zero =>
      refine ⟨by simpa using hl, fun l hl' => by simpa using hw l (by simpa using hl'), fun hne => ?_⟩
      have := hp (fun h0 => hne (by simpa using Nat.eq_of_beq_eq_true h0))
      simpa using beq_iff.1 this
    | succ k =>
      have := plAt_spec P (Nat.succ j0) hr k (by simpa using hk)
      have e : Nat.succ j0 + k = j0 + (k + 1) := by omega
      rw [e] at this
      simpa using this

end CFSG.KC.Misc.IdxMul

end
