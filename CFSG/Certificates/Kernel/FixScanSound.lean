module

public import Certificates.Data.Kernel.FixScan
public import CFSG.Certificates.Kernel.Co1BMulSound

public section

namespace CFSG.KC.FixScan

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KS.SporSch.VOrb
  CFSG.Sporadic.Co1.OddNative

theorem fixScanK_eq (T : Nat → Nat) (Ms : List Nat) (lo len acc : Nat) :
    fixScanK T Ms lo len acc = countBelow (fun j => allFixK Ms (ptK T (lo + j))) len acc := by
  induction len generalizing acc with
  | zero => rfl
  | succ n ih =>
    change strictN (Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (allFixK Ms (ptK T (Nat.add lo n)))) (fixScanK T Ms lo n) = _
    rw [CFSG.KC.F2W.strictN_eq, ih]
    change _ = countBelow _ n (if allFixK Ms (ptK T (lo + n)) then acc + 1 else acc)
    congr 1
    cases allFixK Ms (ptK T (lo + n)) <;> rfl

theorem allFixK_eq (Ms : List Nat) (x : Nat) :
    allFixK Ms x = (Ms.map (unpackR 24)).all fun Mt => isFixedN Mt x := by
  induction Ms with
  | nil => rfl
  | cons Mt Ms ih =>
    change andB (Nat.beq (vmF 24 Mt x) x) (allFixK Ms x) = _
    rw [ih, List.map_cons, List.all_cons, isFixedN, CFSG.KC.F2W.vecMulN_unpackR]
    cases h : Nat.beq (vmF 24 Mt x) x
    · have := Nat.ne_of_beq_eq_false h
      simp [andB, this]
    · have := Nat.eq_of_beq_eq_true h
      simp [andB, this]

theorem countBelow_congr {p q : Nat → Bool} {n : Nat} (h : ∀ i < n, p i = q i) (acc : Nat) :
    countBelow p n acc = countBelow q n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    change countBelow p n (if p n then acc + 1 else acc) = countBelow q n (if q n then acc + 1 else acc)
    rw [h n (Nat.lt_succ_self n), ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem countBelow_add_acc (p : Nat → Bool) (n acc : Nat) :
    countBelow p n acc = acc + countBelow p n 0 := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    change countBelow p n (if p n then acc + 1 else acc) =
      acc + countBelow p n (if p n then 0 + 1 else 0)
    rw [ih, ih (if p n then 0 + 1 else 0)]
    cases p n <;> simp <;> omega

theorem countBelow_split (p : Nat → Bool) (a b acc : Nat) :
    countBelow p (a + b) acc = countBelow p a (countBelow (fun j => p (a + j)) b acc) := by
  induction b generalizing acc with
  | zero => rfl
  | succ b ih =>
    change countBelow p (a + b) (if p (a + b) then acc + 1 else acc) =
      countBelow p a (countBelow (fun j => p (a + j)) b (if p (a + b) then acc + 1 else acc))
    exact ih _

theorem countBelow_slices {p : Nat → Bool} {L NS : Nat} {C : Nat → Nat} (h0 : C 0 = 0)
    (hs : ∀ s < NS, countBelow (fun j => p (s * L + j)) L (C s) = C (s + 1)) :
    countBelow p (NS * L) 0 = C NS := by
  have key : ∀ s ≤ NS, countBelow p (s * L) 0 = C s := by
    intro s
    induction s with
    | zero =>
      intro _
      rw [Nat.zero_mul, h0]
      rfl
    | succ s ih =>
      intro hs'
      have h1 := hs s (by omega)
      rw [countBelow_add_acc] at h1
      rw [Nat.succ_mul, countBelow_split, countBelow_add_acc, ih (by omega), ← h1, Nat.add_comm]
  exact key NS le_rfl

end CFSG.KC.FixScan

end
