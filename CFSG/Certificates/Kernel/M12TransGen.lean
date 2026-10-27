module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalCheckInputs

public section

namespace CFSG.KC.M12Trans

open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow

@[expose] def r0K (tp tl : Nat → Nat) (lc : Nat → Nat → Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih i p => Bool.rec (motive := fun _ => Nat) (ih (tp i) (lc (tl i) p)) p (Nat.beq i 0)) n

theorem r0CodeAux_eq : ∀ n i p, r0CodeAux n i p = r0K tpar tlet letterCode n i p
  | 0, _, _ => rfl
  | n + 1, i, p => by
    rw [r0CodeAux]
    by_cases hi : i = 0
    · subst hi
      rfl
    · rw [ite_eq_right hi, r0CodeAux_eq n]
      have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
      change _ = Bool.rec (motive := fun _ => Nat) _ p (Nat.beq i 0)
      rw [hb]
      rfl

theorem r0βCodeAux_eq : ∀ n i p, r0βCodeAux n i p = r0K tpar tlet letterCodeβ n i p
  | 0, _, _ => rfl
  | n + 1, i, p => by
    rw [r0βCodeAux]
    by_cases hi : i = 0
    · subst hi
      rfl
    · rw [ite_eq_right hi, r0βCodeAux_eq n]
      have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
      change _ = Bool.rec (motive := fun _ => Nat) _ p (Nat.beq i 0)
      rw [hb]
      rfl

@[expose] def rCodeG (r0 : Nat → Nat → Nat) (i p : Nat) : Nat :=
  wordCode gWord (r0 i (SylowTable.nth 0 gInvCode p))

@[expose] def rβCodeG (r0b : Nat → Nat → Nat) (i p : Nat) : Nat :=
  wordCodeβ gWord (r0b i (SylowTable.nth 0 gβInvCode p))

@[expose] def cosetCheckG (tp tl : Nat → Nat) (ta tw : Nat → Nat → Nat) (r0 : Nat → Nat → Nat) :
    Bool :=
  (List.range 1485).all fun i =>
    (i == 0 || (decide (tp i < i) && (tl i == 1 || tl i == 2))) &&
      [1, 2].all fun l => decide (ta l i < 1485) && decide (tw l i < 64) &&
        (List.range 12).all fun p =>
          r0 i (letterCode l p) == SylowTable.nth 0 (SylowTable.code (tw l i)) (r0 (ta l i) p)

@[expose] def decompCheckG (pp ih : Nat → Nat → Nat) (rc : Nat → Nat) : Bool :=
  (List.range 1485).all fun i => (List.range 64).all fun h =>
    decide (pp i h < 64) && decide (ih i h < 1485) &&
      (List.range 12).all fun p => rc (12 * i + dCode h p) == dCode (pp i h) (rc (12 * ih i h + p))

@[expose] def betaCheckG (ai sg : Nat → Nat) (r0b : Nat → Nat → Nat) (rc : Nat → Nat) : Bool :=
  ((List.range 1485).map sg).Nodup &&
    (List.range 1485).all fun i => decide (ai i < 64) && decide (sg i < 1485) &&
      (List.range 12).all fun p => rβCodeG r0b i p == dCode (ai i) (rc (12 * sg i + p))

@[expose] def quotCheckG (ai sg : Nat → Nat) (pp ih : Nat → Nat → Nat) : Bool :=
  (List.range 1485).all fun i => (List.range 64).all fun h =>
    mIdx (mIdx (invIdx (ai i)) (bIdx (pp i h))) (ai (ih i h)) == pp (sg i) (bIdx h)

@[expose] def FSumG (pp ih : Nat → Nat → Nat) (h k : Nat) : Nat :=
  ((List.range 1485).map fun i => fIdx (pp i h) (pp (ih i h) k)).sum

@[expose] def transferCheckG (pp ih : Nat → Nat → Nat) : Bool :=
  (List.range 64).all fun h => (List.range 64).all fun k =>
    (FSumG pp ih h k + muIdx h + muIdx k + muIdx (mIdx h k)) % 2 == fIdx h k

@[expose] def cIdxG (ai : Nat → Nat) (pp ih : Nat → Nat → Nat) (i h : Nat) : Nat :=
  fIdx (ai i) (invIdx (ai i)) + lam0Idx (pp i h) +
    fIdx (invIdx (ai i)) (bIdx (pp i h)) +
    fIdx (mIdx (invIdx (ai i)) (bIdx (pp i h))) (ai (ih i h))

@[expose] def LamSumG (ai : Nat → Nat) (pp ih : Nat → Nat → Nat) (h : Nat) : Nat :=
  ((List.range 1485).map fun i => cIdxG ai pp ih i h).sum

@[expose] def lambdaCheckG (ai : Nat → Nat) (pp ih : Nat → Nat → Nat) : Bool :=
  (List.range 64).all fun h => (LamSumG ai pp ih h + muIdx h + muIdx (bIdx h)) % 2 == lamIdx h

theorem rCode_eq : rCode = rCodeG (r0CodeAux 1485) := rfl

theorem cosetCheck_eq : cosetCheck = cosetCheckG tpar tlet tact twit (r0CodeAux 1485) := rfl

theorem decompCheck_eq : decompCheck = decompCheckG tp tih (fun k => rCodeArr[k]!) := rfl

theorem betaCheck_eq : betaCheck = betaCheckG taIdx tsig (r0βCodeAux 1485) (fun k => rCodeArr[k]!) :=
  rfl

theorem quotCheck_eq : quotCheck = quotCheckG taIdx tsig tp tih := rfl

theorem transferCheck_eq : transferCheck = transferCheckG tp tih := rfl

theorem lambdaCheck_eq : lambdaCheck = lambdaCheckG taIdx tp tih := rfl

end CFSG.KC.M12Trans

end
