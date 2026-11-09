module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Enum.DefsC
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def letC (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def wordAccC (n w idn : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih (fun T => strictN (icode z) (fun c =>
      pcompC n w (mask w) (letC S SI c) T))) wd

theorem wordK_eq_C (n w idn : Nat) (S SI : Nat → Nat) :
    ∀ wd : List Int, wordK n w (mask w) idn S SI wd = wordAccC n w idn S SI wd
  | [] => rfl
  | z :: wd => by
    have e1 : wordK n w (mask w) idn S SI (z :: wd) =
        strictN (wordK n w (mask w) idn S SI wd) (fun T => strictN (icode z) (fun c =>
          pcomp n w (mask w) (letC S SI c) T)) := rfl
    have e2 : wordAccC n w idn S SI (z :: wd) =
        strictN (wordAccC n w idn S SI wd) (fun T => strictN (icode z) (fun c =>
          pcompC n w (mask w) (letC S SI c) T)) := rfl
    rw [e1, e2, wordK_eq_C n w idn S SI wd]
    simp only [CFSG.KS.PK.pcompC_eq]

@[expose] noncomputable def wordEqC (n w idn : Nat) (S SI : Nat → Nat) (kS : Nat) (wd : List Int)
    (r : Nat) : Bool :=
  bAnd(szOK n w, bAnd(lettersK kS wd, Nat.beq (wordAccC n w idn S SI wd) r))

theorem wordEqK_eq_C (n w idn : Nat) (S SI : Nat → Nat) (kS : Nat) (wd : List Int) (r : Nat) :
    CFSG.KS.Prim.wordEqK n w (mask w) idn S SI kS wd r = wordEqC n w idn S SI kS wd r := by
  unfold CFSG.KS.Prim.wordEqK wordEqC
  rw [wordK_eq_C]

theorem wordEqK_of_word {n w m idn kS r : Nat} {S SI : Nat → Nat} {wd : List Int}
    (hw : wordK n w m idn S SI wd = r) (hs : szOK n w = true) (hl : lettersK kS wd = true) :
    CFSG.KS.Prim.wordEqK n w m idn S SI kS wd r = true := by
  unfold CFSG.KS.Prim.wordEqK
  rw [hs, hl, hw]
  exact Nat.beq_refl r

theorem wordEqK_of_C {n w idn kS r : Nat} {S SI : Nat → Nat} {wd : List Int}
    (h : wordEqC n w idn S SI kS wd r = true) :
    CFSG.KS.Prim.wordEqK n w (mask w) idn S SI kS wd r = true := by
  unfold CFSG.KS.Prim.wordEqK
  rw [wordK_eq_C]
  exact h

end CFSG.KS.Raw

end
