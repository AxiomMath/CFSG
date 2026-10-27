module

public import Certificates.Data.Kernel.SporSch.Co1Cen
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.RankThree.PartOne.SPOR.Co1SylowData

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KS.Raw CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier.Native CFSG.RankThree.PartOne.SPOR

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem centreOK_unpack (A B X p : Nat) :
    co1SylowCentreOK (unpack 24 24 A) (unpack 24 24 B) (unpack 24 24 X) (unpack 24 24 p) =
      cenPtK A B X p := by
  have hb : ∀ Y Z, (unpack 24 24 Y == unpack 24 24 Z) = eqK Y Z := fun Y Z => by
    rw [← unpackR_eq_unpack, ← unpackR_eq_unpack]
    exact CFSG.KC.Co1B.beq_unpack Y Z
  have hpow : ∀ e : Nat, pow (unpack 24 24 X) e = unpack 24 24 (powWK X e) := by
    intro e
    induction e with
    | zero =>
      rw [pow, ← unpackR_eq_unpack]
      exact CFSG.KC.Co1B.one_eq
    | succ e ih =>
      have h : powWK X (e + 1) = mulWK (powWK X e) X := CFSG.KC.F2W.strictN_eq _ _
      rw [pow, ih, mul_unpackW, h]
  have hany : (List.range 5).any (fun k => eqK p (powWK X k)) =
      !(CFSG.KC.Enum.allN 5 fun k => !eqK p (powWK X k)) := by
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, MatL.allN_iff]
    simp only [List.mem_range, Bool.not_eq_true', not_forall]
    constructor
    · rintro ⟨k, hk, he⟩
      exact ⟨k, hk, by simp [he]⟩
    · rintro ⟨k, hk, he⟩
      exact ⟨k, hk, by simpa using he⟩
  have hn : ∀ c : Bool, (if c = true then false else true) = !c := fun c => by cases c <;> rfl
  unfold co1SylowCentreOK cenPtK
  simp only [mul_unpackW, hb, hpow, MatL.bAnd_eq, bIf_eq, hn, hany]
  cases eqK (mulWK p A) (mulWK A p) <;> cases eqK (mulWK p B) (mulWK B p) <;>
    cases CFSG.KC.Enum.allN 5 (fun k => !eqK p (powWK X k)) <;> simp

theorem cenK_sound {A B X N : Nat} {P : Nat → Nat} (PAR LAB : Nat → Nat)
    (h : cenK A B X N P = true) :
    CFSG.Sporadic.Th.Native.allIn 0 (bfsTree N P PAR LAB).pts.size (fun i =>
      co1SylowCentreOK (unpack 24 24 A) (unpack 24 24 B) (unpack 24 24 X)
        (bfsTree N P PAR LAB).pts[i]!) = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨k, hk⟩ _
  have hkN : k < N := by simpa [bfsTree] using hk
  have hp : (bfsTree N P PAR LAB).pts[0 + k]! = unpack 24 24 (P k) := by
    rw [Nat.zero_add, getElem!_pos _ k (by simp [bfsTree, hkN])]
    simp [bfsTree]
  have h1 := MatL.allN_iff.1 h k hkN
  rw [MatL.strictB_eq] at h1
  dsimp only
  rw [hp, centreOK_unpack]
  exact h1

end CFSG.KS.SporSch.M24

end
