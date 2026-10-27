module

public import Certificates.Data.Kernel.Misc.ChainTailQ
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.BfsPin (PP)

theorem commB_false {n w X p q z : ℕ} (hX : PP n w X) (hz : z < n)
    (h : cptK w (mask w) X p q z = false) :
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) p q) X)
      (pcomp n w (mask w) X (pcomp n w (mask w) p q)) = false := by
  have hn := hX.lt32
  cases hb : Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) p q) X)
      (pcomp n w (mask w) X (pcomp n w (mask w) p q))
  · rfl
  · have e : pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) p q) X) z =
        pg w (mask w) (pcomp n w (mask w) X (pcomp n w (mask w) p q)) z := by
      rw [Nat.eq_of_beq_eq_true hb]
    rw [PF.pg_pcomp hn hz, PF.pg_pcomp hn (hX.2.1 z hz), PF.pg_pcomp hn hz, PF.pg_pcomp hn hz] at e
    have h' : cptK w (mask w) X p q z = true := by
      unfold cptK
      rw [e, Nat.beq_refl]
    rw [h] at h'
    exact absurd h' Bool.false_ne_true

theorem ptailK_of_ptailQ {n w : ℕ} {LR TR : ℕ → ℕ} {BP X z1 z2 NE : ℕ} {XP EP : ℕ → ℕ}
    (hX : PP n w X) (h1 : z1 < n) (h2 : z2 < n) :
    ∀ fuel i ACC, ptailQ n w LR TR X z1 z2 NE EP fuel i ACC = true →
      ptailK n w LR TR BP X XP [] NE EP (fuel + 1) i ACC = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i ACC hQ
    have e : ptailQ n w LR TR X z1 z2 NE EP 0 i ACC = strictB (LR i) fun R => allN (rcnt R) fun k =>
        strictB (TR (Nat.add (roff n (Nat.mul n w) R) k)) fun t =>
          Bool.rec (motive := fun _ => Bool) true
            (Bool.rec (motive := fun _ => Bool) true
              (strictB (pcomp n w (mask w) ACC t) fun P =>
                !(Nat.beq (pcomp n w (mask w) P X) (pcomp n w (mask w) X P)) ||
                  CFSG.KC.LQT.P.anyN NE fun e => Nat.beq P (EP e))
              (cptK w (mask w) X ACC t z2))
            (cptK w (mask w) X ACC t z1) := rfl
    have e' : ptailK n w LR TR BP X XP [] NE EP (0 + 1) i ACC = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP [] i ACC (rpt w (mask w) R k)) ||
          ptailK n w LR TR BP X XP [] NE EP 0 (i + 1)
            (pcomp n w (mask w) ACC (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    rw [e, Orb.strictB_eq] at hQ
    rw [e', Orb.strictB_eq, Orb.allN_iff]
    intro k hk
    have hq := Orb.allN_iff.1 hQ k hk
    rw [Orb.strictB_eq] at hq
    have hr : relOKK w (mask w) BP XP [] i ACC (rpt w (mask w) (LR i) k) = true := rfl
    rw [hr, Bool.not_true, Bool.false_or]
    cases c1 : cptK w (mask w) X ACC (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k)) z1
    · have h0 : ptailK n w LR TR BP X XP [] NE EP 0 (i + 1)
          (pcomp n w (mask w) ACC (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))) =
          (!(Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) ACC
              (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))) X)
            (pcomp n w (mask w) X (pcomp n w (mask w) ACC
              (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))))) ||
            CFSG.KC.LQT.P.anyN NE fun e => Nat.beq (pcomp n w (mask w) ACC
              (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))) (EP e)) := rfl
      rw [h0, commB_false hX h1 c1]
      rfl
    · rw [c1] at hq
      cases c2 : cptK w (mask w) X ACC (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k)) z2
      · have h0 : ptailK n w LR TR BP X XP [] NE EP 0 (i + 1)
            (pcomp n w (mask w) ACC (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))) =
            (!(Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) ACC
                (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))) X)
              (pcomp n w (mask w) X (pcomp n w (mask w) ACC
                (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))))) ||
              CFSG.KC.LQT.P.anyN NE fun e => Nat.beq (pcomp n w (mask w) ACC
                (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k))) (EP e)) := rfl
        rw [h0, commB_false hX h2 c2]
        rfl
      · rw [c2, Orb.strictB_eq] at hq
        exact hq
  | succ fuel ih =>
    intro i ACC hQ
    have e : ptailQ n w LR TR X z1 z2 NE EP (fuel + 1) i ACC = strictB (LR i) fun R =>
        allN (rcnt R) fun k => strictB (pcomp n w (mask w) ACC
          (TR (Nat.add (roff n (Nat.mul n w) R) k))) (ptailQ n w LR TR X z1 z2 NE EP fuel (i + 1)) :=
      rfl
    have e' : ptailK n w LR TR BP X XP [] NE EP (fuel + 1 + 1) i ACC = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP [] i ACC (rpt w (mask w) R k)) ||
          ptailK n w LR TR BP X XP [] NE EP (fuel + 1) (i + 1)
            (pcomp n w (mask w) ACC (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    rw [e, Orb.strictB_eq] at hQ
    rw [e', Orb.strictB_eq, Orb.allN_iff]
    intro k hk
    have hq := Orb.allN_iff.1 hQ k hk
    rw [Orb.strictB_eq] at hq
    have hr : relOKK w (mask w) BP XP [] i ACC (rpt w (mask w) (LR i) k) = true := rfl
    rw [hr, Bool.not_true, Bool.false_or]
    exact ih (i + 1) _ hq

end CFSG.KC.Misc.ChainTail

end
