module

public import Certificates.Data.Kernel.Misc.ChainTailQL
public import CFSG.Certificates.Kernel.Misc.ChainTailQSound
public import CFSG.Certificates.Kernel.Misc.ChainTailLvSound
public import Certificates.Data.Kernel.Misc.ChainTailOrb
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.BfsPin (PP)

variable {n w : ℕ} {LR TR : ℕ → ℕ} {BP X z1 z2 : ℕ} {XP : ℕ → ℕ}
  {RL : ℕ → List (ℕ × ℕ × ℕ)} {L : ℕ → Bool}

theorem qLeafK_eq (hX : PP n w X) (h1 : z1 < n) (h2 : z2 < n) (acc t j : ℕ) :
    qLeafK n w X L z1 z2 acc t =
      ptailGK n w LR TR BP X XP RL L 0 j (pcomp n w (mask w) acc t) := by
  have e : ptailGK n w LR TR BP X XP RL L 0 j (pcomp n w (mask w) acc t) =
      (!(Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) acc t) X)
        (pcomp n w (mask w) X (pcomp n w (mask w) acc t))) || L (pcomp n w (mask w) acc t)) := rfl
  rw [e]
  unfold qLeafK
  cases c1 : cptK w (mask w) X acc t z1
  · rw [commB_false hX h1 c1]
    rfl
  · cases c2 : cptK w (mask w) X acc t z2
    · rw [commB_false hX h2 c2]
      rfl
    · exact Orb.strictB_eq _ _

theorem ptailQGK_eq (hX : PP n w X) (h1 : z1 < n) (h2 : z2 < n) (f i acc : ℕ) :
    ptailQGK n w LR TR BP X XP RL L z1 z2 f i acc =
      ptailGK n w LR TR BP X XP RL L (f + 1) i acc := by
  induction f generalizing i acc with
  | zero =>
    have e1 : ptailQGK n w LR TR BP X XP RL L z1 z2 0 i acc = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
          qLeafK n w X L z1 z2 acc (TR (Nat.add (roff n (Nat.mul n w) R) k)) := rfl
    have e2 : ptailGK n w LR TR BP X XP RL L (0 + 1) i acc = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
          ptailGK n w LR TR BP X XP RL L 0 (Nat.succ i)
            (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    rw [e1, e2]
    simp only [qLeafK_eq (LR := LR) (TR := TR) (BP := BP) (XP := XP) (RL := RL) hX h1 h2 _ _
      (Nat.succ i)]
  | succ f ih =>
    have e1 : ptailQGK n w LR TR BP X XP RL L z1 z2 (f + 1) i acc = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
          ptailQGK n w LR TR BP X XP RL L z1 z2 f (Nat.succ i)
            (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    have e2 : ptailGK n w LR TR BP X XP RL L (f + 1 + 1) i acc = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
          ptailGK n w LR TR BP X XP RL L (f + 1) (Nat.succ i)
            (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    rw [e1, e2]
    simp only [ih]

theorem repBranchQK_eq (hX : PP n w X) (h1 : z1 < n) (h2 : z2 < n) (f q : ℕ) :
    repBranchQK n w LR TR BP X XP RL L z1 z2 (f + 2) q =
      (relOKK w (mask w) BP XP (RL 0) 0 (pidn n w) (rpt w (mask w) (LR 0) q) &&
        ptailGK n w LR TR BP X XP RL L (f + 1) 1
          (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q))) := by
  have e : Nat.sub (f + 2) 2 = f := Nat.add_sub_cancel f 2
  unfold repBranchQK
  rw [e, ptailQGK_eq hX h1 h2]

theorem repBranchQK_LK {NE : ℕ} {EP : ℕ → ℕ} (hX : PP n w X) (h1 : z1 < n) (h2 : z2 < n)
    (f q : ℕ) :
    repBranchQK n w LR TR BP X XP RL (fun P => CFSG.KC.LQT.P.anyN NE fun e => Nat.beq P (EP e))
        z1 z2 (f + 2) q =
      repBranchLK n w LR TR BP X XP RL NE EP (f + 2) q := by
  have e : Nat.sub (f + 2) 1 = f + 1 := Nat.add_sub_cancel (f + 1) 1
  unfold repBranchLK
  rw [repBranchQK_eq hX h1 h2, e]
  rfl

theorem repBranchQK_K {rels : List (ℕ × ℕ × ℕ)} {NE : ℕ} {EP : ℕ → ℕ} (hX : PP n w X)
    (h1 : z1 < n) (h2 : z2 < n) (f q : ℕ) :
    repBranchQK n w LR TR BP X XP (fun _ => rels)
        (fun P => CFSG.KC.LQT.P.anyN NE fun e => Nat.beq P (EP e)) z1 z2 (f + 2) q =
      repBranchK n w LR TR BP X XP rels NE EP (f + 2) q := by
  rw [repBranchQK_LK hX h1 h2]
  exact repBranchLK_eq (fun _ _ _ => rfl) _ _

end CFSG.KC.Misc.ChainTail

end
