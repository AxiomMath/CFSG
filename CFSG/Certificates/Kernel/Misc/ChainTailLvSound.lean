module

public import Certificates.Data.Kernel.Misc.ChainTailLv

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem relOKK_lv {w m BP : Nat} {XP : Nat → Nat} {rels : List (Nat × Nat × Nat)}
    {RL : Nat → List (Nat × Nat × Nat)} (h1 : ∀ i, ∀ r ∈ RL i, r ∈ rels)
    (h2 : ∀ r ∈ rels, r ∈ RL (Nat.max r.1 r.2.1)) (i acc q : Nat) :
    relOKK w m BP XP (RL i) i acc q = relOKK w m BP XP rels i acc q := by
  unfold relOKK
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  refine ⟨fun h r hr => ?_, fun h r hr => h r (h1 i r hr)⟩
  cases hm : Nat.beq (Nat.max r.1 r.2.1) i
  · rfl
  · have he := Nat.eq_of_beq_eq_true hm
    have hr' := h2 r hr
    rw [he] at hr'
    have := h r hr'
    rw [hm] at this
    exact this

theorem relOKK_tbl {w m BP : Nat} {XP : Nat → Nat} {rels : List (Nat × Nat × Nat)}
    {T : List (List (Nat × Nat × Nat))} (h1 : ∀ l ∈ T, ∀ r ∈ l, r ∈ rels)
    (h2 : ∀ r ∈ rels, r ∈ T.getD (Nat.max r.1 r.2.1) []) (i acc q : Nat) :
    relOKK w m BP XP (T.getD i []) i acc q = relOKK w m BP XP rels i acc q := by
  refine relOKK_lv (RL := fun i => T.getD i []) (fun i r hr => ?_) h2 i acc q
  rw [List.getD_eq_getElem?_getD] at hr
  cases hl : T[i]? with
  | none =>
    rw [hl] at hr
    simp at hr
  | some l =>
    rw [hl] at hr
    exact h1 l (List.mem_of_getElem? hl) r hr

theorem ptailLK_eq {n w BP X NE : Nat} {LR TR XP EP : Nat → Nat} {rels : List (Nat × Nat × Nat)}
    {RL : Nat → List (Nat × Nat × Nat)}
    (h : ∀ i acc q, relOKK w (mask w) BP XP (RL i) i acc q = relOKK w (mask w) BP XP rels i acc q)
    (f i acc : Nat) :
    ptailLK n w LR TR BP X XP RL NE EP f i acc = ptailK n w LR TR BP X XP rels NE EP f i acc := by
  induction f generalizing i acc with
  | zero => rfl
  | succ f ih =>
    have e1 : ptailLK n w LR TR BP X XP RL NE EP (f + 1) i acc = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
          ptailLK n w LR TR BP X XP RL NE EP f (Nat.succ i)
            (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    have e2 : ptailK n w LR TR BP X XP rels NE EP (f + 1) i acc = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) R k)) ||
          ptailK n w LR TR BP X XP rels NE EP f (Nat.succ i)
            (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))) := rfl
    rw [e1, e2]
    simp only [h, ih]

theorem repBranchLK_eq {n w BP X NE : Nat} {LR TR XP EP : Nat → Nat} {rels : List (Nat × Nat × Nat)}
    {RL : Nat → List (Nat × Nat × Nat)}
    (h : ∀ i acc q, relOKK w (mask w) BP XP (RL i) i acc q = relOKK w (mask w) BP XP rels i acc q)
    (nb q : Nat) :
    repBranchLK n w LR TR BP X XP RL NE EP nb q = repBranchK n w LR TR BP X XP rels NE EP nb q := by
  unfold repBranchLK repBranchK ptailBranchK
  rw [h, ptailLK_eq h]
  cases relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) q) <;> rfl

end CFSG.KC.Misc.ChainTail

end
