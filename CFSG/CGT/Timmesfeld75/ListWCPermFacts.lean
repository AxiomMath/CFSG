module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.CGT.Timmesfeld75.ListWCPermCheck

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

structure Facts (D : Data) : Prop where
  nodup : (elts D).Nodup
  closed : ∀ x ∈ elts D, ∀ s ∈ pcT D, memS D (compT D.n x s) = true
  closedInv : ∀ x ∈ elts D, ∀ w ∈ D.pc, memS D (compT D.n x (wT D (invWord w))) = true
  invok : ∀ x ∈ elts D, invOK D.n x (invT D.n x) = true
  zlt : D.zIdx < 2 ^ D.pc.length
  zne : ¬ (el D D.zIdx = idT D.n)
  zsq : compT D.n (el D D.zIdx) (el D D.zIdx) = idT D.n
  zcomm : ∀ s ∈ pcT D, commT D.n (el D D.zIdx) s = true
  center : ∀ x ∈ elts D, (∀ s ∈ pcT D, commT D.n x s = true) →
    x = idT D.n ∨ x = el D D.zIdx
  cw : ∀ w ∈ D.cw, commT D.n (wT D w) (el D D.zIdx) = true
  excl : ∀ x ∈ elts D, x = idT D.n ∨ x = el D D.zIdx ∨
    (∃ c ∈ D.cls, ∃ p ∈ c, el D p.1 = x) ∨ excl D.n (elts D) (cwT D) x = true
  idxNodup : (0 :: D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)).Nodup
  idxLt : ∀ i ∈ (D.cls.flatMap fun c => c.map Prod.fst), i < 2 ^ D.pc.length
  classes : ∀ c ∈ D.cls, (match c with
    | [] => false
    | (i₀, _) :: _ => c.all fun p => commT D.n (wT D p.2) (el D D.zIdx) &&
        conjT D.n (wT D p.2) (wT D (invWord p.2)) (el D i₀) == el D p.1) = true
  verdicts : ∀ J ∈ allMasks D.cls.length, ∃ p ∈ D.verdicts, p.1 = J ∧ verdictOK D J p.2 = true

theorem facts_of_wcCheck {D : Data} (h : wcCheck D = true) : Facts D := by
  unfold wcCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun he => ?_, h7, h8, fun x hx hc => ?_, h10, fun x hx => ?_, h12,
    h13, h14, h15⟩
  · rw [he] at h6
    simp at h6
  · rcases h9 x hx with (h | h) | h
    · rw [List.all_eq_true.2 hc] at h
      exact absurd h (by decide)
    · exact Or.inl h
    · exact Or.inr h
  · rcases h11 x hx with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end CFSG.CGT.Timmesfeld75.WCCheck
