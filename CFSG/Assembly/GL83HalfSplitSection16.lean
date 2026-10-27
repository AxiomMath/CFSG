module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Assembly

@[expose] def LargeEvenHalfSplitWithE6Four (p : ℕ) (lab : LargeEvenLabel)
    (centerTrivial : Prop) : Prop :=
  LargeEvenHalfSplit p lab centerTrivial ∨
    (lab.tag = .E6 ∧ lab.n = 2 ∧ centerTrivial ∧ p = 5)

theorem largeEvenHalfSplit_implies_withE6Four {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : LargeEvenHalfSplit p lab c) : LargeEvenHalfSplitWithE6Four p lab c :=
  Or.inl h

theorem largeEvenHalfSplitWithE6Four_E6_four {c : Prop} (hc : c) :
    LargeEvenHalfSplitWithE6Four 5 ⟨.E6, 0, 2⟩ c :=
  Or.inr ⟨rfl, rfl, hc, rfl⟩

theorem not_largeEvenHalfSplit_E6_four :
    ¬ LargeEvenHalfSplit 5 ⟨.E6, 0, 2⟩ True := by
  norm_num [LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted]

@[expose] def LargeEvenHalfSplitE6FourException (p : ℕ) (lab : LargeEvenLabel)
    (centerTrivial : Prop) : Prop :=
  lab.tag = .E6 ∧ lab.n = 2 ∧ centerTrivial ∧ p = 5

theorem not_largeEvenHalfSplit_of_E6FourException {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : LargeEvenHalfSplitE6FourException p lab c) : ¬ LargeEvenHalfSplit p lab c := by
  rcases h with ⟨ht, hn, -, hp⟩
  subst p
  norm_num [LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted, ht, hn]

theorem largeEvenHalfSplit_iff_withE6Four_and_not_exception {p : ℕ}
    {lab : LargeEvenLabel} {c : Prop} :
    LargeEvenHalfSplit p lab c ↔
      LargeEvenHalfSplitWithE6Four p lab c ∧ ¬ LargeEvenHalfSplitE6FourException p lab c := by
  constructor
  · intro h
    exact ⟨Or.inl h, fun he => not_largeEvenHalfSplit_of_E6FourException he h⟩
  · rintro ⟨h, hne⟩
    exact h.elim id (fun he => (hne he).elim)

@[expose] def LargeEvenSplit16 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (LargeEvenUntwisted lab.tag ∧ p ∣ 2 ^ lab.n - 1) ∨
    (¬ LargeEvenUntwisted lab.tag ∧ lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4 ∧
      p ∣ 2 ^ lab.n + 1) ∨
    ((lab.tag = .twD ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4) ∧
      p ∣ 2 ^ lab.n - 1) ∨
    (lab.n = 1 ∧ p = 3)

@[expose] def LargeEvenHalfSplit16 (p : ℕ) (lab : LargeEvenLabel)
    (centerTrivial : Prop) : Prop :=
  LargeEvenSplit16 p lab ∨
    ((lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
      p ∣ 2 ^ lab.n + 1) ∨
    (((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) ∧ p ∣ 2 ^ lab.n - 1) ∨
    (((lab.tag = .A ∧ lab.rank = 5) ∨ lab.tag = .E6) ∧ lab.n = 2 ∧ centerTrivial ∧ p = 5) ∨
    (lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1 ∧ p = 7) ∨
    (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7)

theorem largeEvenHalfSplit16_E6_four {centerTrivial : Prop} (hcenter : centerTrivial) :
    LargeEvenHalfSplit16 5 ⟨.E6, 0, 2⟩ centerTrivial :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl, hcenter, rfl⟩)))

theorem largeEvenSplit16_triality_plus : LargeEvenSplit16 5 ⟨.triD4, 0, 2⟩ := by
  norm_num [LargeEvenSplit16, LargeEvenUntwisted]

theorem not_largeEvenSplit_triality_plus : ¬ LargeEvenSplit 5 ⟨.triD4, 0, 2⟩ := by
  norm_num [LargeEvenSplit, LargeEvenUntwisted]

theorem largeEvenSplit_suzuki_plus : LargeEvenSplit 3 ⟨.twB2, 0, 3⟩ := by
  norm_num [LargeEvenSplit, LargeEvenUntwisted]

theorem not_largeEvenSplit16_suzuki_plus : ¬ LargeEvenSplit16 3 ⟨.twB2, 0, 3⟩ := by
  norm_num [LargeEvenSplit16, LargeEvenUntwisted]

end CFSG.Assembly
