module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def QTKSimpleList (S : Type) [Group S] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 9 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 2 p f) ∨
      (∃ f : ℕ, (f = 1 ∨ f = 2) ∧
        (StatedClassicalModel S .PSL 3 p f ∨ StatedClassicalModel S .PSU 3 p f)) ∨
      StatedClassicalModel S .PSp 2 p 1 ∨ ChevalleyExceptionalModel S .G2 p 1 ∨
      ((∃ a : ℕ, p = 2 ^ a + 1) ∧ StatedClassicalModel S .PSL 4 p 1) ∨
      ((∃ b : ℕ, p + 1 = 2 ^ b) ∧ StatedClassicalModel S .PSU 4 p 1))) ∨
  ((∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel S .PSU 4 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)) ∨
    StatedClassicalModel S .PSU 5 2 2 ∨ ReeTitsModel S .Tits 2 1) ∨
  ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel S .PSL n 2 1) ∨
    StatedClassicalModel S .PSp 3 2 1) ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨
      s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL) ∧
    Nonempty (S ≃* NativeSporadic.Carrier s))

end CFSG.SectionRank.QTK
