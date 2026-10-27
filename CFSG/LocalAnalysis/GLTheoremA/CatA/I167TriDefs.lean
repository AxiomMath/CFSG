module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def Type167Grp (p : ℕ) (Q : Type) [Group Q] : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ catalogIs Q (isLnA n 2)) ∨
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ 6 ≤ n ∧ catalogIs Q (isOmMA n 2)) ∨
  (∃ n k : ℕ, Odd n ∧ 3 ≤ n ∧ (k = 1 → 5 ≤ n) ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
    catalogIs Q (isOmPA n (2 ^ k)))

@[expose] def Type167Canon (l : GLALabel) : Prop :=
  (l.tag = .A ∧ 3 ≤ l.rank) ∨ (l.tag = .twD ∧ 6 ≤ l.rank) ∨ (l.tag = .D ∧ 5 ≤ l.rank)

@[expose] def TriJLabel (l : GLALabel) : Prop :=
  l.tag = .G2 ∨ ((l.tag = .A ∨ l.tag = .twA) ∧ l.rank = 2) ∨ l.tag = .triD4

theorem type167Grp_congr {p : ℕ} {Q R : Type} [Group Q] [Group R] (e : Q ≃* R) :
    Type167Grp p Q ↔ Type167Grp p R := by
  unfold Type167Grp
  simp only [catalogIs_congr e]

theorem not_type167Canon_of_triJLabel {l : GLALabel} (h : TriJLabel l) : ¬ Type167Canon l := by
  intro hc
  unfold TriJLabel at h
  unfold Type167Canon at hc
  rcases h with h | ⟨h | h, h2⟩ | h <;> rcases hc with ⟨h', h''⟩ | ⟨h', h''⟩ | ⟨h', h''⟩ <;> simp_all <;> omega

end CFSG.LocalAnalysis.GLTheoremA.I167

end
