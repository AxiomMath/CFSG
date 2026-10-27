module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I14NegPieceA : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J →
    labK = ⟨.twA, 5, 2⟩ → p = 5 → ¬ (labJ.tag = .A ∧ labJ.rank = 3 ∧ labJ.n = 2)

@[expose] def I14NegPieceB : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J →
    (labK.tag = .twA ∧ labK.rank = 5) → labJ.tag ≠ .B ∧ labJ.tag ≠ .C ∧ labJ.tag ≠ .D

@[expose] def I14NegPieceC : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J →
    ((labK.tag = .D ∨ labK.tag = .B ∨ labK.tag = .C) ∧ labK.rank = 5) →
      ¬ (labJ.tag = .twD ∧ labJ.rank = 5)

@[expose] def I14NegPieceD : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J →
    labK = ⟨.E6, 0, 2⟩ → ¬ (labJ.tag = .twD ∧ labJ.rank = 5)

theorem i14NegFactS_iff_pieces :
    I14NegFactS ↔ I14NegPieceA ∧ I14NegPieceB ∧ I14NegPieceC ∧ I14NegPieceD := by
  constructor
  · intro h
    refine ⟨fun S _ _ p α J labK labJ hp hp2 hZ hK hJ hα hcomp => (h S p α J labK labJ hp hp2 hZ hK hJ hα hcomp).1,
      fun S _ _ p α J labK labJ hp hp2 hZ hK hJ hα hcomp => (h S p α J labK labJ hp hp2 hZ hK hJ hα hcomp).2.1,
      fun S _ _ p α J labK labJ hp hp2 hZ hK hJ hα hcomp => (h S p α J labK labJ hp hp2 hZ hK hJ hα hcomp).2.2.1,
      fun S _ _ p α J labK labJ hp hp2 hZ hK hJ hα hcomp => (h S p α J labK labJ hp hp2 hZ hK hJ hα hcomp).2.2.2⟩
  · rintro ⟨hA, hB, hC, hD⟩ S _ _ p α J labK labJ hp hp2 hZ hK hJ hα hcomp
    exact ⟨hA S p α J labK labJ hp hp2 hZ hK hJ hα hcomp, hB S p α J labK labJ hp hp2 hZ hK hJ hα hcomp,
      hC S p α J labK labJ hp hp2 hZ hK hJ hα hcomp, hD S p α J labK labJ hp hp2 hZ hK hJ hα hcomp⟩

theorem i14NegFactS_of_pieces (hA : I14NegPieceA) (hB : I14NegPieceB) (hC : I14NegPieceC)
    (hD : I14NegPieceD) : I14NegFactS :=
  i14NegFactS_iff_pieces.2 ⟨hA, hB, hC, hD⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
