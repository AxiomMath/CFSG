module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Split
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)

@[expose] def K37Open {X : Type} [Group X] [Finite X] (K E : Subgroup X) : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧
        (q.card = 2 ∨ ¬ autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧
        (q.card = 2 ∨ (m = 2 ∧ q.card = 8 ∧
          ¬ autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 3 q) ∧
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 4 q) ∧
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 3 q) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .B 3 q) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .G2 q) ∨
    IsThreeCenterCover ↥K (alternatingGroup (Fin 6)) ∨
    IsThreeCenterCover ↥K (alternatingGroup (Fin 7)) ∨
    IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .M22).Group ∨
    IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .J3).Group ∨
    IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .McL).Group ∨
    IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .Suz).Group ∨
    IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .ONan).Group ∨
    ∃ s : TauCeti.SporadicName, s ∉ CFSG.RankThree.PartOne.Census3.sporadicsThm3 ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

@[expose] def K37Rest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E S : Subgroup X), K37Setting X K E S → K37Open K E →
    S ≤ Subgroup.centralizer (K : Set X)

theorem K37Setting.goal_of_open (hR : K37Rest) {X : Type} [Group X] [Finite X]
    {K E S : Subgroup X} (h : K37Setting X K E S) (hO : K37Open K E) : K37Goal K S :=
  fun hSC => absurd (hR X K E S h hO) hSC

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
