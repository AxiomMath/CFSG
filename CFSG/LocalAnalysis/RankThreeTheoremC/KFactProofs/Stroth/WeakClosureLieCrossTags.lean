module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossKnown
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCross

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def CrossClassical (t : StatedLieTag) (m : ℕ) : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {n ℓ f p : ℕ} [Fact p.Prime], p ≠ 2 → p ≠ ℓ → m ≤ n →
    ¬ CrossCharKnown t n ℓ f p → StatedClassicalModel K t n ℓ f → WCOn p K

@[expose] def CrossChevalley (t : StatedLieTag) : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime], StatedLieAdmissible t 0 ℓ f →
    p ≠ 2 → p ≠ ℓ → ChevalleyExceptionalModel K t ℓ f → WCOn p K

@[expose] def CrossReeTits (t : StatedLieTag) : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime], StatedLieAdmissible t 0 ℓ f →
    p ≠ 2 → p ≠ ℓ → ReeTitsModel K t ℓ f → WCOn p K

structure CrossCharTags : Prop where
  psl : CrossClassical .PSL 3
  psu : CrossClassical .PSU 3
  psp : CrossClassical .PSp 2
  pomegaOdd : CrossClassical .POmegaOdd 3
  pomegaPlus : CrossClassical .POmegaPlus 4
  pomegaMinus : CrossClassical .POmegaMinus 4
  g2 : CrossChevalley .G2
  f4 : CrossChevalley .F4
  e6 : CrossChevalley .E6
  e7 : CrossChevalley .E7
  e8 : CrossChevalley .E8
  twistedE6 : CrossChevalley .twistedE6
  trialityD4 : CrossChevalley .trialityD4
  twistedG2 : CrossReeTits .twistedG2
  twistedF4 : CrossReeTits .twistedF4
  tits : CrossReeTits .Tits

theorem wcLieCross_of_tags (h : CrossCharTags) : WCLieCross := by
  intro t K _ _ _ _ n ℓ f hadm hmodel p hp hp2 hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hk : CrossCharKnown t n ℓ f p
  · exact wcOn_of_crossCharKnown hmodel hp hp2 hpℓ hk
  · cases t with
    | PSL =>
      have hn2 : n ≠ 2 := fun h2 => hk (Or.inr (Or.inl ⟨rfl, h2⟩))
      have hn : 2 ≤ n := hadm.2.2.1
      exact h.psl hp2 hpℓ (by omega) hk (hmodel.statedClassicalModel (by decide))
    | PSU => exact h.psu hp2 hpℓ hadm.2.2.1 hk (hmodel.statedClassicalModel (by decide))
    | PSp => exact h.psp hp2 hpℓ hadm.2.2.1 hk (hmodel.statedClassicalModel (by decide))
    | POmegaOdd =>
      exact h.pomegaOdd hp2 hpℓ hadm.2.2.1 hk (hmodel.statedClassicalModel (by decide))
    | POmegaPlus =>
      exact h.pomegaPlus hp2 hpℓ hadm.2.2 hk (hmodel.statedClassicalModel (by decide))
    | POmegaMinus =>
      exact h.pomegaMinus hp2 hpℓ hadm.2.2 hk (hmodel.statedClassicalModel (by decide))
    | G2 =>
      obtain rfl : n = 0 := hadm.2.2.1
      exact h.g2 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | F4 =>
      obtain rfl : n = 0 := hadm.2.2
      exact h.f4 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | E6 =>
      obtain rfl : n = 0 := hadm.2.2
      exact h.e6 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | E7 =>
      obtain rfl : n = 0 := hadm.2.2
      exact h.e7 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | E8 =>
      obtain rfl : n = 0 := hadm.2.2
      exact h.e8 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | twistedE6 =>
      obtain rfl : n = 0 := hadm.2.2
      exact h.twistedE6 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | trialityD4 =>
      obtain rfl : n = 0 := hadm.2.2
      exact h.trialityD4 hadm hp2 hpℓ (hmodel.chevalleyExceptionalModel (by decide))
    | twistedB2 => exact absurd (Or.inl rfl) hk
    | twistedG2 =>
      obtain rfl : n = 0 := hadm.2.2.1
      exact h.twistedG2 hadm hp2 hpℓ (hmodel.reeTitsModel (by decide)).2
    | twistedF4 =>
      obtain rfl : n = 0 := hadm.2.2.1
      exact h.twistedF4 hadm hp2 hpℓ (hmodel.reeTitsModel (by decide)).2
    | Tits =>
      obtain rfl : n = 0 := hadm.2.2.1
      exact h.tits hadm hp2 hpℓ (hmodel.reeTitsModel (by decide)).2

theorem wcLie_of_crossCharTags
    (h : CrossCharTags) : WCLie :=
  wcLie_of_crossChar (crossCharResidue_iff.2 (wcLieCross_of_tags h))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
