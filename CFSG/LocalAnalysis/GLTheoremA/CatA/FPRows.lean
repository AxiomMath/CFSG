module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMarking
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI

variable {G : Type} [Group G] [Finite G]

@[expose] def StOrderBody (p : ℕ) : LargeEvenRawCont := fun R _ _ F =>
  ∀ f ∈ F, orderOf f = p → twoPart (fixNum f) ^ p = twoPart (Nat.card R)

theorem i91CentPartAt_of_stOrder {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hst : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → ¬ (lab.tag = .triD4 ∧ p = 3) →
      CAll lab (LargeEvenSimpleGuard (StOrderBody p))) : I91CentPartAt G p := by
  intro X L b hL _ _ hF
  have h := canon_marking_and_labelAll_simple' (P' := fun lab R _ I F =>
      ¬ (lab.tag = .triD4 ∧ p = 3) → StOrderBody p R I F)
    (fun lab hlab => by
      by_cases h3 : lab.tag = .triD4 ∧ p = 3
      · exact (canonRawInnAny hp.ne_one hlab).mono fun R _ I F _ hs hna h => absurd h3 h
      · exact (hst lab hlab h3).mono fun R _ I F h' hs hna _ => h' hs hna) hF.2
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, hP, hSt⟩ := Canonical.largeEvenMarking_exists h
  obtain ⟨hne, f, hf, u, hu, hord, he⟩ := fieldOn_data hF.1 θ hP
  have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, h'⟩
    rcases hne with h0 | h0
    · exact h0 h
    · exact h0 h'
  have hZ := odd_card_center_pQuot hp hp2 L
  rw [centCard2_eq_twoPart_fixNum hF.1 hZ, card2_eq_twoPart_card_pSimple hp hp2,
    ← fixNum_congr θ, he, fixNum_conj, Nat.card_congr θ.toEquiv]
  exact hSt h3 f hf hord

end FP

end CFSG.LocalAnalysis.GLTheoremA
