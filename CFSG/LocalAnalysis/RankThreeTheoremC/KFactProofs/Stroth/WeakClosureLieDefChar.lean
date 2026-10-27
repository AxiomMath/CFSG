module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieSymplectic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieOrthogonal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwisted
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieRee

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

section DefChar

theorem wcLie_defChar {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f) (h : LieModel K t n ℓ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p = ℓ) : WCOn p K := by
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  cases t with
  | PSL =>
    have hcl := h.statedClassicalModel (by decide)
    have hn : 2 ≤ n := hadm.2.2.1
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact wcOn_psl_two hp2 hcl
    · exact wcOn_psl_of_three_le hp2 hn3 hcl
  | PSU => exact wcOn_psu hp2 hadm.2.2.1 (h.statedClassicalModel (by decide))
  | PSp => exact wcOn_psp hp2 hadm.2.2.1 (h.statedClassicalModel (by decide))
  | POmegaOdd => exact wcOn_pomegaOdd hp2 hadm.2.2.1 (h.statedClassicalModel (by decide))
  | POmegaPlus => exact wcOn_pomegaPlus hp2 hadm.2.2 (h.statedClassicalModel (by decide))
  | POmegaMinus => exact wcOn_pomegaMinus hp2 hadm.2.2 (h.statedClassicalModel (by decide))
  | G2 =>
    exact wcOn_chevalley_untwisted hp2 (Or.inl rfl) (h.chevalleyExceptionalModel (by decide))
  | F4 =>
    exact wcOn_chevalley_untwisted hp2 (Or.inr (Or.inl rfl))
      (h.chevalleyExceptionalModel (by decide))
  | E6 =>
    exact wcOn_chevalley_untwisted hp2 (Or.inr (Or.inr (Or.inl rfl)))
      (h.chevalleyExceptionalModel (by decide))
  | E7 =>
    exact wcOn_chevalley_untwisted hp2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (h.chevalleyExceptionalModel (by decide))
  | E8 =>
    exact wcOn_chevalley_untwisted hp2 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (h.chevalleyExceptionalModel (by decide))
  | twistedE6 =>
    exact wcOn_chevalley_twisted hp2 (Or.inl rfl) (h.chevalleyExceptionalModel (by decide))
  | trialityD4 =>
    exact wcOn_chevalley_twisted hp2 (Or.inr rfl) (h.chevalleyExceptionalModel (by decide))
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedG2 =>
    have h3 : p = 3 := hadm.2.2.2.1
    subst h3
    exact wcOn_reeG2 (h.reeTitsModel (by decide)).2
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

end DefChar

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
