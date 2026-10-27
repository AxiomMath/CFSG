module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Even
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Odd
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii)

variable {G : Type} [Group G] [Finite G]

theorem p622Prop65_of_parts (hS : Setting G) (hD1 : TheoremD1 G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) (h3 : GL83SmallRankProp65Alpha G) (h62 : P622Lemma62Three)
    (hL : P622Prop65Large) : P622Prop65 G := by
  intro p P M hsit x z hx hz hN F hF1 hFM hcop hodd hBF
  by_cases hp3 : p = 3
  · subst hp3
    rcases h62 G hS hD1 hD2 hU0 P M hsit x z hx hz with hα | hnorm
    · have h2 : Nat.Coprime (Nat.card F) 2 := Nat.coprime_two_right.mpr hodd
      have h3' : Nat.Coprime (Nat.card F) 3 := hcop.symm
      have h6 : Nat.Coprime (Nat.card F) (2 * 3) := Nat.Coprime.mul_right h2 h3'
      have hcop6 : Nat.Coprime (Nat.card F) 6 := h6
      exact h3 P M hsit hα x z hx hz F hFM hF1 hcop6 hBF
    · exact absurd hnorm hN
  · exact hL G hS hD1 hD2 hU0 p hp3 P M hsit x z hx hz hN F hF1 hFM hcop hodd hBF

theorem gl83SmallRankProp622_of_inputs (hS : Setting G) (hD1 : TheoremD1 G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) (h614 : GL83SmallRankProp614 G) (hKD : P622KFactD)
    (hK64 : KFact64ii) (hP65 : P622Prop65 G) (hKx : P622Kx) : GL83SmallRankProp622 G := by
  intro p P M hsit x hx T hT
  by_contra hcon
  have hnc : ¬ SmallRankCover p M x := fun h => hcon (Or.inl h)
  have hn1 : ¬ (p = 3 ∧ SmallRankCaseOne x T) := fun h => hcon (Or.inr h)
  obtain ⟨z, hz⟩ := p622_exists_central hS P hsit.mem_sigmaA
  have hf : Prop627Failure G p P M x z T := p622_failure_of_not hsit hx hz hT hnc hn1
  have h614x : P622Prop614At M x z := fun H hH hBH hex => h614 p P M hsit x z hx hz H hH hBH hex
  obtain ⟨S, hc⟩ := p622_exists_conf hf h614x
  have hodd := p622_odd_core hKD hS hc hnc
  have hbot : smallRankD p x = ⊥ := p622_primeCore_eq_bot hK64 hP65 hS hc hnc hodd
  have hbot' : rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥ := hbot
  have hnc1 : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x) := by
    rw [hbot, sup_bot_eq]
    exact fun h => hx.not_centralizer_le (h.trans inf_le_left)
  obtain ⟨K, hK⟩ := p622_apply_pcomp hK64 hS hc hnc1
  obtain ⟨hL, hLH, hzK, hrk, hLY, hLN⟩ := p622_kxData_of_pcomp_bot hK hbot'
  have hLM : ¬ K ≤ M := fun h => hLY ((le_inf h hLH).trans le_sup_left)
  exact hKx G hS hD1 hD2 hU0 p P M x z T S hf h614x hc.isMax hc.le_S hbot' K hL hLH hzK hrk
    hLM hLN

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
