module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotFrontier
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4U0Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622KFactD)

variable {G : Type} [Group G] [Finite G]

theorem p622Prop614Large_of_residues (hnr : SlotP614NormalizerRankLarge)
    (h617 : SlotP614StepL617Large) (hΩ : SlotP614OmegaULarge) (hcore : SlotP614CoreLargeU0)
    (hS : Setting G) (hD1 : TheoremD1 G) (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp3 : p ≠ 3) {P : Sylow p G} {M : Subgroup G} (hsit : SmallRankSituation G p P M)
    {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) :
    P622Prop614At M x z := by
  intro H hH hBH hex
  obtain ⟨S₀, hS₀HM, hS₀2, hS₀1, hBS₀⟩ := hex
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  by_contra hHM
  have hnr' : Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z) := by
    by_cases hα : HasPrimeConstraint (G := M) p
    · exact fail614GNormalizerRank_of_alpha hS hsit hα hx hz
    · exact hnr G hS hD1 p hp5 P M hsit x z hx hz hα
  obtain ⟨S', hSS', hS'⟩ := exists_isMaxTwoInvariantIn_of_le
    (B := zpowers x ⊔ zpowers z) (X := H ⊓ M) (S := S₀) ⟨hS₀HM, hS₀2, hBS₀⟩
  have hpair : Prop614Pair M (zpowers x ⊔ zpowers z) H S' :=
    ⟨hH, hBH, hHM, hS', ne_bot_of_le_ne_bot hS₀1 hSS'⟩
  obtain ⟨H₀, S₁, hopt⟩ := exists_fail614GOptimal hS hD1 hsit hx hz hnr' ⟨H, S', hpair⟩
  have hO : rankThreePrimeCore p H₀ ≤ M := h617 G hS hD1 p hp5 P M hsit x z hx hz H₀ S₁ hopt
  have hΩ' : ∀ Q : Subgroup G, Q ≤ H₀ → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z := fun Q hQH hQp hBQ q hqQ hq1 =>
    omega_le_of_omegaU hS hD2 hU0 hp5 hsit hopt hQH hQp hBQ hqQ hq1
      (hΩ G hS hD1 p hp5 P M hsit x z hx hz H₀ S₁ hopt hO Q hQH hQp hBQ)
  exact hcore G hS hD1 hU0 p hp5 P M hsit x z hx hz H₀ S₁ hopt hO hΩ'

theorem p622_prop614_of_residues (hS : Setting G) (hD1 : TheoremD1 G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) (h3 : GL83SmallRankProp614Three G) (hnr : SlotP614NormalizerRankLarge)
    (h617 : SlotP614StepL617Large) (hΩ : SlotP614OmegaULarge) (hcore : SlotP614CoreLargeU0) :
    GL83SmallRankProp614 G := by
  intro p P M hsit x z hx hz H hH hBH hex
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 P M hsit x z hx hz H hH hBH hex
  · exact p622Prop614Large_of_residues hnr h617 hΩ hcore hS hD1 hD2 hU0 hp3 hsit hx hz H hH hBH
      hex

theorem gl83SmallRankProp622_of_open (hK : KFactBlockFactorThreePrime)
    (hL62 : ∀ (G : Type) [Group G] [Finite G], GL83SmallRankLemma62At3 G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hδ : SlotP614CaseDelta) (hcore3 : SlotP614Core) (hnr : SlotP614NormalizerRankLarge)
    (h617 : SlotP614StepL617Large) (hΩ : SlotP614OmegaULarge) (hcoreL : SlotP614CoreLargeU0)
    (hKD3 : P622KFactDThree) (hKD5 : S622KFactD) (hK64 : KFact64ii)
    (h62d : P622CaseDelta4) (h65L : P622Prop65Large) (hKx : P622Kx) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G →
      FullCoreLocal G → GL83SmallRankProp622 G := by
  intro G _ _ hS hD1 hD2 hU0
  have h3 : GL83SmallRankProp614Three G :=
    prop614Three_of_core hS hU0 hD1 hK
      (fun P M hsit x z hx hz => hL62 G hS hU0 P M hsit x z hx hz)
      (fun P M hsit x z hx hz hδc => hδ G hS hD1 P M hsit x z hx hz hδc)
      (hcore3 G hS hD1)
  have h614 : GL83SmallRankProp614 G :=
    p622_prop614_of_residues hS hD1 hD2 hU0 h3 hnr h617 hΩ hcoreL
  have hP65 : P622Prop65 G :=
    p622Prop65_of_parts hS hD1 hD2 hU0 (prop65Alpha_of_kfacts hS hU0 hK1 hK2)
      (p622Lemma62Three_of_delta4 hL62 h62d) h65L
  exact gl83SmallRankProp622_of_inputs hS hD1 hD2 hU0 h614
    (p622KFactD_of_three_five hKD3 hKD5) hK64 hP65 hKx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
