module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrontier

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def StrongOrExceptionalFive (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p → D1Local p P M →
    GLBCore p 2 (P : Subgroup G) ≤ M →
      ((p ∣ Nat.card M ∧ ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G)) ∨
        (Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
          ∃ P₀ : Subgroup G, GLBClauseTwo M P P₀ p))

@[expose] def DichotomyRank4Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Open.IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G →
      StrongOrExceptionalFive G

@[expose] def ConfinementNonstrongFive (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p → D1Local p P M →
    ¬ GLBStronglyEmbedded p M →
      ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ Open.pRank p (H ⊓ M) → H ≤ M

@[expose] def E2NonstrongRank4Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Open.IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G →
      ConfinementNonstrongFive G

variable {G : Type} [Group G] [Finite G]

theorem eq_three_or_five_le_of_d1Local {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hloc : D1Local p P M) : p = 3 ∨ 5 ≤ p := by
  obtain ⟨hp, hp2, -, -⟩ := hloc.beta
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  omega

theorem strongOrExceptional_of_five (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hP5 : PElementPrimeFive G) (h313 : GL83NormalElementaryRankFour)
    (h5 : StrongOrExceptionalFive G) : StrongOrExceptional G := by
  intro p P M hloc hcore
  rcases eq_three_or_five_le_of_d1Local hloc with rfl | hp5
  · exact Or.inl (stronglyEmbedded_three_of_pElement hS hD1 hFC hP5 h313 hloc).2
  · exact (h5 p P M hp5 hloc hcore).imp id fun h => ⟨hp5, h⟩

theorem confinementNonstrong_of_five (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hP5 : PElementPrimeFive G) (h313 : GL83NormalElementaryRankFour)
    (h5 : ConfinementNonstrongFive G) : ConfinementNonstrong G := by
  intro p P M hloc hns H hH hrank
  rcases eq_three_or_five_le_of_d1Local hloc with rfl | hp5
  · exact absurd (stronglyEmbedded_three_of_pElement hS hD1 hFC hP5 h313 hloc) hns
  · exact h5 p P M hp5 hloc hns H hH hrank

theorem dichotomyRank4_of_five (hD1 : D1Rank4) (hFC : FullCoreRank4)
    (hP5 : ∀ (G : Type) [Group G] [Finite G], PElementPrimeFive G)
    (h313 : GL83NormalElementaryRankFour) (h5 : DichotomyRank4Five) : DichotomyRank4 := by
  intro G _ _ _ hnonab hK hchar he hpre
  exact strongOrExceptional_of_five ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
    (hD1 G hnonab hK hchar he hpre) (hFC G hnonab hK hchar he hpre) (hP5 G) h313
    (h5 G hnonab hK hchar he hpre)

theorem e2NonstrongRank4_of_five (hD1 : D1Rank4) (hFC : FullCoreRank4)
    (hP5 : ∀ (G : Type) [Group G] [Finite G], PElementPrimeFive G)
    (h313 : GL83NormalElementaryRankFour) (h5 : E2NonstrongRank4Five) : E2NonstrongRank4 := by
  intro G _ _ _ hnonab hK hchar he hpre
  exact confinementNonstrong_of_five ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
    (hD1 G hnonab hK hchar he hpre) (hFC G hnonab hK hchar he hpre) (hP5 G) h313
    (h5 G hnonab hK hchar he hpre)

theorem theoremCRankFour_of_five_endpoints
    (hD1 : D1Rank4)
    (hD2 : D2Rank4) (hFC : FullCoreRank4) (hDich : DichotomyRank4Five)
    (hE2 : E2NonstrongRank4Five) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (h313 : GL83NormalElementaryRankFour) (hRB : KFactReeBorelMaximal)
    (hRI : KFactReeInvolution) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h713 : GL83.I_7_13_1) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) : GLBUniqueFour G :=
  have hP5 : ∀ (G : Type) [Group G] [Finite G], PElementPrimeFive G :=
    fun _ _ _ => pElementPrimeFive_holds h243 h244 hsig h313 hRB hRI hInn hWC h713
  theoremCRankFour_of_node_endpoints' hD1 hD2 hFC
    (dichotomyRank4_of_five hD1 hFC hP5 h313 hDich)
    (e2NonstrongRank4_of_five hD1 hFC hP5 h313 hE2) h243 h244 hsig h313 hRB hRI hInn hWC h713
    G hnonab hK hchar he hpre

end CFSG.LocalAnalysis.RankFourTheoremC
