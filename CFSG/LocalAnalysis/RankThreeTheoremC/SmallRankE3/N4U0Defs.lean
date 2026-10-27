module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5LargeSteps
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def SlotP614NormalizerRankLargeU0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ¬ HasPrimeConstraint (G := M) p →
        ∀ T : Subgroup G, IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T →
          CFSG.Open.pRank p (P : Subgroup G) ≤ CFSG.Open.pRank p (M ⊓ normalizer (T : Set G))

@[expose] def SlotP614StepL617LargeU0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ∀ H S : Subgroup G, Fail614OptimalGen p M x z H S → rankThreePrimeCore p H ≤ M

@[expose] def SlotP614CoreLargeU0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ∀ H S : Subgroup G, Fail614OptimalGen p M x z H S → rankThreePrimeCore p H ≤ M →
          (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
            ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) → False

theorem SlotP614NormalizerRankLarge.toU0 (h : SlotP614NormalizerRankLarge) :
    SlotP614NormalizerRankLargeU0 :=
  fun G _ _ hS hD1 _ => h G hS hD1

theorem SlotP614StepL617Large.toU0 (h : SlotP614StepL617Large) : SlotP614StepL617LargeU0 :=
  fun G _ _ hS hD1 _ => h G hS hD1

theorem slotP614LargeD2_of_stepsU0 (hnr : SlotP614NormalizerRankLargeU0)
    (h617 : SlotP614StepL617LargeU0) (hΩ : SlotP614OmegaULarge) (hcore : SlotP614CoreLargeU0) :
    SlotP614LargeD2 := by
  intro G _ _ hS hD1 hD2 hU0 p hp3 P M x z T hf S₀ hS₀S hS₀1 hzS₀
  have hsit := hf.situation
  have hp : p.Prime := hf.prime
  have hp2 : p ≠ 2 := hf.ne_two
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  have hx := hf.point
  have hz := hf.central
  have hS₀T : S₀ ≤ T := hS₀S.trans inf_le_left
  have hS₀2 : IsPGroup 2 S₀ := hf.sylowTwo.isPGroup.to_le hS₀T
  have hxc : x ∈ centralizer (S₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hS₀S hs : s ∈ T ⊓ centralizer ({x} : Set G)).2
  have hxS₀ : zpowers x ≤ normalizer (S₀ : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hxc)
  have hBS₀ : zpowers x ⊔ zpowers z ≤ normalizer (S₀ : Set G) := sup_le hxS₀ hzS₀
  by_contra hHM
  have hnr' : Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z) := by
    by_cases hα : HasPrimeConstraint (G := M) p
    · exact fail614GNormalizerRank_of_alpha hS hsit hα hx hz
    · exact hnr G hS hD1 hU0 p hp5 P M hsit x z hx hz hα
  obtain ⟨S', hSS', hS'⟩ := exists_isMaxTwoInvariantIn_of_le
    (B := zpowers x ⊔ zpowers z) (X := normalizer (S₀ : Set G) ⊓ M) (S := S₀)
    ⟨le_inf le_normalizer (hS₀T.trans hf.T_le_M), hS₀2, hBS₀⟩
  have hpair : Prop614Pair M (zpowers x ⊔ zpowers z) (normalizer (S₀ : Set G)) S' :=
    ⟨⟨S₀, hS₀1, hS₀2, rfl⟩, hBS₀, hHM, hS', ne_bot_of_le_ne_bot hS₀1 hSS'⟩
  obtain ⟨H₀, S₁, hopt⟩ := exists_fail614GOptimal hS hD1 hsit hx hz hnr' ⟨_, S', hpair⟩
  have hO : rankThreePrimeCore p H₀ ≤ M := h617 G hS hD1 hU0 p hp5 P M hsit x z hx hz H₀ S₁ hopt
  have hΩ' : ∀ Q : Subgroup G, Q ≤ H₀ → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z := fun Q hQH hQp hBQ q hqQ hq1 =>
    omega_le_of_omegaU hS hD2 hU0 hp5 hsit hopt hQH hQp hBQ hqQ hq1
      (hΩ G hS hD1 p hp5 P M hsit x z hx hz H₀ S₁ hopt hO Q hQH hQp hBQ)
  exact hcore G hS hD1 hU0 p hp5 P M hsit x z hx hz H₀ S₁ hopt hO hΩ'

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
