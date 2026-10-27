module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTenCfg
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.RankThree.PartTwo.Sec19.Item194Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81ElevenElevenRankOneJZeroCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    Open.pRank p K ≤ 1 → 3 ≤ Open.pRank p H → ¬ (p = 3 ∧ IsAltTwoP 3 K) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L →
      ∃ A : Subgroup G, A ≤ H ∧ IsAGLQ p M A ∧
        (∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
          (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) ∧
        ∀ b ∈ A, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)

variable (G) in
@[expose] def AGL81ElevenElevenOtherJZeroCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    (Open.pRank p K ≤ 1 → 3 ≤ Open.pRank p H) → ¬ (p = 3 ∧ IsAltTwoP 3 K) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L →
      ∃ A : Subgroup G, A ≤ H ∧ IsAGLQ p M A ∧
        (∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
          (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) ∧
        (∀ b ∈ A, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) ∧
        (2 ≤ Open.pRank p K → A = d1LiftX p H Q K)

theorem commJZero_of_commutator_le {M H L A : Subgroup G} (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hAH : A ≤ H) (hAM : A ≤ M)
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) :
    ∀ b ∈ A, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := by
  intro b hb x hx
  have hxL : x ∈ L := ((jZero_le H L).trans inf_le_right) hx
  have hT : b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 L := hAL (Subgroup.commutator_mem_commutator hb hxL)
  have hbN : b ∈ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hAH hb)) y
    have e2 := Subgroup.mem_normalizer_iff.mp (hMn (hAM hb)) y
    exact ⟨fun hy => ⟨e1.mp hy.1, e2.mp hy.2⟩, fun hy => ⟨e1.mpr hy.1, e2.mpr hy.2⟩⟩
  have hJ : b * x * b⁻¹ * x⁻¹ ∈ jZero H L :=
    (jZero H L).mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_jZero H L hbN) x).mp hx)
      ((jZero H L).inv_mem hx)
  exact CFSG.RankThree.PartTwo.Sec19.Item194Proof.inf_pCoreOf_le
    ((jZero_le H L).trans inf_le_right) ⟨hJ, hT⟩

theorem agl81ElevenElevenOtherJZeroCfg_of (h2 : AGL81ElevenElevenRankTwoCfg G)
    (h1 : AGL81ElevenElevenRankOneJZeroCfg G) : AGL81ElevenElevenOtherJZeroCfg G := by
  intro hS p P M H Q K hσ hd hnc hrk hA6 L hL hLn hno
  by_cases hK : 2 ≤ Open.pRank p K
  · obtain ⟨hQ, hAL⟩ := h2 hS p P M H Q K hσ hd hnc hK hA6 L hL hLn hno
    have hAH : d1LiftX p H Q K ≤ H := (d1LiftX_le p H Q K).trans hd.le_H
    exact ⟨d1LiftX p H Q K, hAH, hQ, hd.sylowK_d1LiftX,
      commJZero_of_commutator_le hL.le hLn hAH hQ.1 hAL, fun _ => rfl⟩
  · push Not at hK
    obtain ⟨A, hAH, hAQ, hsyl, hAJ⟩ := h1 hS p P M H Q K hσ hd hnc (by omega) (hrk (by omega))
      hA6
      L hL hLn hno
    exact ⟨A, hAH, hAQ, hsyl, hAJ, fun h => absurd h (by omega)⟩

theorem agl81ElevenFiveAt_of_jZero (h6 : AGL81ElevenSixCfg G) (h11 : AGL81ElevenElevenCfg G)
    (hOther : AGL81ElevenElevenOtherJZeroCfg G) (h98 : AGL81NineEightTwo G)
    (h9 : AGL81NineCompetitorQ G) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hKC : KFactNineThreeComponentL34)
    (hKR : KFactL34ThreeRankTwo) : AGL81ElevenFiveAt G := by
  intro hS p P M H Q K hσ hd hnc hrk L hL
  obtain ⟨hXM, hlist⟩ := hd.nineThree h9 hS
  have hleft : AGL81ElevenFiveOne p H K L →
      p = 3 ∧ IsComponentOf K ⊤ ∧
        ((IsAltTwoP 3 K ∧ ∃ I₀ ∈ cZero (H ⊓ L),
            CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre p H K) ∨
          (IsLinThreeFour K ∧ IsAGLQ 3 M (d1LiftX p H Q K) ∧
            ¬ Hyp111B3 p H (d1LiftX p H Q K) K)) := by
    rintro ⟨hp3, hA, hI⟩
    exact ⟨hp3, hd.isComponentOf_of_simple (isSimpleGroup_of_isAltTwoP_three hA),
      Or.inl ⟨hA, hI⟩⟩
  rcases h6 hS p P M H Q K hσ hd.toCfg hnc L hL with hLn | h5
  · by_cases h5 : AGL81ElevenFiveOne p H K L
    · exact hleft h5
    by_cases hA6 : p = 3 ∧ IsAltTwoP 3 K
    ·
      exfalso
      obtain ⟨rfl, hA⟩ := hA6
      obtain ⟨hA₀Q, hA₀L⟩ := h11 hS P M H Q K hσ hd.toCfg hA hnc L hL hLn h5
      have hsyl := hd.sylowK_d1LiftX
      have hAH : d1LiftX 3 H Q K ≤ H := (d1LiftX_le 3 H Q K).trans hd.pair.le_H
      have hb3 : Hyp111B3 3 H (d1LiftX 3 H Q K) K := by
        rcases hd.b3_or_isLinThreeFour h98 hKC hS hlist hA₀Q hAH hsyl with h | ⟨-, hL34⟩
        · exact h
        · exfalso
          have h1 := Hyp111.card_of_isLinThreeFour hL34
          rw [card_of_isAltTwoP_three hA] at h1
          norm_num at h1
      exact hd.false_of_rebase hS hCGT hD2 hXM hAH hA₀Q hsyl hb3 hL hLn hA₀L
    ·
      obtain ⟨A, hAH, hAQ, hsylA, hAJ, hA0⟩ :=
        hOther hS p P M H Q K hσ hd.toCfg hnc hrk hA6 L hL hLn h5
      by_cases hb3 : Hyp111B3 p H A K
      · exact ((hd.toCfgAt hAQ hAH hsylA hb3).false_of_comm_jZero_of_b3 hS hCGT hD2 h1033 hXM hL
          hLn hAJ).elim
      · rcases hd.b3_or_isLinThreeFour h98 hKC hS hlist hAQ hAH hsylA with h | ⟨hp3, hL34⟩
        · exact absurd h hb3
        · subst hp3
          have hAeq : A = d1LiftX 3 H Q K := hA0 (hKR _ K hL34)
          subst hAeq
          exact ⟨rfl, hd.isComponentOf_of_simple (isSimpleGroup_of_isLinThreeFour' hL34),
            Or.inr ⟨hL34, hAQ, hb3⟩⟩
  · exact hleft h5

end CFSG.LocalAnalysis.RankThreeTheoremC
