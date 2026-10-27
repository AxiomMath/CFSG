module

public import CFSG.LocalAnalysis.RankFourTheoremC.Assembly
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers

@[expose] def FullCoreLocality (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M → GLBCore p 2 (P : Subgroup G) ≤ M

@[expose] def ConfinementNonstrong (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M → ¬ GLBStronglyEmbedded p M →
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

@[expose] def FullCoreRank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → FullCoreLocality G

@[expose] def DeltaTwoRank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → GLBDeltaTwo G

@[expose] def E2NonstrongRank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → ConfinementNonstrong G

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_of_stronglyEmbedded {p : ℕ} {M R : Subgroup G}
    (hs : GLBStronglyEmbedded p M) (hRM : R ≤ M) (hpR : p ∣ Nat.card R) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hconj : R.map (MulAut.conj g).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hRconj : R ≤ GLBConj g M := by
    intro x hx
    have hgx : g * x * g⁻¹ ∈ R := hconj ▸ Subgroup.mem_map_of_mem _ hx
    exact ⟨g * x * g⁻¹, hRM hgx, by simp [mul_assoc]⟩
  exact hs.2.2 g hgM (hpR.trans (Subgroup.card_dvd_of_le (le_inf hRM hRconj)))

omit [Finite G] in
theorem isElemAbelian_mono {p : ℕ} {E Q : Subgroup G} (hE : IsElemAbelian p E) (hQE : Q ≤ E) :
    IsElemAbelian p Q := CFSG.Open.IsElemAbelian.mono hE hQE

theorem pRank_eq_of_isElemAbelian {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQ : IsElemAbelian p Q) {k : ℕ} (hk : Nat.card Q = p ^ k) : pRank p Q = k := by
  apply le_antisymm
  · obtain ⟨E, hEQ, -, hEcard⟩ := pRank_attained p hp Q
    have hle : p ^ pRank p Q ≤ p ^ k := hEcard ▸ hk ▸ Subgroup.card_le_of_le hEQ
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  · exact le_csSup (pRank_bddAbove p hp Q) ⟨Q, le_rfl, hQ, hk⟩

theorem dvd_card_of_one_le_pRank {p : ℕ} (hp : p.Prime) {R : Subgroup G}
    (hR : 1 ≤ pRank p R) : p ∣ Nat.card R := by
  obtain ⟨E, hER, -, hEcard⟩ := pRank_attained p hp R
  have hdvd : p ∣ Nat.card E := hEcard ▸ dvd_pow_self p (by omega)
  exact hdvd.trans (Subgroup.card_dvd_of_le hER)

theorem le_of_stronglyEmbedded (hD2 : D2For G) {p : ℕ} (hp : p ∈ GLBBetaFour G) (P : Sylow p G)
    {M : Subgroup G} (hM : GLBIsMaxTwoLocal M) (hPM : GLBCore p 2 (P : Subgroup G) ≤ M)
    (hs : GLBStronglyEmbedded p M) {H : Subgroup G} (hH : IsTwoLocal H)
    (h2 : 2 ≤ pRank p (H ⊓ M)) : H ≤ M := by
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨E, hEHM, hE, hEcard⟩ := pRank_attained p hp.1 (H ⊓ M)
  have hdvd : p ^ 2 ∣ Nat.card E := hEcard ▸ pow_dvd_pow p h2
  obtain ⟨Q, hQcard, -, hQE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp.1 (H := ⊥) (L := E) (by simp) hdvd bot_le
  have hQHM : Q ≤ H ⊓ M := hQE.trans hEHM
  have hQM : GLBCore p 1 Q ≤ M := by
    refine (fullCore_le_iff p 1 Q M).mpr fun R hRQ hR1 => ?_
    exact normalizer_le_of_stronglyEmbedded hs (hRQ.trans (hQHM.trans inf_le_right))
      (dvd_card_of_one_le_pRank hp.1 hR1)
  exact hD2 p hp P M hM hPM Q (IsPGroup.of_card hQcard)
    (pRank_eq_of_isElemAbelian hp.1 (isElemAbelian_mono hE hQE) hQcard) hQM H hH
    (hQHM.trans inf_le_left)

theorem deltaOne_of_fullCore (hpre : GLBPreuniqueness G) (hFC : FullCoreLocality G) :
    GLBDeltaOne G := by
  intro q hq P
  obtain ⟨Y, hY, hWY⟩ := (hpre q hq).2 P
  obtain ⟨L, hYL, hL⟩ := exists_maximal_twoLocal hY
  exact ⟨L, hL.1, hFC q P L ⟨hq, hL, hWY.trans hYL⟩⟩

theorem confinementAtCore_of_nonstrong (hD2 : D2For G) (hE1 : AlmostStrongAtCore G)
    (hE2 : ConfinementNonstrong G) : ConfinementAtCore G := by
  intro p P M hloc H hH h2
  by_cases hs : GLBStronglyEmbedded p M
  · obtain ⟨-, -, -, P', -, hP'M, -⟩ := hE1 p P M hloc
    exact le_of_stronglyEmbedded hD2 hloc.beta P' hloc.maxLocal hP'M hs hH h2
  · exact hE2 p P M hloc hs H hH h2

theorem theoremCRankFour_of_refined_endpoints (hD1 : D1Rank4) (hD2 : D2Rank4)
    (hFC : FullCoreRank4) (hδ₂ : DeltaTwoRank4) (hE1 : E1Rank4) (hE2 : E2NonstrongRank4)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hpre : GLBPreuniqueness G) : GLBUniqueFour G := by
  have hD2G : D2For G := hD2 G hnonab hK hchar he
    (deltaOne_of_fullCore hpre (hFC G hnonab hK hchar he hpre))
    (hδ₂ G hnonab hK hchar he hpre)
  exact uniqueFour_of_atCore hpre (hD1 G hnonab hK hchar he hpre) (hE1 G hnonab hK hchar he hpre)
    (confinementAtCore_of_nonstrong hD2G (hE1 G hnonab hK hchar he hpre)
      (hE2 G hnonab hK hchar he hpre))

end CFSG.LocalAnalysis.RankFourTheoremC
