module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Shape
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Case1
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Case2Main
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G} {x : G}

theorem normalizer_le_of_plane_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) {U : Subgroup G}
    (hUP : U ≤ (P : Subgroup G)) (hUe : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hxU : x ∈ U) {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hUY : U ≤ normalizer (Y : Set G))
    (hYO : IsSylowOf 2 (Y ⊓ rankThreePrimeCore p M) (rankThreePrimeCore p M)) :
    normalizer (Y : Set G) ≤ M := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨n, f, W, hB⟩ := exists_borelDataP hp5 hK hG hloc hType h
  have hS := shape_p hp5 hK hG hloc hType h
  obtain ⟨t₀, ht₀, rfl⟩ := hB.exists_plane_eq hUP hUe hUc hxU hS.abelian
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  obtain ⟨hOle, hMO, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hO : ¬ p ∣ Nat.card (rankThreePrimeCore p M) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mp hOcop
  have hM2 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P₂, hP₂1, hP₂2, hP₂M⟩ := hloc.maxLocal.1
    have hP₂le : P₂ ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP₂M ▸ Subgroup.le_normalizer)
        hP₂M.le hP₂2
    intro h0
    exact hP₂1 (le_bot_iff.1 (hP₂le.trans h0.le))
  have hO2R : pCoreOf 2 M ≤ rankThreePrimeCore p M :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore hp2 M
  have hO2 : 2 ∣ Nat.card (rankThreePrimeCore p M) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hM2 (Subgroup.card_eq_one.mp (by simpa using hk))
    exact (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hO2R)
  have hQM : hB.QK ≤ M := hB.QK_le_P.trans hPM
  have hn2 : 2 ≤ CFSG.Open.pRank p hB.QK := by
    have h1 := CFSG.SectionRank.le_pRank hp.out.one_lt (le_refl hB.QK) hB.QK_isElemAbelian
      hB.card_QK
    have := hB.three_le
    omega
  have hCM : centralizer (hB.QK : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (hB.QK : Set G)).trans
      (normalizer_le_of_two_le_pRank hG.fc hloc hB.QK_isPGroup hQM hn2)
  have hcont : ∀ m ∈ M, ∀ q ∈ hB.QK, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ rankThreePrimeCore p M :=
    conj_mem_sup_p hK hG hloc h hB hS
  have hRM : M ≤ normalizer ((hB.QK ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) :=
    hB.le_normalizer_QK_sup hS hPM hMO hcont
  have hD1 : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M :=
    fun H hH hr => hG.d1 p hloc.beta P M hloc.maxLocal hloc.core H hH hr
  exact hB.normalizer_le_of_normal hS hO hO2 hMO hOle hQM hRM hCM (hPM h.mem) hD1 ht₀ hY2 hYM hUY
    hYO

end CFSG.LocalAnalysis.RankFourTheoremC.P5
