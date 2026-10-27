module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSpor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusSporadic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

theorem kFact2401Spor_holds :
    KFact2401Spor := by
  intro A _ _ L s hL h2
  by_cases h11 : s = .M11
  · exact Or.inr h11
  left
  by_cases hJ1 : s = .J1
  · exfalso
    subst hJ1
    obtain ⟨e⟩ := hL
    obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
    have hLc : Nat.card ↥L = 175560 := by
      rw [Nat.card_congr (e.trans f.symm).toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    obtain ⟨E, hEL, -, hEc⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 L (by omega)
    have hdvd : Nat.card E ∣ Nat.card L := Subgroup.card_dvd_of_le hEL
    rw [hEc, hLc] at hdvd
    have h9 : 3 ^ 2 ∣ 3 ^ CFSG.Open.pRank 3 L := pow_dvd_pow 3 h2
    have := h9.trans hdvd
    norm_num at this
  · intro E hE J hJ
    obtain ⟨e⟩ := hL
    obtain ⟨T, hT⟩ := hE.exists_sylow_eq_subgroupOf
    have hGLB := CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.sporGammaOneAt_three s h11 hJ1
      ↥L ⟨e⟩ T
    have hle : CFSG.Open.GLBCore 3 1 (T : Subgroup ↥L) ≤ J.subgroupOf L := by
      refine sSup_le ?_
      rintro N ⟨Q, hQT, hQ1, rfl⟩
      have hQne : Q ≠ ⊥ := by
        intro hbot
        obtain ⟨E', hE'Q, -, hcard⟩ :=
          CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 Q (by omega)
        have hE' : E' = ⊥ := le_bot_iff.mp (hbot ▸ hE'Q)
        rw [hE', Subgroup.card_bot] at hcard
        have h3 : 3 ^ 1 ≤ 3 ^ CFSG.Open.pRank 3 Q := Nat.pow_le_pow_right (by norm_num) hQ1
        omega
      have hSE : Q.map L.subtype ≤ E := by
        rintro _ ⟨y, hy, rfl⟩
        have : y ∈ E.subgroupOf L := hT ▸ hQT hy
        exact this
      have hSne : Q.map L.subtype ≠ ⊥ := by
        intro hbot
        exact hQne ((Subgroup.map_eq_bot_iff_of_injective Q L.subtype_injective).mp hbot)
      have hJS := hJ (Q.map L.subtype) hSE hSne
      intro g hg
      have h1 : (g : A) ∈ normalizer ((Q.map L.subtype : Subgroup A) : Set A) := by
        have h2 : (Q.map L.subtype).subgroupOf L = Q :=
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q
        have h4 : g ∈ (normalizer ((Q.map L.subtype : Subgroup A) : Set A)).subgroupOf L := by
          rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le Q), h2]
          exact hg
        exact h4
      exact hJS ⟨h1, g.2⟩
    have htop : J.subgroupOf L = ⊤ := top_unique (hGLB ▸ hle)
    exact Subgroup.subgroupOf_eq_top.mp htop

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
