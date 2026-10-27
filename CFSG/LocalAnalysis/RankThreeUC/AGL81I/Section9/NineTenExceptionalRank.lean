module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFive
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LieType.OutStructureFiveDispatch
public import CFSG.LieType.OutStructureThreeRankQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

theorem NineSettingGen.false_of_four_le_pRank_three_of_le {G : Type} [Group G] [Finite G]
    {M Q H E : Subgroup G} {p : ℕ} (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) {J : Subgroup G} (hJH : J ≤ H) (hJM : J ≤ M)
    (hJ3 : 4 ≤ CFSG.Open.pRank 3 J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTne : CFSG.pCore 2 ↥H ≠ ⊥ := by
    intro hbot
    have hpcof : pCoreOf 2 H = ⊥ := by
      rw [pCoreOf, hbot, Subgroup.map_bot]
    have hcen : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (bot_le : (⊥ : Subgroup G) ≤ Subgroup.center G)
    have hcl := (mem_H2Fam_iff.mp hH2).2.2.2
    rw [hpcof, hcen, inf_top_eq] at hcl
    exact h.not_le (hcl.trans bot_le)
  have hO : pCoreOf 2 H ≠ ⊥ := fun hbot =>
    hTne ((Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥H) H.subtype_injective).mp hbot)
  have htop : IsTwoLocal (⊤ : Subgroup ↥H) := by
    refine ⟨CFSG.pCore 2 ↥H, hTne, CFSG.pCore_isPGroup, ?_⟩
    exact (show ⊤ = Subgroup.normalizer ((CFSG.pCore 2 ↥H : Subgroup ↥H) : Set ↥H) from by
      rw [Subgroup.normalizer_eq_top])
  have hH3 : CFSG.Open.pRank 3 H ≤ rankThreeLocalRank 3 H :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) H).le.trans
      (local_pRank_le_localRank (G := ↥H) 3 (by norm_num) (⊤ : Subgroup ↥H) htop)
  have hJ3H : CFSG.Open.pRank 3 J ≤ CFSG.Open.pRank 3 H :=
    CFSG.SectionRank.pRank_mono (by norm_num) hJH
  have hJHM : CFSG.Open.pRank 3 J ≤ CFSG.Open.pRank 3 (H ⊓ M) :=
    CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hJH hJM)
  have h95 := (h.nineFiveGen hp).2.2 (Or.inl hO) (by omega)
  omega

theorem NineSettingGen.not_le_of_outFiveExceptional
    (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G] [Finite G]
    {M Q H E : Subgroup G} {p : ℕ} (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (hp3 : 3 < p) {C : Subgroup (StarGroup p H)}
    (hC : CFSG.IsComponent C)
    (hex : CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p)
    {J : Subgroup G} (hJ : IsPComponentIn p J H) (hJC : starImg p H J = C) : ¬ J ≤ M := by
  intro hJM
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) h.prime
    omega
  obtain ⟨t, N, r, f, hcl, ht, hN⟩ : ∃ (t : CFSG.Open.StatedLieTag) (N r f : ℕ),
      CFSG.Open.StatedClassicalModel (↥C ⧸ Subgroup.center ↥C) t N r f ∧
        (t = .PSL ∨ t = .PSU) ∧ 2 * p + 1 ≤ N := by
    rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
    · exact ⟨.PSL, N, r, f, hcl, Or.inl rfl, hN⟩
    · exact ⟨.PSU, N, r, f, hcl, Or.inr rfl, hN⟩
  have hsimple : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC.1.2.1
  let ρ : ↥J →* StarGroup p H :=
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp (Subgroup.inclusion hJ.1)
  have hρC : ∀ x : ↥J, ρ x ∈ C := fun x => by
    rw [← hJC]
    exact ⟨Subgroup.inclusion hJ.1 x, x.2, rfl⟩
  let φ : ↥J →* ↥C ⧸ Subgroup.center ↥C :=
    (QuotientGroup.mk' (Subgroup.center ↥C)).comp (ρ.codRestrict C hρC)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    have hc : (c : StarGroup p H) ∈ starImg p H J := by
      rw [hJC]
      exact c.2
    obtain ⟨z, hz, hzc⟩ := hc
    exact ⟨⟨(z : G), hz⟩, congrArg (QuotientGroup.mk' (Subgroup.center ↥C))
      (Subtype.ext hzc)⟩
  have h4 := CFSG.LieType.OutStructure.four_le_pRank_three_of_surjective_classical hGA
    hC.1.2.2 hcl ht (by omega) φ hφ
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup J] at h4
  exact h.false_of_four_le_pRank_three_of_le hH2 hp hJ.1 hJM h4

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
