module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcReeF4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.K128.SylowShapeRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.Ree
open CFSG.LieType.Ree.LargeReeInvolution (card_rankOneGroupOne card_rankOneGroupTwo rankOneGroupOne
  rankOneGroupTwo)

open CFSG.RankThree.LargeReeOrder (card_reeFixedBorel)


section

set_option linter.unusedSectionVars false


theorem ree_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  have hmodel := CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_reeF4_of_lie hv e
  obtain ⟨-, a, ha, -, F, _, _, _, hF, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hmodel
  have hp : p.Prime := S.hp
  have hp5 : 5 ≤ p := S.hp5
  have hp2 : p ≠ 2 := by omega
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨T₀, hT₀⟩ := (large_Ree_Sylow_opposition F4 a F w₀ hw₀).1
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport θ S.hpar T₀
  have hB : (F4.reeFixedBorel F a).subgroupOf (F4.reeGamma F a) ≤
      Subgroup.normalizer ((T₀ : Subgroup ↥(F4.reeGamma F a)) : Set ↥(F4.reeGamma F a)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hT₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1
      (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hb)) x
  have hBK₀ := hB.trans hN
  have hBA : F4.reeFixedBorel F a ≤ P.map (F4.reeGamma F a).subtype :=
    fun x hx => ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩, hBK₀ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  have hne' : P.map (F4.reeGamma F a).subtype ≠ F4.reeGamma F a := by
    intro h
    apply hP
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL F4.tag F) ∈ P.map (F4.reeGamma F a).subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzord : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hordc : orderOf (z' : ModGL F4.tag F) = p := by
    rw [Subgroup.orderOf_coe]
    exact hzord
  have hzA : (z' : ModGL F4.tag F) ∈ P.map (F4.reeGamma F a).subtype := ⟨z', hz'P, rfl⟩
  have hKr : CFSG.Open.pRank p (⊤ : Subgroup ↥(F4.reeGamma F a)) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt θ] at h1
    exact h1
  have hpq : ¬ p ∣ Nat.card F - 1 := fun h => by
    have := two_le_pRank_reeGamma_of_dvd_sub_one hp hF h
    omega
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hpN : ¬ p ∣ 2 ^ (2 * a + 1) := fun h => by
    have h3 := hp.dvd_of_dvd_pow h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3
    omega
  have hpq' : ¬ p ∣ 2 ^ (2 * a + 1) - 1 := by
    rw [hF] at hpq
    exact hpq
  have hphi2 : p ∣ 2 ^ (2 * a + 1) + 1 → False := fun hd => by
    have he : 1 ≤ (2 ^ (2 * a + 1) + 1).factorization p :=
      hp.factorization_pos_of_dvd (by positivity) hd
    have hrank := CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he
      (CFSG.RankThree.PartOne.K128.sylowShape_ree_phi2 hF hp hp5 hd)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
    have h := le_trans hrank hKr
    omega
  have hphi4 : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 → False := fun hd => by
    have he : 1 ≤ ((2 ^ (2 * a + 1)) ^ 2 + 1).factorization p :=
      hp.factorization_pos_of_dvd (by positivity) hd
    have hrank := CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he
      (CFSG.RankThree.PartOne.K128.sylowShape_ree_phi4 hF hp hp5 hd)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
    have h := le_trans hrank hKr
    omega
  have hsq : (2 ^ (2 * a + 1)) ^ 2 - 1 = (2 ^ (2 * a + 1) - 1) * (2 ^ (2 * a + 1) + 1) := by
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ (2 * a + 1) = r + 1 := ⟨2 ^ (2 * a + 1) - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  rcases eq_borel_or_eq_reeLocalParabolic hF hBA (Subgroup.map_subtype_le P) hne' with h | ⟨j, hj⟩
  ·
    have hmem : (z' : ModGL F4.tag F) ∈ F4.reeFixedBorel F a := by
      rw [← h]
      exact hzA
    have hpB : p ∣ Nat.card (F4.reeFixedBorel F a) := by
      have h1 := orderOf_dvd_natCard
        (⟨(z' : ModGL F4.tag F), hmem⟩ : ↥(F4.reeFixedBorel F a))
      rwa [Subgroup.orderOf_mk, hordc] at h1
    rw [card_reeFixedBorel hF] at hpB
    rcases (Nat.Prime.dvd_mul hp).1 hpB with h1 | h2
    · exact hpN (hp.dvd_of_dvd_pow h1)
    · exact hpq' (hp.dvd_of_dvd_pow h2)
  ·
    have hmem : (z' : ModGL F4.tag F) ∈ F4.reeLocalParabolic F a j := by
      rw [← hj]
      exact hzA
    have hpP : p ∣ Nat.card (F4.reeLocalParabolic F a j) := by
      have h1 := orderOf_dvd_natCard
        (⟨(z' : ModGL F4.tag F), hmem⟩ : ↥(F4.reeLocalParabolic F a j))
      rwa [Subgroup.orderOf_mk, hordc] at h1
    have hpM := dvd_card_reeLocalBlock_of_dvd_card_parabolic hF hp hp2 hpq j hpP
    obtain ⟨hM0, hM1⟩ :=
      CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hF
    obtain ⟨j, hj'⟩ := j
    have hj2 : j < 2 := hj'
    interval_cases j
    · rw [show F4.reeLocalBlock F a ⟨0, hj'⟩ = rankOneGroupOne F a from hM0.1,
        card_rankOneGroupOne hF] at hpM
      rcases (Nat.Prime.dvd_mul hp).1 hpM with h1 | h2
      · exact hpN h1
      · rw [hsq] at h2
        rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h4
        · exact hpq' h3
        · exact hphi2 h4
    · rw [show F4.reeLocalBlock F a ⟨1, hj'⟩ = rankOneGroupTwo F a from hM1.1,
        card_rankOneGroupTwo ha hF] at hpM
      rcases (Nat.Prime.dvd_mul hp).1 hpM with h1 | h2
      · rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h4
        · exact hpN (hp.dvd_of_dvd_pow h3)
        · exact hpq' h4
      · exact hphi4 h2

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
