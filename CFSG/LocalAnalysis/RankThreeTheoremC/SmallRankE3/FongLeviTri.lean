module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcTriality
public import CFSG.RankThree.PartOne.K133X.D4
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

section

set_option linter.unusedSectionVars false


theorem tri_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩)) : False := by
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie ↥K (.trialityD4 q) := ⟨hv, e⟩
  have hmodel :=
    CFSG.RankThree.PartOne.K133X.chevalleyExceptionalModel_trialityD4_of_isoLie hq2 hiso
  obtain ⟨⟨-, hf, -⟩, hmod⟩ := hmodel
  obtain ⟨F, _, _, σ, hK, hσ, ⟨θ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmod
  have hK3 : Nat.card F = (2 ^ q.exponent) ^ 3 := hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 3 * q.exponent) (by rw [hK3, ← pow_mul, mul_comm])
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element TwistTag.D4.tag
  obtain ⟨⟨T₀, hT₀⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 F 2 σ w₀ hw₀
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport θ S.hpar T₀
  have hT₀' : (T₀ : Set ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) =
      (((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) :
          Subgroup ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) :
            Set ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) :=
    congrArg (fun H : Subgroup ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom) =>
      (H : Set ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom))) hT₀
  rw [hT₀'] at hN
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  obtain ⟨b, hb⟩ := Tri.exists_le_parabolic_of_normalizer_le σ hN hP
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzord : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hmem : (z' : ModGL TwistTag.D4.tag F) ∈
      graphFixedParabolic TwistTag.D4 F σ.toRingHom {b} := hb ⟨z', hz'P, rfl⟩
  have hdvd : p ∣ Nat.card ↥(graphFixedParabolic TwistTag.D4 F σ.toRingHom {b}) := by
    have h := orderOf_dvd_natCard
      (⟨(z' : ModGL TwistTag.D4.tag F), hmem⟩ :
        ↥(graphFixedParabolic TwistTag.D4 F σ.toRingHom {b}))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hzord] at h
  have h2 := Tri.two_le_pRank_of_dvd_card_parabolic σ hf hK3 hσ b S.hp S.hp5 hdvd
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  have hKr : CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv S.hp.one_lt θ] at h1
    exact h1
  omega

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
