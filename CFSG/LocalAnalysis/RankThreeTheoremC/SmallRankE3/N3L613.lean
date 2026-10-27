module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Comp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem three_rank_normalizer_le {G : Type} [Group G] [Finite G] (hrank : evenRank G = 3)
    (M : Subgroup G) :
    ∀ Q : Subgroup ↥M, Q ≠ ⊥ → IsPGroup 2 Q → Open.pRank 3 (normalizer (Q : Set ↥M)) ≤ 3 := by
  intro Q hQ hQ2
  have hQ' : Q.map M.subtype ≠ ⊥ := by
    intro h
    apply hQ
    exact (Subgroup.map_eq_bot_iff_of_injective Q M.subtype_injective).mp h
  have hloc : IsTwoLocal (normalizer ((Q.map M.subtype : Subgroup G) : Set G)) :=
    ⟨Q.map M.subtype, hQ', hQ2.map M.subtype, rfl⟩
  have h1 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) _ hloc
  have h2 : (normalizer (Q : Set ↥M)).map M.subtype ≤
      normalizer ((Q.map M.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n ∈ normalizer (Q : Set ↥M) := hn
    rw [Subgroup.mem_normalizer_iff] at hn'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hh
      exact Subgroup.mem_map.mpr ⟨n * q * n⁻¹, (hn' q).mp hq, rfl⟩
    · intro hh
      obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hh
      have hqe' : (q : G) = (n : G) * h * (n : G)⁻¹ := hqe
      have hh' : h = ((n⁻¹ * q * n : ↥M) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hqe']
        group
      have hmem : n⁻¹ * q * n ∈ Q := by
        have := (hn' (n⁻¹ * q * n)).mpr (by
          have e : n * (n⁻¹ * q * n) * n⁻¹ = q := by group
          rw [e]; exact hq)
        exact this
      rw [hh']
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have h3 := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) h2
  rw [pRank_map_subtype (by norm_num : 1 < 3)] at h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
