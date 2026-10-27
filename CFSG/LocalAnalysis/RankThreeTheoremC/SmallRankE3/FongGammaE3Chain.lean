module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaPara
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGPara
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQuot
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section Para

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem n5_false_of_not_sylow_E3 (c : KQCfg A p Kb Sb Bb Mb z) (hchev : IsChevSimple 2 ↥Kb)
    (h131 : KFact131) (hne : Sb ⊓ Kb ≠ ⊥)
    (hns : ¬ CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Kb) Kb) (hPara : KFactGammaParaE3)
    (hnb : ∀ b ∈ Bb, b ≠ 1 → ¬ ∀ k ∈ Kb, b * k = k * b)
    (hrk : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.Open.pRank ℓ Kb ≤ 3)
    (hcent : ∀ y ∈ Bb, y ∉ zpowers z →
      CFSG.HallHigman.IsPSolvable p ↥(Mb ⊓ centralizer ({y} : Set A))) : False := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hK₀par := KGQ.isParabolicTwo_inf c hchev h131 hne
  have hzM : z ∈ Mb := c.cover_Z (Subgroup.le_normalizer (Subgroup.mem_zpowers z))
  have hzK₀ : z ∈ Kb ⊓ Mb := ⟨c.z_mem_K, hzM⟩
  have hK₀ne : Kb ⊓ Mb ≠ Kb := fun h => c.not_le (h.symm.le.trans inf_le_right)
  have hSyl := KGQ.not_le_primeCore_of_not_sylow c hchev h131 hne hns
  obtain ⟨y, hyB, hyz, hy⟩ := hPara A Kb (Kb ⊓ Mb) Bb z p hchev c.prime c.five_le c.rank
    c.z_order hzK₀ hK₀par hK₀ne hSyl c.B_elem c.B_card c.z_mem_B c.B_le_K
    (n5_B_le_normalizer_inf c) hnb hrk
  exact hy (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
    (hcent y hyB hyz) (inf_le_inf_right _ inf_le_right))

end Para

theorem n5_pRank_img_le_three {G : Type} [Group G] [Finite G]
    (hS : CFSG.LocalAnalysis.RankThreeTheoremC.Setting G) {H D : Subgroup G}
    [(D.subgroupOf H).Normal] (L : Subgroup G) (hH : IsTwoLocal H) (hD2 : IsPGroup 2 D) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.Open.pRank ℓ (KGC.img H D L) ≤ 3 := by
  intro ℓ hℓ hℓ2
  have h1 : CFSG.Open.pRank ℓ (KGC.img H D L) ≤
      CFSG.Open.pRank ℓ (⊤ : Subgroup (KGC.QA H D)) :=
    CFSG.SectionRank.pRank_mono hℓ.one_lt le_top
  have hD2' : IsPGroup 2 (D.subgroupOf H) := hD2.comap_subtype
  have hDℓ : ¬ ℓ ∣ Nat.card (D.subgroupOf H) :=
    CFSG.QuasithinUnique.K1.not_dvd_card_of_isPGroup_two hD2' hℓ hℓ2
  have h2 := CFSG.QuasithinUnique.K1.pRank_top_quotient_le H (D.subgroupOf H) hℓ hDℓ
  have h3 := local_pRank_le_evenRank ℓ hℓ hℓ2 H hH
  rw [hS.rank] at h3
  exact h1.trans (h2.trans h3)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
