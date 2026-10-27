module

public import CFSG.Foundations.KCoreClosure
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open
open scoped Pointwise

theorem openIsKGroup_sup_pGroup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup G} (hK : CFSG.Open.IsKGroup ↥K) (hB : IsPGroup p B) (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.IsKGroup ↥(K ⊔ B) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK' : CFSG.IsKGroup ↥K :=
    CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hK
  set M : Subgroup G := K ⊔ B with hM
  have hKM : K ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hBN
  haveI hKn : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMN
  set φ : ↥M →* ↥M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M) with hφ
  have hBp : IsPGroup p (B.subgroupOf M) := hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm
  have hdecomp : ∀ m : ↥M, ∃ b : ↥M, b ∈ B.subgroupOf M ∧ φ m = φ b := by
    intro m
    have hm : (m : G) ∈ ((B : Set G) * (K : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B K hBN, sup_comm]
      exact m.2
    obtain ⟨b, hb, l, hl, hbl⟩ := Set.mem_mul.1 hm
    refine ⟨⟨b, hBM hb⟩, Subgroup.mem_subgroupOf.2 hb, ?_⟩
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show ((m : G))⁻¹ * b ∈ K
    rw [← hbl]
    have : (b * l)⁻¹ * b = l⁻¹ := by group
    rw [this]
    exact K.inv_mem hl
  have hQp : IsPGroup p (↥M ⧸ K.subgroupOf M) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, hbm⟩ := hdecomp m
    obtain ⟨k, hk⟩ := hBp ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have hk' : b ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hmb : (QuotientGroup.mk m : ↥M ⧸ K.subgroupOf M) = QuotientGroup.mk b := hbm
    rw [hmb, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  haveI : Finite (↥M ⧸ K.subgroupOf M) := inferInstance
  haveI : Group.IsNilpotent (↥M ⧸ K.subgroupOf M) := hQp.isNilpotent
  have hq : CFSG.KCore.KGroupAllSimple CFSG.Assembly.InCatalog (↥M ⧸ K.subgroupOf M) :=
    CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.Assembly.inCatalog_containsAbelianSimple
      inferInstance
  have hker : CFSG.KCore.KGroupAllSimple CFSG.Assembly.InCatalog ↥φ.ker := by
    have e : ↥φ.ker ≃* ↥K :=
      (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (K.subgroupOf M))).trans
        (Subgroup.subgroupOfEquivOfLe hKM)
    exact CFSG.KCore.KGroupAllSimple.of_mulEquiv CFSG.Assembly.inCatalog_isoInvariant hK' e
  have hall : CFSG.KCore.KGroupAllSimple CFSG.Assembly.InCatalog ↥M :=
    CFSG.KCore.KGroupAllSimple.of_ker CFSG.Assembly.inCatalog_isoInvariant φ hker hq
  exact fun K' L _ _ hs _ => hall K' (L.subgroupOf K') hs

end CFSG.LocalAnalysis.GLTheoremA
