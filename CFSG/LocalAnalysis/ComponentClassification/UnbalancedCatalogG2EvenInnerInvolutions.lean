module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem units_map_entrywise_pinnedX (σ : K ≃+* K) (α : Fin Tag.G2.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ.toRingHom) (X α c) = X α (σ c) :=
  Units.ext (entrywise_pinnedX σ.toRingHom α c)

theorem units_map_entrywise_g2N (σ : K ≃+* K) (A B C D E F : K) :
    Units.map (entrywiseHom σ.toRingHom) (g2N A B C D E F) =
      g2N (σ A) (σ B) (σ C) (σ D) (σ E) (σ F) := by
  simp only [g2N, map_mul, units_map_entrywise_pinnedX]

theorem exists_of_commute_conj_pinnedX {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {γ : Fin Tag.G2.rank → ℤ} {β : MulAut (adjointGroup .G2 K)}
    (hβ : Commute β (MulAut.conj ⟨X γ 1, pinnedX_mem_adjointGroup γ 1⟩)) :
    ∃ g : adjointGroup .G2 K, (g : ModGL .G2 K) * X γ 1 = X γ 1 * g ∧ ∃ σ : K ≃+* K,
      ∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (even_G2_exact_automorphism_normal_form hf K hK).1 β
  refine ⟨g, ?_, σ, hgσ⟩
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  set z : adjointGroup .G2 K := ⟨X γ 1, pinnedX_mem_adjointGroup γ 1⟩
  have h1 : MulAut.conj (β z) = MulAut.conj z := by
    rw [← mulAut_mul_conj_mul_inv, hβ.eq, mul_inv_cancel_right]
  have h2 := mulAut_conj_injective_of_center_eq_bot hZ h1
  have h3 := congrArg Subtype.val h2
  rw [hgσ z] at h3
  change (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (X γ 1) *
    (g : ModGL .G2 K)⁻¹ = X γ 1 at h3
  rw [units_map_entrywise_pinnedX, map_one] at h3
  exact mul_inv_eq_iff_eq_mul.1 h3

omit [Field K] in
theorem finite_mulAut_of_finite {G : Type*} [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun σ : MulAut G => (σ : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem units_map_entrywise_refl (h : ModGL .G2 K) :
    Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) h = h :=
  Units.ext (entrywise_id (h : Module.End K (RootModule .G2 K)))

theorem conj_commute_of_commute {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    Commute (MulAut.conj a) (MulAut.conj b) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, h]

section Long

variable [CharP K 2]

variable (K) in
@[expose] def g2LongRadicalInn : Subgroup (MulAut (adjointGroup .G2 K)) :=
  ((g2LongRadical K).subgroupOf (adjointGroup .G2 K)).map MulAut.conj

theorem g2LongRadicalInn_isPGroup : IsPGroup 2 (g2LongRadicalInn K) :=
  (IsPGroup.of_equiv g2LongRadical_isPGroup
    (Subgroup.subgroupOfEquivOfLe g2LongRadical_le_adjointGroup).symm).map _

theorem apply_mem_g2LongRadical {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {β : MulAut (adjointGroup .G2 K)}
    (hβ : Commute β (MulAut.conj ⟨X g2c 1, pinnedX_mem_adjointGroup g2c 1⟩))
    {q : adjointGroup .G2 K} (hq : (q : ModGL .G2 K) ∈ g2LongRadical K) :
    (β q : ModGL .G2 K) ∈ g2LongRadical K := by
  obtain ⟨g, hgz, σ, hgσ⟩ := exists_of_commute_conj_pinnedX hf hK hβ
  obtain ⟨q₀, hq₀, l₀, hl₀, hg⟩ := exists_mem_mul_of_commute_c g.2 hgz
  obtain ⟨B, C, D, E, F, hqe⟩ := hq
  rw [hgσ, hqe, units_map_entrywise_g2N, map_zero, hg, mul_inv_rev,
    show q₀ * l₀ * g2N 0 (σ B) (σ C) (σ D) (σ E) (σ F) * (l₀⁻¹ * q₀⁻¹) =
      q₀ * (l₀ * g2N 0 (σ B) (σ C) (σ D) (σ E) (σ F) * l₀⁻¹) * q₀⁻¹ by group]
  exact mul_mem (mul_mem hq₀ (conj_mem_g2LongRadical hl₀ (g2N_mem_g2LongRadical _ _ _ _ _)))
    (inv_mem hq₀)

theorem mem_g2LongRadicalInn {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {β : MulAut (adjointGroup .G2 K)}
    (hβ : Commute β (MulAut.conj ⟨X g2c 1, pinnedX_mem_adjointGroup g2c 1⟩))
    (hN : ∀ n ∈ g2LongRadicalInn K, β * n = n * β) : β ∈ g2LongRadicalInn K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨g, hgz, σ, hgσ⟩ := exists_of_commute_conj_pinnedX hf hK hβ
  obtain ⟨q₀, hq₀, l₀, hl₀, hg⟩ := exists_mem_mul_of_commute_c g.2 hgz
  have hfix : ∀ q : adjointGroup .G2 K, (q : ModGL .G2 K) ∈ g2LongRadical K → β q = q := by
    intro q hq
    have hn : MulAut.conj q ∈ g2LongRadicalInn K := ⟨q, hq, rfl⟩
    have h1 : MulAut.conj (β q) = MulAut.conj q := by
      rw [← mulAut_mul_conj_mul_inv, hN _ hn, mul_inv_cancel_right]
    exact mulAut_conj_injective_of_center_eq_bot hZ h1
  have hσ : σ = RingEquiv.refl K := by
    refine RingEquiv.ext fun x => ?_
    have h1 := congrArg Subtype.val (hfix ⟨X g2c x, pinnedX_mem_adjointGroup g2c x⟩
      (pinnedX_c_mem_g2LongRadical x))
    rw [hgσ] at h1
    change (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (X g2c x) *
      (g : ModGL .G2 K)⁻¹ = X g2c x at h1
    rw [units_map_entrywise_pinnedX, hg, mul_inv_rev,
      show q₀ * l₀ * X g2c (σ x) * (l₀⁻¹ * q₀⁻¹) = q₀ * (l₀ * X g2c (σ x) * l₀⁻¹) * q₀⁻¹ by
        group, (commute_of_mem_g2RankOne_r hl₀ _).eq, mul_inv_cancel_right,
      (commute_pinnedX_c_of_mem_posUnipotent _ (g2LongRadical_le_posUnipotent hq₀)).symm.eq,
      mul_inv_cancel_right] at h1
    exact pinnedX_injective .G2 K g2c h1
  subst hσ
  have hact : ActsOnRadical l₀ LinearMap.id := by
    refine ⟨fun y => commute_of_mem_g2RankOne_r hl₀ y, fun x F => ?_⟩
    have hqC : g2N 0 (x 0) (x 1) (x 2) (x 3) F ∈ adjointGroup .G2 K :=
      g2LongRadical_le_adjointGroup (g2N_mem_g2LongRadical _ _ _ _ _)
    have h1 := congrArg Subtype.val (hfix ⟨_, hqC⟩ (g2N_mem_g2LongRadical _ _ _ _ _))
    rw [hgσ, units_map_entrywise_refl, hg] at h1
    have e : l₀ * g2N 0 (x 0) (x 1) (x 2) (x 3) F * l₀⁻¹ =
        q₀⁻¹ * g2N 0 (x 0) (x 1) (x 2) (x 3) F * q₀⁻¹⁻¹ := by
      rw [inv_inv]
      calc l₀ * g2N 0 (x 0) (x 1) (x 2) (x 3) F * l₀⁻¹ =
          q₀⁻¹ * (q₀ * l₀ * g2N 0 (x 0) (x 1) (x 2) (x 3) F * (q₀ * l₀)⁻¹) * q₀ := by group
        _ = q₀⁻¹ * g2N 0 (x 0) (x 1) (x 2) (x 3) F * q₀ := by rw [h1]
    rw [e]
    exact (actsOnRadical_of_mem (inv_mem hq₀)).2 x F
  have hl₁ : (⟨l₀, hl₀⟩ : g2RankOne K g2ir) = 1 := by
    refine radActionHom_injective ?_
    rw [map_one]
    exact Units.ext ((radAction_spec ⟨l₀, hl₀⟩).unique hact)
  have hl₀1 : l₀ = 1 := congrArg Subtype.val hl₁
  refine ⟨⟨q₀, g2LongRadical_le_adjointGroup hq₀⟩, hq₀, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hgσ, units_map_entrywise_refl, hg, hl₀1, mul_one]
  rfl

theorem oddCore_inf_centralizer_conj_pinnedX_c {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (adjointGroup .G2 K))) (hIH : inner (adjointGroup .G2 K) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
      {MulAut.conj (⟨X g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ : adjointGroup .G2 K)}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have : Finite (MulAut (adjointGroup .G2 K)) := finite_mulAut_of_finite
  set z : adjointGroup .G2 K := ⟨X g2c 1, pinnedX_mem_adjointGroup g2c 1⟩
  refine SpChain.oddCore_eq_bot_of_centralizer (N := g2LongRadicalInn K) ?_ ?_ ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hIH ⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    refine (conj_commute_of_commute (Subtype.ext ?_)).eq.symm
    exact (commute_pinnedX_c_of_mem_posUnipotent 1 (g2LongRadical_le_posUnipotent hq)).eq
  · rintro c hc _ ⟨q, hq, rfl⟩
    have hcz : Commute c (MulAut.conj z) :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2)
    refine ⟨c q, apply_mem_g2LongRadical hf hK hcz hq, ?_⟩
    exact (mulAut_mul_conj_mul_inv c q).symm
  · intro Y hY _ hodd
    exact SpChain.eq_bot_of_isPGroup_two g2LongRadicalInn_isPGroup hY hodd
  · intro c hc hcN
    have hcz : Commute c (MulAut.conj z) :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2)
    obtain ⟨k, hk⟩ := g2LongRadicalInn_isPGroup ⟨c, mem_g2LongRadicalInn hf hK hcz hcN⟩
    exact ⟨k, congrArg Subtype.val hk⟩

end Long

section Short

variable [CharP K 2]

variable (K) in
@[expose] def g2ShortRadicalInn : Subgroup (MulAut (adjointGroup .G2 K)) :=
  ((g2ShortRadical K).subgroupOf (adjointGroup .G2 K)).map MulAut.conj

theorem g2ShortRadical_le_adjointGroup : g2ShortRadical K ≤ adjointGroup .G2 K :=
  fun _ hq => g2LongRadical_le_adjointGroup (g2ShortRadical_le_g2LongRadical hq)

theorem g2ShortRadicalInn_isPGroup : IsPGroup 2 (g2ShortRadicalInn K) := by
  have : CFSG.IsElementaryAbelian 2 (g2ShortRadical K) := g2ShortRadical_isElementaryAbelian
  exact (IsPGroup.of_equiv (CFSG.IsElementaryAbelian.isPGroup 2 (g2ShortRadical K))
    (Subgroup.subgroupOfEquivOfLe g2ShortRadical_le_adjointGroup).symm).map _

theorem apply_mem_g2ShortRadical {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {β : MulAut (adjointGroup .G2 K)}
    (hβ : Commute β (MulAut.conj ⟨X g2v 1, pinnedX_mem_adjointGroup g2v 1⟩))
    {q : adjointGroup .G2 K} (hq : (q : ModGL .G2 K) ∈ g2ShortRadical K) :
    (β q : ModGL .G2 K) ∈ g2ShortRadical K := by
  obtain ⟨g, hgz, σ, hgσ⟩ := exists_of_commute_conj_pinnedX hf hK hβ
  obtain ⟨q₀, hq₀, l₀, hl₀, hg⟩ := exists_mem_mul_of_commute_v g.2 hgz
  obtain ⟨D, E, F, hqe⟩ := hq
  rw [hgσ, hqe, units_map_entrywise_g2N, map_zero, hg, mul_inv_rev,
    show q₀ * l₀ * g2N 0 0 0 (σ D) (σ E) (σ F) * (l₀⁻¹ * q₀⁻¹) =
      q₀ * (l₀ * g2N 0 0 0 (σ D) (σ E) (σ F) * l₀⁻¹) * q₀⁻¹ by group]
  exact mul_mem (mul_mem hq₀ (conj_mem_g2ShortRadical hl₀ (g2N_mem_g2ShortRadical _ _ _)))
    (inv_mem hq₀)

theorem mem_g2ShortRadicalInn {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {β : MulAut (adjointGroup .G2 K)}
    (hβ : Commute β (MulAut.conj ⟨X g2v 1, pinnedX_mem_adjointGroup g2v 1⟩))
    (hN : ∀ n ∈ g2ShortRadicalInn K, β * n = n * β) : β ∈ g2ShortRadicalInn K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨g, hgz, σ, hgσ⟩ := exists_of_commute_conj_pinnedX hf hK hβ
  obtain ⟨q₀, hq₀, l₀, hl₀, hg⟩ := exists_mem_mul_of_commute_v g.2 hgz
  have hfix : ∀ q : adjointGroup .G2 K, (q : ModGL .G2 K) ∈ g2ShortRadical K → β q = q := by
    intro q hq
    have hn : MulAut.conj q ∈ g2ShortRadicalInn K := ⟨q, hq, rfl⟩
    have h1 : MulAut.conj (β q) = MulAut.conj q := by
      rw [← mulAut_mul_conj_mul_inv, hN _ hn, mul_inv_cancel_right]
    exact mulAut_conj_injective_of_center_eq_bot hZ h1
  have hσ : σ = RingEquiv.refl K := by
    refine RingEquiv.ext fun x => ?_
    have h1 := congrArg Subtype.val (hfix ⟨X g2v x, pinnedX_mem_adjointGroup g2v x⟩
      (pinnedX_v_mem_g2ShortRadical x))
    rw [hgσ] at h1
    change (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (X g2v x) *
      (g : ModGL .G2 K)⁻¹ = X g2v x at h1
    rw [units_map_entrywise_pinnedX, hg, mul_inv_rev,
      show q₀ * l₀ * X g2v (σ x) * (l₀⁻¹ * q₀⁻¹) = q₀ * (l₀ * X g2v (σ x) * l₀⁻¹) * q₀⁻¹ by
        group, (commute_of_mem_g2RankOne_a hl₀ _).eq, mul_inv_cancel_right,
      (commute_of_mem_g2ShortRadical hq₀ (pinnedX_v_mem_g2ShortRadical _)).eq,
      mul_inv_cancel_right] at h1
    exact pinnedX_injective .G2 K g2v h1
  subst hσ
  have hact : ActsOnShort l₀ LinearMap.id := by
    refine ⟨fun x => commute_of_mem_g2RankOne_a hl₀ x,
      (exists_actsOnShort hl₀).choose_spec.2.1, fun y => ?_⟩
    have hqA : g2N 0 0 0 0 (y 0) (y 1) ∈ g2ShortRadical K := g2N_mem_g2ShortRadical _ _ _
    have h1 := congrArg Subtype.val (hfix ⟨_, g2ShortRadical_le_adjointGroup hqA⟩ hqA)
    rw [hgσ, units_map_entrywise_refl, hg] at h1
    calc l₀ * g2N 0 0 0 0 (y 0) (y 1) * l₀⁻¹ =
        q₀⁻¹ * (q₀ * l₀ * g2N 0 0 0 0 (y 0) (y 1) * (q₀ * l₀)⁻¹) * q₀ := by group
      _ = q₀⁻¹ * (g2N 0 0 0 0 (y 0) (y 1) * q₀) := by rw [h1, mul_assoc]
      _ = g2N 0 0 0 0 (y 0) (y 1) := by
          rw [← (commute_of_mem_g2ShortRadical hq₀ hqA).eq, inv_mul_cancel_left]
      _ = g2N 0 0 0 0 (LinearMap.id y 0) (LinearMap.id y 1) := rfl
  have hl₁ : (⟨l₀, hl₀⟩ : g2RankOne K g2ia) = 1 := by
    refine shActionHom_injective ?_
    rw [map_one]
    exact Units.ext ((shAction_spec ⟨l₀, hl₀⟩).unique hact)
  have hl₀1 : l₀ = 1 := congrArg Subtype.val hl₁
  refine ⟨⟨q₀, g2ShortRadical_le_adjointGroup hq₀⟩, hq₀, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hgσ, units_map_entrywise_refl, hg, hl₀1, mul_one]
  rfl

theorem oddCore_inf_centralizer_conj_pinnedX_v {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (adjointGroup .G2 K))) (hIH : inner (adjointGroup .G2 K) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
      {MulAut.conj (⟨X g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ : adjointGroup .G2 K)}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have : Finite (MulAut (adjointGroup .G2 K)) := finite_mulAut_of_finite
  set z : adjointGroup .G2 K := ⟨X g2v 1, pinnedX_mem_adjointGroup g2v 1⟩
  refine SpChain.oddCore_eq_bot_of_centralizer (N := g2ShortRadicalInn K) ?_ ?_ ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hIH ⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    refine (conj_commute_of_commute (Subtype.ext ?_)).eq.symm
    exact (commute_of_mem_g2ShortRadical (pinnedX_v_mem_g2ShortRadical 1) hq).eq
  · rintro c hc _ ⟨q, hq, rfl⟩
    have hcz : Commute c (MulAut.conj z) :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2)
    refine ⟨c q, apply_mem_g2ShortRadical hf hK hcz hq, ?_⟩
    exact (mulAut_mul_conj_mul_inv c q).symm
  · intro Y hY _ hodd
    exact SpChain.eq_bot_of_isPGroup_two g2ShortRadicalInn_isPGroup hY hodd
  · intro c hc hcN
    have hcz : Commute c (MulAut.conj z) :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2)
    obtain ⟨k, hk⟩ := g2ShortRadicalInn_isPGroup ⟨c, mem_g2ShortRadicalInn hf hK hcz hcN⟩
    exact ⟨k, congrArg Subtype.val hk⟩

end Short

theorem even_G2_inner_involution_full_centralizer_odd_core {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup .G2 K)))
    (hIH : inner (adjointGroup .G2 K) ≤ H) {α : MulAut (adjointGroup .G2 K)}
    (hαI : α ∈ inner (adjointGroup .G2 K)) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨z, rfl⟩ := hαI
  have hz : orderOf z = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_center_eq_bot hZ) z]
    exact hα
  have hconj : ∀ z₀ : adjointGroup .G2 K, IsConj z z₀ →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {MulAut.conj z₀}) = ⊥ →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {MulAut.conj z}) = ⊥ := by
    intro z₀ hzz h
    obtain ⟨c, hc⟩ := isConj_iff.1 hzz
    have e : MulAut.conj z = MulAut.conj c⁻¹ * MulAut.conj z₀ * (MulAut.conj c⁻¹)⁻¹ := by
      rw [← hc, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [e]
    exact SpChain.oddCore_centralizer_conj_eq_bot (hIH ⟨c⁻¹, rfl⟩) h
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) z hz with h | h
  · exact hconj _ h (oddCore_inf_centralizer_conj_pinnedX_c hf hK H hIH)
  · exact hconj _ h (oddCore_inf_centralizer_conj_pinnedX_v hf hK H hIH)

end CFSG.ComponentClassification.UnbalancedCatalog
