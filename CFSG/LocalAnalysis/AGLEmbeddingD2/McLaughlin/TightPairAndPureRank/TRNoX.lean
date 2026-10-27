module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
import CFSG.Goldschmidt.Steps.G37CoreSetup
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridgeAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSetup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_inf' {A B : Subgroup G} (h : IsSubnormal A B) (K : Subgroup G) :
    IsSubnormal (A ⊓ K) (B ⊓ K) :=
  h.inf K

theorem isSubnormal_subgroupOf' {A B : Subgroup G} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem isSubnormal_trans'' {A B C : Subgroup G} (h1 : IsSubnormal A B) (h2 : IsSubnormal B C) :
    IsSubnormal A C :=
  h1.trans h2

theorem noXBlock_of_decomp {M X₀ J T : Subgroup G} (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hM : GLBIsMaxTwoLocal M) (hT2 : IsPGroup 2 T) (hJX : J ≤ X₀) (hXM : X₀ ≤ M)
    (hdec : ∀ x ∈ X₀, ∃ t ∈ T, ∃ j ∈ J, x = t * j) (hTX : T ≤ X₀)
    (hJn : ∀ x ∈ X₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hJsub : IsSubnormal J M) :
    ∀ Y : Subgroup ↥X₀, IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hYsub hY
  have hle : X₀ ≤ Subgroup.normalizer (J : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => hJn x hx j hj, fun hj => ?_⟩
    have := hJn x⁻¹ (X₀.inv_mem hx) _ hj
    simpa [mul_assoc] using this
  set D : Subgroup ↥X₀ := J.subgroupOf X₀ with hD
  have hDn : D.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).mpr hle
  have hYD : Y ≤ D := by
    let Nn : Subgroup ↥Y := (D ⊓ Y).subgroupOf Y
    have hNn : Nn.Normal := ⟨fun x hx g => by
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, Y.mul_mem (Y.mul_mem g.2 x.2) (Y.inv_mem g.2)⟩
      exact hDn.conj_mem _ (Subgroup.mem_subgroupOf.mp hx).1 g.1⟩
    have hq : IsPGroup 2 (↥Y ⧸ Nn) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨t, ht, j, hj, hyt⟩ := hdec y.1 y.1.2
      obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
      have hm' : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      refine ⟨m, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, (y ^ 2 ^ m).2⟩
      let t' : ↥X₀ := ⟨t, hTX ht⟩
      let j' : ↥X₀ := ⟨j, hJX hj⟩
      have hjD : j' ∈ D := Subgroup.mem_subgroupOf.mpr hj
      have hyeq : (y : ↥X₀) = t' * j' := Subtype.ext hyt
      have hmk : (QuotientGroup.mk (y : ↥X₀) : ↥X₀ ⧸ D) = QuotientGroup.mk t' := by
        rw [hyeq, QuotientGroup.eq]
        simpa using D.inv_mem hjD
      have ht1 : t' ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm')
      have h1 : (QuotientGroup.mk ((y : ↥X₀) ^ 2 ^ m) : ↥X₀ ⧸ D) = 1 := by
        rw [QuotientGroup.mk_pow, hmk, ← QuotientGroup.mk_pow, ht1]; rfl
      have := (QuotientGroup.eq_one_iff _).mp h1
      simpa using this
    have hfull := hY.1.1 Nn hq
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ Nn := by rw [hfull]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  set Y' : Subgroup G := Y.map X₀.subtype with hY'
  have hY'J : Y' ≤ J := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hYD hy)
  have hs1 : IsSubnormal Y' X₀ := by
    have h := cfsg_isSubnormal_map X₀.subtype hYsub
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hs2 : IsSubnormal Y' J := by
    have h := isSubnormal_inf' hs1 J
    rwa [inf_eq_left.mpr hY'J, inf_eq_right.mpr hJX] at h
  have hsub : IsSubnormal Y' M := isSubnormal_trans'' hs2 hJsub
  have hXY : CFSG.RankThree.PartOne.InClassX ↥Y := CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hY
  have hXY' : CFSG.RankThree.PartOne.InClassX ↥Y' :=
    CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv (Y.equivMapOfInjective X₀.subtype
      X₀.subtype_injective) hXY
  have hY'X : InClassXBlock Y' := CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hXY'
  exact hX M Y' hM (hY'J.trans (hJX.trans hXM)) hsub hY'X

theorem isSubnormal_trJ {M S L₁ L₂ : Subgroup G} (h₁ : IsWeakSBlock M S L₁)
    (h₂ : IsWeakSBlock M S L₂) : IsSubnormal (trJ M L₁ L₂) M := by
  have hJM : trJ M L₁ L₂ ≤ M := sup_le (sup_le h₁.le h₂.le) (pCoreOf_le 2 M)
  refine CFSG.Goldschmidt.G37.open_isSubnormal_of_subgroupOf hJM ?_
  have hQ : ((pCoreOf 2 M).subgroupOf M).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 M)]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  rw [trJ, Subgroup.subgroupOf_sup (sup_le h₁.le h₂.le) (pCoreOf_le 2 M),
    Subgroup.subgroupOf_sup h₁.le h₂.le]
  exact CFSG.GroupTheory.isSubnormal_sup
    (CFSG.GroupTheory.isSubnormal_sup (isSubnormal_subgroupOf' h₁.subnormal)
      (isSubnormal_subgroupOf' h₂.subnormal)) hQ

theorem noXBlock_trX {M S L₁ L₂ T : Subgroup G} (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hM : GLBIsMaxTwoLocal M) (h₁ : IsWeakSBlock M S L₁) (h₂ : IsWeakSBlock M S L₂)
    (hT2 : IsPGroup 2 T) (hN : ∀ t ∈ T, ∀ j ∈ trJ M L₁ L₂, t * j * t⁻¹ ∈ trJ M L₁ L₂)
    (hTM : T ≤ M) :
    ∀ Y : Subgroup ↥(trX M L₁ L₂ T), IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  refine noXBlock_of_decomp hX hM hT2 le_trX_left (trX_le h₁.le h₂.le hTM)
    (fun x hx => exists_mul_of_mem_trX hN hx) le_trX_right ?_ (isSubnormal_trJ h₁ h₂)
  intro x hx j hj
  obtain ⟨t, ht, j₀, hj₀, rfl⟩ := exists_mul_of_mem_trX hN hx
  have : t * j₀ * j * (t * j₀)⁻¹ = t * (j₀ * j * j₀⁻¹) * t⁻¹ := by group
  rw [this]
  exact hN t ht _ ((trJ M L₁ L₂).mul_mem ((trJ M L₁ L₂).mul_mem hj₀ hj) ((trJ M L₁ L₂).inv_mem hj₀))

theorem cfsgIsKGroup_of_open {X : Type} [Group X] [Finite X] (hX : Open.IsKGroup X) :
    CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple hX


theorem gnSetting_trX {M S L₁ L₂ T : Subgroup G} (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hM : GLBIsMaxTwoLocal M) (hKM : Open.IsKGroup ↥M) (hcM : CharTwo M)
    (h₁ : IsWeakSBlock M S L₁) (h₂ : IsWeakSBlock M S L₂) (hT2 : IsPGroup 2 T)
    (hN : ∀ t ∈ T, ∀ j ∈ trJ M L₁ L₂, t * j * t⁻¹ ∈ trJ M L₁ L₂) (hTM : T ≤ M)
    (hSyl : IsSylowTwoOf T (trX M L₁ L₂ T)) :
    WeakBlockModuleData.GNSetting ↥(trX M L₁ L₂ T) (T.subgroupOf (trX M L₁ L₂ T)) where
  kGroup := cfsgIsKGroup_of_open (CFSG.AGLEmbedding.AscEightFour.isKGroup_mono hKM (trX_le h₁.le h₂.le hTM))
  sylow := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT2.of_equiv (Subgroup.subgroupOfEquivOfLe le_trX_right).symm
    · show ¬ 2 ∣ (T.subgroupOf (trX M L₁ L₂ T)).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hSyl.2.2
  charTwo := charTwo_top_of_le hcM (pCoreOf_le_trJ.trans le_trX_left) (trX_le h₁.le h₂.le hTM)
  noXBlock := noXBlock_trX hX hM h₁ h₂ hT2 hN hTM

end CFSG.AGLEmbeddingD2.McLaughlin
