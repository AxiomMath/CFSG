module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterExc
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional
public import CFSG.GroupTheory.SteinbergCBFTPSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.TauCetiBridge
open CFSG.Adapters.CatalogueFieldBridges
open scoped Pointwise

theorem le_fixSubgroup_and_conj_mem_of_canonicalData {C : Type} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {δ : MulAut C} {J : Subgroup C}
    (hNδ : J.map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer ({δ} : Set (MulAut C)))
    (hnormal : ((J.map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer ({δ} : Set (MulAut C)))).Normal) :
    J ≤ fixSubgroup δ ∧ ∀ f ∈ fixSubgroup δ, ∀ t ∈ J, f * t * f⁻¹ ∈ J := by
  have hfix : ∀ j ∈ J, δ j = j := by
    intro j hj
    have hmem : (MulAut.conj j : MulAut C) ∈ J.map (MulAut.conj : C →* MulAut C) :=
      ⟨j, hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hNδ hmem)
    apply hinj
    rw [← mul_conj_mul_inv δ j, ← h1]
    group
  refine ⟨fun j hj => hfix j hj, fun f hf t ht => ?_⟩
  have hc : MulAut.conj f ∈ Subgroup.centralizer ({δ} : Set (MulAut C)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (conj_commute_of_mem_fixSub hf).symm
  have hmt : (MulAut.conj t : MulAut C) ∈ J.map (MulAut.conj : C →* MulAut C) :=
    ⟨t, ht, rfl⟩
  have hn : (⟨MulAut.conj t, hNδ hmt⟩ : Subgroup.centralizer ({δ} : Set (MulAut C))) ∈
      (J.map (MulAut.conj : C →* MulAut C)).subgroupOf
        (Subgroup.centralizer ({δ} : Set (MulAut C))) := hmt
  have h2 := hnormal.conj_mem _ hn ⟨MulAut.conj f, hc⟩
  obtain ⟨s, hs, hsf⟩ := Subgroup.mem_subgroupOf.1 h2
  have hseq : s = f * t * f⁻¹ := by
    apply hinj
    rw [map_mul, map_mul, map_inv]
    exact hsf
  rwa [← hseq]

theorem idxCoreAt_of_coreData {C : Type} [Group C] {p : ℕ} {d : TauCeti.LieTypeIndex}
    {δ : MulAut C} {J : Subgroup C} (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hJq : CFSG.IsQuasisimple J)
    (hNδ : J.map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer ({δ} : Set (MulAut C)))
    (hnormal : ((J.map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer ({δ} : Set (MulAut C)))).Normal)
    (hpdvd : p ∣ Nat.card J) {i : TauCeti.CFSGIndex}
    (htype : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group)) (hsub : subRelC p d i) :
    IdxCoreAt p d δ := by
  obtain ⟨hle, hnorm⟩ := le_fixSubgroup_and_conj_mem_of_canonicalData hinj hNδ hnormal
  exact ⟨J, hle, hnorm, hJq, hpdvd, i, htype, hsub⟩

theorem idxCoreAt_entrywise {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {d : TauCeti.LieTypeIndex} {i : TauCeti.CFSGIndex} {σ : K ≃+* K}
    (hJC : fixedFieldImage τ σ ≤ adjointGroup τ K)
    (hq : CFSG.IsQuasisimple (fixedFieldImage τ σ))
    (hNδ : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) ≤
      Subgroup.centralizer ({entrywiseAdjointAut τ σ} : Set (MulAut ↥(adjointGroup τ K))))
    (hnormal : ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer ({entrywiseAdjointAut τ σ} :
        Set (MulAut ↥(adjointGroup τ K))))).Normal)
    (hpdvd : p ∣ Nat.card ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)))
    (hsub : subRelC p d i)
    (htype : Nonempty (↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ⧸
      Subgroup.center ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃* i.Group)) :
    IdxCoreAt p d (entrywiseAdjointAut τ σ) :=
  idxCoreAt_of_coreData
    (mulAut_conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := τ) (K := K)))
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hq)
    hNδ hnormal hpdvd htype hsub

theorem card_fixSubfield_eq_pow_div {K : Type} [Field K] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) {σ : K ≃+* K} (hσp : orderOf σ = p) :
    Nat.card (fixSubfield σ) = ℓ ^ (f / p) := by
  obtain ⟨-, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hcard
  exact hcard

theorem idxCoreAt_entrywise_cat {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) {q₀ : TauCeti.PrimePower} (hv₀ : (c q₀).Valid)
    {K : Type} [Field K] [Finite K] {p : ℕ} {d : TauCeti.LieTypeIndex} {σ : K ≃+* K}
    (hp : p.Prime) (hk : Nat.card (fixSubfield σ) = q₀.card)
    (hJC : fixedFieldImage τ σ ≤ adjointGroup τ K)
    (hq : CFSG.IsQuasisimple (fixedFieldImage τ σ))
    (hNδ : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) ≤
      Subgroup.centralizer ({entrywiseAdjointAut τ σ} : Set (MulAut ↥(adjointGroup τ K))))
    (hnormal : ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer ({entrywiseAdjointAut τ σ} :
        Set (MulAut ↥(adjointGroup τ K))))).Normal)
    (hdvd : ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ))))
    (hsub : subRelC p d (.lie ⟨c q₀, hv₀⟩)) :
    IdxCoreAt p d (entrywiseAdjointAut τ σ) := by
  have hpdvd : p ∣ Nat.card ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv,
      ← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv]
    exact (Nat.Prime.dvd_iff_not_coprime hp).2 hdvd
  exact idxCoreAt_entrywise hJC hq hNδ hnormal hpdvd hsub
    (nonempty_centerQuotient_catEquiv hB hv₀ hk
      ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))

theorem idxCoreAt_entrywise_cat_of_simple {τ : Tag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) {q₀ : TauCeti.PrimePower} (hv₀ : (c q₀).Valid)
    {K : Type} [Field K] [Finite K] {p : ℕ} {d : TauCeti.LieTypeIndex} {σ : K ≃+* K}
    (hp : p.Prime) (hk : Nat.card (fixSubfield σ) = q₀.card)
    (hJC : fixedFieldImage τ σ ≤ adjointGroup τ K)
    (hsimple : IsSimpleGroup ↥(fixedFieldImage τ σ))
    (hnc : ¬∀ a b : ↥(fixedFieldImage τ σ), a * b = b * a)
    (hNδ : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) ≤
      Subgroup.centralizer ({entrywiseAdjointAut τ σ} : Set (MulAut ↥(adjointGroup τ K))))
    (hnormal : ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer ({entrywiseAdjointAut τ σ} :
        Set (MulAut ↥(adjointGroup τ K))))).Normal)
    (hdvd : ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ))))
    (hsub : subRelC p d (.lie ⟨c q₀, hv₀⟩)) :
    IdxCoreAt p d (entrywiseAdjointAut τ σ) :=
  haveI : IsSimpleGroup ↥(fixedFieldImage τ σ) := hsimple
  idxCoreAt_entrywise_cat hB hv₀ hp hk hJC (isQuasisimple_of_simple_nonabelian hnc) hNδ hnormal
    hdvd hsub

private theorem idxCoreAt_G2_two_entrywise {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) {q : TauCeti.PrimePower} (hqcard : q.card = 2 ^ p)
    {σ : K ≃+* K} (hk2 : Nat.card (fixSubfield σ) = 2)
    (hJC : fixedFieldImage Tag.G2 σ ≤ adjointGroup Tag.G2 K)
    (hNδ : ((fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)).map
        (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) ≤
      Subgroup.centralizer ({entrywiseAdjointAut Tag.G2 σ} :
        Set (MulAut ↥(adjointGroup Tag.G2 K))))
    (hnormal : ((((fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)).map
        (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K))).subgroupOf
      (Subgroup.centralizer ({entrywiseAdjointAut Tag.G2 σ} :
        Set (MulAut ↥(adjointGroup Tag.G2 K))))).Normal)
    (hdf : p ∣ Nat.card (fixSubfield σ) ^ 6 - 1) :
    IdxCoreAt p (.G2 q) (entrywiseAdjointAut Tag.G2 σ) := by
  classical
  have h63 : p ∣ 63 := by
    rw [hk2] at hdf
    norm_num at hdf
    exact hdf
  have hp37 : p = 3 ∨ p = 7 := by
    have hle : p ≤ 63 := Nat.le_of_dvd (by norm_num) h63
    have key : ∀ m ∈ Finset.Icc 2 63, m.Prime → m ∣ 63 → m = 3 ∨ m = 7 := by decide
    exact key p (Finset.mem_Icc.2 ⟨hp.two_le, hle⟩) hp h63
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  have hinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))
  obtain ⟨hJle, hJnorm⟩ := le_fixSubgroup_and_conj_mem_of_canonicalData hinj hNδ hnormal
  let φ : ↥(adjointGroup Tag.G2 (fixSubfield σ)) →* ↥(adjointGroup Tag.G2 K) :=
    subfieldInclusion (fixSubfield σ)
  have hφ : Function.Injective φ := subfieldInclusion_injective (fixSubfield σ)
  have hrange : φ.range = (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
    ext g
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, (coe_subfieldInclusion (fixSubfield σ) a).symm⟩
    · rintro ⟨a, ha, hga⟩
      exact ⟨⟨a, ha⟩, Subtype.ext ((coe_subfieldInclusion (fixSubfield σ) ⟨a, ha⟩).trans hga)⟩
  obtain ⟨hTq0, hTcard0, hZT0, -, -⟩ :=
    derived_range_adjointG2_two (fixSubfield σ) hk2 φ hφ
  have hT : ⁅φ.range, φ.range⁆ =
      (commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))).map φ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_map]
  let eT : ↥⁅φ.range, φ.range⁆ ≃*
      ↥⁅adjointGroup Tag.G2 (fixSubfield σ), adjointGroup Tag.G2 (fixSubfield σ)⁆ :=
    ((MulEquiv.subgroupCongr hT).trans
      ((commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))).equivMapOfInjective φ hφ).symm).trans
      (((commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))).equivMapOfInjective
        (adjointGroup Tag.G2 (fixSubfield σ)).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _)))
  let q₃ : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have hq₃ : q₃.card = 3 := by
    rw [TauCeti.PrimePower.card_def]
    norm_num [q₃]
  have hv₃ : (TauCeti.LieTypeIndex.twistedA 2 q₃).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q₃]
  have hsub : subRelC p (.G2 q) (.lie ⟨.twistedA 2 q₃, hv₃⟩) := by
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨q₃, rfl, hq₃⟩, ⟨q, rfl⟩, ?_⟩)))
    rw [show fieldSize (TauCeti.LieTypeIndex.G2 q) = q.card from rfl, hqcard]
  have h1 : StatedClassicalModel ↥⁅adjointGroup Tag.G2 (fixSubfield σ),
      adjointGroup Tag.G2 (fixSubfield σ)⁆ StatedLieTag.PSU 3 3 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel
      (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds
        (fixSubfield σ) hk2)
      (by simp [CFSG.Blueprint.classicalTags])
  have h2 : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q₃, hv₃⟩).Group
      StatedLieTag.PSU 3 3 1 :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q₃ hv₃ (MulEquiv.refl _)
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h1 h2
  refine ⟨⁅(fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K),
      (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)⁆, ?_, ?_, ?_, ?_,
    .lie ⟨.twistedA 2 q₃, hv₃⟩, ?_, hsub⟩
  · intro t ht
    exact hJle (Subgroup.commutator_le_self _ ht)
  · have hJN : fixSubgroup (entrywiseAdjointAut Tag.G2 σ) ≤
        Subgroup.normalizer ((fixedFieldImage Tag.G2 σ).subgroupOf
          (adjointGroup Tag.G2 K) : Set (adjointGroup Tag.G2 K)) := by
      intro f hf
      rw [Subgroup.mem_normalizer_iff]
      intro t
      exact ⟨fun ht => hJnorm f hf t ht, fun ht => by
        have h := hJnorm f⁻¹ (inv_mem hf) (f * t * f⁻¹) ht
        rwa [show f⁻¹ * (f * t * f⁻¹) * f⁻¹⁻¹ = t by group] at h⟩
    have h := CFSG.GroupTheory.FT63ChII.le_normalizer_commutator
      (H₁ := (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K))
      (H₂ := (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K))
      (K := fixSubgroup (entrywiseAdjointAut Tag.G2 σ)) hJN hJN
    intro f hf t ht
    exact (Subgroup.mem_normalizer_iff.1 (h hf) t).1 ht
  · rw [hrange] at hTq0
    exact hTq0
  · rw [hrange] at hTcard0
    rw [hTcard0]
    rcases hp37 with rfl | rfl <;> norm_num
  · rw [hrange] at hZT0
    have hJeq : ⁅(fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K),
        (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)⁆ =
        ⁅φ.range, φ.range⁆ := by rw [hrange]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZT0).trans
      (QuotientGroup.quotientBot.trans
        ((MulEquiv.subgroupCongr hJeq).trans (eT.trans e2)))⟩

private theorem idxCoreAt_G2_even_entrywise {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) {q : TauCeti.PrimePower} (hpf : p ∣ q.exponent)
    (hK' : Nat.card K = q.p ^ q.exponent) (hk3 : 3 ≤ q.p ^ (q.exponent / p))
    {σ : K ≃+* K} (hσp : orderOf σ = p)
    (hJC : fixedFieldImage Tag.G2 σ ≤ adjointGroup Tag.G2 K)
    (hq : CFSG.IsQuasisimple (fixedFieldImage Tag.G2 σ))
    (hNδ : ((fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)).map
        (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) ≤
      Subgroup.centralizer ({entrywiseAdjointAut Tag.G2 σ} :
        Set (MulAut ↥(adjointGroup Tag.G2 K))))
    (hnormal : ((((fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)).map
        (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K))).subgroupOf
      (Subgroup.centralizer ({entrywiseAdjointAut Tag.G2 σ} :
        Set (MulAut ↥(adjointGroup Tag.G2 K))))).Normal)
    (hdvd : ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ)))) :
    IdxCoreAt p (.G2 q) (entrywiseAdjointAut Tag.G2 σ) := by
  have hpos : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
  let q₀ : TauCeti.PrimePower := ⟨q.p, q.exponent / p, q.prime_p, hpos⟩
  have hq0card : q₀.card = q.p ^ (q.exponent / p) := TauCeti.PrimePower.card_def q₀
  have hq0 : 3 ≤ q₀.card := by rw [hq0card]; exact hk3
  have hv₀ : (TauCeti.LieTypeIndex.G2 q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hq0, by simp⟩
  have hsub : subRelC p (.G2 q) (.lie ⟨.G2 q₀, hv₀⟩) := by
    refine Or.inl ⟨trivial, ?_⟩
    show fieldSize (TauCeti.LieTypeIndex.G2 q₀) ^ p = fieldSize (TauCeti.LieTypeIndex.G2 q)
    rw [show fieldSize (TauCeti.LieTypeIndex.G2 q₀) = q₀.card from rfl,
      show fieldSize (TauCeti.LieTypeIndex.G2 q) = q.card from rfl,
      TauCeti.PrimePower.card_def q₀, TauCeti.PrimePower.card_def q, ← pow_mul,
      Nat.div_mul_cancel hpf]
  have hk : Nat.card (fixSubfield σ) = q₀.card := by
    rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp, hq0card]
  exact idxCoreAt_entrywise_cat Even.chevalleyBridgesAll.g2 hv₀ hp hk hJC hq hNδ hnormal hdvd hsub

private theorem idxCoreAt_G2_three_entrywise {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) {q : TauCeti.PrimePower} (h3 : q.p = 3) (hpf : p ∣ q.exponent)
    (hK' : Nat.card K = q.p ^ q.exponent) {σ : K ≃+* K} (hσp : orderOf σ = p)
    (hJC : fixedFieldImage Tag.G2 σ ≤ adjointGroup Tag.G2 K)
    (hfix : ∀ g : ↥(adjointGroup Tag.G2 K),
      g ∈ (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) ↔
        entrywiseAdjointAut Tag.G2 σ g = g)
    (hdvd : ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ)))) :
    IdxCoreAt p (.G2 q) (entrywiseAdjointAut Tag.G2 σ) := by
  have hpos : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
  let q₀ : TauCeti.PrimePower := ⟨q.p, q.exponent / p, q.prime_p, hpos⟩
  have hq0card : q₀.card = q.p ^ (q.exponent / p) := TauCeti.PrimePower.card_def q₀
  have hcardk : Nat.card (fixSubfield σ) = 3 ^ (q.exponent / p) := by
    rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp, h3]
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have h3k : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hcardk]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (q.exponent / p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq0 : 3 ≤ q₀.card := by
    rw [hq0card, h3, ← hcardk]
    exact h3k
  have hv₀ : (TauCeti.LieTypeIndex.G2 q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hq0, by simp⟩
  have hsub : subRelC p (.G2 q) (.lie ⟨.G2 q₀, hv₀⟩) := by
    refine Or.inl ⟨trivial, ?_⟩
    show fieldSize (TauCeti.LieTypeIndex.G2 q₀) ^ p = fieldSize (TauCeti.LieTypeIndex.G2 q)
    rw [show fieldSize (TauCeti.LieTypeIndex.G2 q₀) = q₀.card from rfl,
      show fieldSize (TauCeti.LieTypeIndex.G2 q) = q.card from rfl,
      TauCeti.PrimePower.card_def q₀, TauCeti.PrimePower.card_def q, ← pow_mul,
      Nat.div_mul_cancel hpf]
  have hq : CFSG.IsQuasisimple (fixedFieldImage Tag.G2 σ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (fixedFieldImageEquiv σ)
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ) h3k)
  have hle : (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) ≤
      fixSubgroup (entrywiseAdjointAut Tag.G2 σ) := fun g hg => (hfix g).1 hg
  have hnorm : ∀ f ∈ fixSubgroup (entrywiseAdjointAut Tag.G2 σ),
      ∀ t ∈ (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K),
        f * t * f⁻¹ ∈ (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
    intro f hf t ht
    refine (hfix _).2 ?_
    have hf' : entrywiseAdjointAut Tag.G2 σ f = f := hf
    have ht' : entrywiseAdjointAut Tag.G2 σ t = t := (hfix t).1 ht
    show entrywiseAdjointAut Tag.G2 σ (f * t * f⁻¹) = f * t * f⁻¹
    rw [map_mul, map_mul, map_inv, hf', ht']
  have hq' : CFSG.IsQuasisimple
      ↥((fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hq
  have hpdvd : p ∣ Nat.card
      ↥((fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv,
      ← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv]
    exact (Nat.Prime.dvd_iff_not_coprime hp).2 hdvd
  have hk : Nat.card (fixSubfield σ) = q₀.card := by
    rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp, hq0card]
  exact ⟨_, hle, hnorm, hq', hpdvd, .lie ⟨.G2 q₀, hv₀⟩,
    nonempty_centerQuotient_catEquiv Even.chevalleyBridgesAll.g2 hv₀ hk
      ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm), hsub⟩

private theorem idxCoreAt_adjointG2 {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hq3 : 3 ≤ q.card) (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    (hKchar : CharP K q.p) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.G2 K)) :
    ∀ x : MulAut ↥(adjointGroup Tag.G2 K), x ^ p = 1 →
      x ∉ innAutDerived ↥(adjointGroup Tag.G2 K) → IdxCoreAt p (.G2 q) x := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp hpq
  have hd6 : p ∣ Nat.card K ^ 6 - 1 := dvd_pow_six_sub_one_of_dvd_card_adjointG2 hp hpK hcard
  have hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 6 - 1 := by
    intro σ hσp
    exact CFSG.HardMathSupport.Timmesfeld.LocalTwo.dvd_pow_sub_one_of_cast_eq
      Nat.card_pos Nat.card_pos
      (card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp).symm hd6
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ))) :=
    fun σ hσp =>
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.not_coprime_card_adjointG2_of_dvd_pow_six
        (fixSubfield σ) hp (hdf σ hσp)
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : ↥(adjointGroup Tag.G2 K) →*
      MulAut ↥(adjointGroup Tag.G2 K)).range :=
    fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  by_cases h2 : q.p = 2
  · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
    have hf2 : 2 ≤ q.exponent := by
      by_contra hlt
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [TauCeti.PrimePower.card_def, h2, h1] at hq3
      norm_num at hq3
    have hNF := conj_normalForm_of_pointwise
      (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        hf2 K hK2).1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.G2 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨hσp, hpf, ⟨h, hh⟩, -⟩ :=
      even_G2_noninner_prime_local_core_trivial hf2 hK2 hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩
        hxinner hαp y σ hyσ
    obtain ⟨-, -, hJC, -, -, -, -, hNδ, hnormal, -, -, -, -⟩ :=
      even_G2_canonical_field_centralizer_all_orders hf2 hK2 σ
    by_cases hexp : q.exponent = p
    · have hk2 : Nat.card (fixSubfield σ) = 2 := by
        rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp, hexp,
          Nat.div_self hp.pos, pow_one]
        exact h2
      have hqcard : q.card = 2 ^ p := by rw [TauCeti.PrimePower.card_def, h2, hexp]
      exact idxCoreAt_of_conj
        (idxCoreAt_G2_two_entrywise hp hqcard hk2 hJC hNδ hnormal (hdf σ hσp))
        (MulAut.conj h) hh
    · have hk3 : 3 ≤ q.p ^ (q.exponent / p) := by
        rw [h2]
        have h1 : 2 ≤ q.exponent / p := by
          rcases Nat.lt_or_ge (q.exponent / p) 2 with hlt | hge
          · exfalso
            have h1 : q.exponent / p = 1 := by
              have hpos : 0 < q.exponent / p :=
                Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
              omega
            have h2' : q.exponent = p := by
              rw [← Nat.div_mul_cancel hpf, h1, one_mul]
            exact hexp h2'
          · exact hge
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (q.exponent / p) := Nat.pow_le_pow_right (by norm_num) h1
      have h3k : 3 ≤ Nat.card (fixSubfield σ) := by
        rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp]
        exact hk3
      have hq : CFSG.IsQuasisimple (fixedFieldImage Tag.G2 σ) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (fixedFieldImageEquiv σ)
          (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card
            (fixSubfield σ) h3k)
      exact idxCoreAt_of_conj
        (idxCoreAt_G2_even_entrywise hp hpf hK' hk3 hσp hJC hq hNδ hnormal (hdvd σ hσp))
        (MulAut.conj h) hh
  · by_cases h3 : q.p = 3
    · have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK', h3]
      haveI hchar3 : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := by
        rw [show CFSG.LieType.Ree.ReeTag.G2.prime = 3 from rfl]
        exact h3 ▸ hKchar
      have hNF := (G2_three_exact_automorphism_normal_form q.exponent_pos K hK3).2.1
      obtain ⟨⟨y, a⟩, hya, -⟩ := hNF x
      have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
          (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.G2 K)))) = p := by
        rw [Subgroup.orderOf_mk]
        exact hxord
      obtain ⟨hpf, -, ⟨σ, hσ, hσp, hφσ, -⟩, ⟨h, hh⟩, -⟩ :=
        CFSG.RankThree.three_G2_noninner_odd_prime_local_core_trivial q.exponent_pos hK3 hp hp2
          ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp y a a.2 hya
      have hΓJ : entrywiseFixedGroup Tag.G2 σ = fixedFieldImage Tag.G2 σ :=
        CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage σ
      have hmemJ : ∀ g : ↥(adjointGroup Tag.G2 K),
          g ∈ (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) ↔
            entrywiseAdjointAut Tag.G2 σ g = g := by
        intro g
        rw [Subgroup.mem_subgroupOf]
        refine (Subgroup.ext_iff.1 hΓJ (g : ModGL Tag.G2 K)).symm.trans ?_
        rw [mem_entrywiseFixedGroup]
        constructor
        · rintro ⟨-, h⟩; exact Subtype.ext h
        · intro h; exact ⟨g.2, congrArg Subtype.val h⟩
      obtain ⟨hJC, -, -, -, -⟩ :=
        three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer q.exponent_pos
          (Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos)
          ⟨p, (Nat.div_mul_cancel hpf).symm⟩ hK3 (fixSubfield σ)
          (card_fixSubfield_eq_pow_div Nat.prime_three q.exponent_pos hK3 hp hσp)
      exact idxCoreAt_of_conj
        (idxCoreAt_G2_three_entrywise hp h3 hpf hK' hσp hJC hmemJ (hdvd σ hσp))
        (MulAut.conj h) (hh.trans hφσ)
    · have hNF := conj_normalForm_of_pointwise
        (odd_F4_and_nonexceptional_G2_automorphism_normal_form q.prime_p h2 q.exponent_pos K hK'
          .G2 (Or.inr ⟨rfl, h3⟩)).1
      obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
      have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
          (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.G2 K)))) = p := by
        rw [Subgroup.orderOf_mk]
        exact hxord
      obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ := odd_Chevalley_inner_field_noninner_prime_local_core_trivial
        Tag.G2 q.prime_p h2 q.exponent_pos K hK' hNF hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩
        hxinner hαp y σ hyσ
      have hpf : p ∣ q.exponent := by
        have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
        rwa [hσp] at this
      have hNF' : ∀ η : MulAut ↥(adjointGroup Tag.G2 K),
          ∃ gβ : ↥(adjointGroup Tag.G2 K) × (K ≃+* K),
            η = MulAut.conj gβ.1 * entrywiseAdjointAut Tag.G2 gβ.2 :=
        fun η => (hNF η).exists
      obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, -⟩ :=
        odd_entrywise_canonical_core_data h2 hNF' σ
      have hpos : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
      let q₀ : TauCeti.PrimePower := ⟨q.p, q.exponent / p, q.prime_p, hpos⟩
      have hq0card : q₀.card = q.p ^ (q.exponent / p) := TauCeti.PrimePower.card_def q₀
      have hq0 : 3 ≤ q₀.card := by
        rw [hq0card]
        have h1 : 1 ≤ q.exponent / p :=
          Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
        have hp3 : 3 ≤ q.p := by
          have h2le := q.prime_p.two_le
          omega
        calc 3 ≤ q.p ^ 1 := by simpa using hp3
          _ ≤ q.p ^ (q.exponent / p) := Nat.pow_le_pow_right q.prime_p.pos h1
      have hv₀ : (TauCeti.LieTypeIndex.G2 q₀).Valid := by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq0, by simp⟩
      have hsub : subRelC p (.G2 q) (.lie ⟨.G2 q₀, hv₀⟩) := by
        refine Or.inl ⟨trivial, ?_⟩
        show fieldSize (TauCeti.LieTypeIndex.G2 q₀) ^ p = fieldSize (TauCeti.LieTypeIndex.G2 q)
        rw [show fieldSize (TauCeti.LieTypeIndex.G2 q₀) = q₀.card from rfl,
          show fieldSize (TauCeti.LieTypeIndex.G2 q) = q.card from rfl,
          TauCeti.PrimePower.card_def q₀, TauCeti.PrimePower.card_def q, ← pow_mul,
          Nat.div_mul_cancel hpf]
      have hk : Nat.card (fixSubfield σ) = q₀.card := by
        rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp, hq0card]
      exact idxCoreAt_of_conj
        (idxCoreAt_entrywise_cat_of_simple Even.chevalleyBridgesAll.g2 hv₀ hp hk hJC hsimple hnc
          hNδ hnormal (hdvd σ hσp) hsub) δ hδ

private theorem idxCoreAt_exc_entrywise {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) (hfs : ∀ q : TauCeti.PrimePower, fieldSize (c q) = q.card)
    (hvalid : ∀ q : TauCeti.PrimePower, (c q).Valid)
    (hshape : ∀ q q' : TauCeti.PrimePower, sameShape (c q) (c q'))
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {q : TauCeti.PrimePower} (hpf : p ∣ q.exponent) (hK' : Nat.card K = q.p ^ q.exponent)
    {σ : K ≃+* K} (hσp : orderOf σ = p)
    (hJC : fixedFieldImage τ σ ≤ adjointGroup τ K)
    (hsimple : IsSimpleGroup ↥(fixedFieldImage τ σ))
    (hnc : ¬∀ a b : ↥(fixedFieldImage τ σ), a * b = b * a)
    (hNδ : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) ≤
      Subgroup.centralizer ({entrywiseAdjointAut τ σ} : Set (MulAut ↥(adjointGroup τ K))))
    (hnormal : ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer ({entrywiseAdjointAut τ σ} :
        Set (MulAut ↥(adjointGroup τ K))))).Normal)
    (hdvd : ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ)))) :
    IdxCoreAt p (c q) (entrywiseAdjointAut τ σ) := by
  have hpos : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
  let q₀ : TauCeti.PrimePower := ⟨q.p, q.exponent / p, q.prime_p, hpos⟩
  have hq0card : q₀.card = q.p ^ (q.exponent / p) := TauCeti.PrimePower.card_def q₀
  have hk : Nat.card (fixSubfield σ) = q₀.card := by
    rw [card_fixSubfield_eq_pow_div q.prime_p q.exponent_pos hK' hp hσp, hq0card]
  have hsub : subRelC p (c q) (.lie ⟨c q₀, hvalid q₀⟩) := by
    refine Or.inl ⟨hshape q q₀, ?_⟩
    show fieldSize (c q₀) ^ p = fieldSize (c q)
    rw [hfs q₀, hfs q, hq0card, TauCeti.PrimePower.card_def q, ← pow_mul,
      Nat.div_mul_cancel hpf]
  exact idxCoreAt_entrywise_cat_of_simple hB (hvalid q₀) hp hk hJC hsimple hnc hNδ hnormal hdvd
    hsub

private theorem idxCoreAt_adjointF4 {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.F4 K)) :
    ∀ x : MulAut ↥(adjointGroup Tag.F4 K), x ^ p = 1 →
      x ∉ innAutDerived ↥(adjointGroup Tag.F4 K) → IdxCoreAt p (.F4 q) x := by
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp hpq
  have hord : p ∣ CFSG.Open.ordF4 (Nat.card K) := by
    rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    exact hcard
  have hcnt : 0 < CFSG.LieType.SeitzGeneration.degCount Tag.F4
      (orderOf ((Nat.card K : ℕ) : ZMod p)) :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.degCount_F4_pos_of_dvd_ordF4 hp Nat.card_pos hpK hord
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.F4 (fixSubfield σ))) := by
    intro σ hσp
    haveI : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    refine dvd_ordF4_of_degCount_pos Nat.card_pos ?_
    rw [card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp]
    exact hcnt
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : ↥(adjointGroup Tag.F4 K) →*
      MulAut ↥(adjointGroup Tag.F4 K)).range := fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  by_cases h2 : q.p = 2
  · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      rw [show CFSG.LieType.Ree.ReeTag.F4.prime = 2 from rfl]
      exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two q.exponent_pos hK2
    have hNF := (even_F4_exact_automorphism_normal_form hf K hK2).2.1
    obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF x
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.F4 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨-, -, ⟨σ, hσ⟩, hmain, -⟩ :=
      even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hK2 hp hp2 ⊤ le_top
        ⟨x, Subgroup.mem_top x⟩ hxinner hαp y k k.isLt hyk
    obtain ⟨hσp, ψ, hψ⟩ := hmain σ hσ
    have hpf : p ∣ q.exponent := by
      have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
      rwa [hσp] at this
    obtain ⟨-, hJC, hsimple, hnc, -, -, -, hNδ, hnormal, -, -⟩ :=
      even_F4_canonical_field_centralizer_all_orders hf hK2 σ
    exact idxCoreAt_of_conj
      (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.f4 (fun _ => rfl) (fun _ => by simp)
        (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) ψ hψ
  · haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI hchar : CharP K q.p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK'
    have hNF := conj_normalForm_of_pointwise
      (odd_F4_and_nonexceptional_G2_automorphism_normal_form q.prime_p h2 q.exponent_pos K hK' .F4
        (Or.inl rfl)).1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.F4 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ := odd_Chevalley_inner_field_noninner_prime_local_core_trivial
      Tag.F4 q.prime_p h2 q.exponent_pos K hK' hNF hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩
      hxinner hαp y σ hyσ
    have hpf : p ∣ q.exponent := by
      have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
      rwa [hσp] at this
    have hNF' : ∀ η : MulAut ↥(adjointGroup Tag.F4 K),
        ∃ gβ : ↥(adjointGroup Tag.F4 K) × (K ≃+* K),
          η = MulAut.conj gβ.1 * entrywiseAdjointAut Tag.F4 gβ.2 :=
      fun η => (hNF η).exists
    obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, -⟩ :=
      odd_entrywise_canonical_core_data h2 hNF' σ
    exact idxCoreAt_of_conj
      (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.f4 (fun _ => rfl) (fun _ => by simp)
        (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) δ hδ

private theorem idxCoreAt_adjointE7 {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E7 K)) :
    ∀ x : MulAut ↥(adjointGroup Tag.E7 K), x ^ p = 1 →
      x ∉ innAutDerived ↥(adjointGroup Tag.E7 K) → IdxCoreAt p (.E7 q) x := by
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp hpq
  have hcnt : 0 < CFSG.LieType.SeitzGeneration.degCount Tag.E7
      (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_cases h3 : p = 3
    · subst h3
      exact degCount_E78_pos_three (Or.inl rfl) hpK
    · have hp5 : 5 ≤ p := by
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      exact degCount_E7_pos_of_dvd_card hp hp5 hpK hcard
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E7 (fixSubfield σ))) := by
    intro σ hσp
    haveI : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
    refine dvd_ordE7_of_degCount_pos hp hp2 Nat.card_pos ?_
    rw [card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp]
    exact hcnt
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : ↥(adjointGroup Tag.E7 K) →*
      MulAut ↥(adjointGroup Tag.E7 K)).range := fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  by_cases h2 : q.p = 2
  · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
    have hNF := conj_normalForm_of_pointwise
      (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK2 Tag.E7 (Or.inl rfl)).1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.E7 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨hσp, -, ⟨ψ, hψ⟩, -⟩ :=
      even_E7_E8_noninner_prime_field_descent_and_local_core_trivial Tag.E7 (Or.inl rfl) hf K hK2
        hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp y σ hyσ
    have hpf : p ∣ q.exponent := by
      have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
      rwa [hσp] at this
    obtain ⟨-, hJC, hsimple, hnc, -, -, -, hNδ, hnormal, -, -⟩ :=
      even_E7_E8_canonical_field_centralizer_all_orders Tag.E7 (Or.inl rfl) hf K hK2 σ
    exact idxCoreAt_of_conj
      (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e7 (fun _ => rfl) (fun _ => by simp)
        (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) ψ hψ
  · haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI hchar : CharP K q.p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK'
    haveI hcharA : CharP (AlgebraicClosure K) q.p :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q.p
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.E7 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨-, ⟨σ, δ, hσp, hδ⟩, -⟩ :=
      odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial q.prime_p h2 q.exponent_pos
        K hK' hp hp2 ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp
    obtain ⟨-, -, -, -, ρ, -, -, -, -, -, -, -, -, hfixer⟩ :=
      CFSG.RankThree.OddE7Rational.odd_E7_rational_inner_diagonal_field_automorphism_structure
        q.prime_p h2 q.exponent_pos K hK' (AlgebraicClosure K)
        (iterateFrobenius (AlgebraicClosure K) q.p q.exponent)
        (fun c => by rw [iterateFrobenius_def, hK']) _ _ rfl rfl
    have hpf : p ∣ q.exponent := by
      have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
      rwa [hσp] at this
    obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, -⟩ :=
      odd_entrywise_canonical_core_data_of_fixer (τ := .E7) h2 σ (fixer_of_rational σ hfixer)
    exact idxCoreAt_of_conj
      (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e7 (fun _ => rfl) (fun _ => by simp)
        (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) δ hδ

private theorem idxCoreAt_adjointE8 {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E8 K)) :
    ∀ x : MulAut ↥(adjointGroup Tag.E8 K), x ^ p = 1 →
      x ∉ innAutDerived ↥(adjointGroup Tag.E8 K) → IdxCoreAt p (.E8 q) x := by
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp hpq
  have hcnt : 0 < CFSG.LieType.SeitzGeneration.degCount Tag.E8
      (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_cases h3 : p = 3
    · subst h3
      exact degCount_E78_pos_three (Or.inr rfl) hpK
    · have hp5 : 5 ≤ p := by
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      exact degCount_E8_pos_of_dvd_card hp hp5 hpK hcard
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E8 (fixSubfield σ))) := by
    intro σ hσp
    haveI : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
    refine dvd_ordE8_of_degCount_pos Nat.card_pos ?_
    rw [card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp]
    exact hcnt
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : ↥(adjointGroup Tag.E8 K) →*
      MulAut ↥(adjointGroup Tag.E8 K)).range := fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  by_cases h2 : q.p = 2
  · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
    have hNF := conj_normalForm_of_pointwise
      (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK2 Tag.E8 (Or.inr rfl)).1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.E8 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨hσp, -, ⟨ψ, hψ⟩, -⟩ :=
      even_E7_E8_noninner_prime_field_descent_and_local_core_trivial Tag.E8 (Or.inr rfl) hf K hK2
        hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp y σ hyσ
    have hpf : p ∣ q.exponent := by
      have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
      rwa [hσp] at this
    obtain ⟨-, hJC, hsimple, hnc, -, -, -, hNδ, hnormal, -, -⟩ :=
      even_E7_E8_canonical_field_centralizer_all_orders Tag.E8 (Or.inr rfl) hf K hK2 σ
    exact idxCoreAt_of_conj
      (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e8 (fun _ => rfl) (fun _ => by simp)
        (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) ψ hψ
  · haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI hchar : CharP K q.p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK'
    have hNF := (odd_E8_inner_field_automorphisms_and_noninner_prime_core q.prime_p h2
      q.exponent_pos K hK').1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
    have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.E8 K)))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ := odd_Chevalley_inner_field_noninner_prime_local_core_trivial
      Tag.E8 q.prime_p h2 q.exponent_pos K hK' hNF hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩
      hxinner hαp y σ hyσ
    have hpf : p ∣ q.exponent := by
      have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
      rwa [hσp] at this
    have hNF' : ∀ η : MulAut ↥(adjointGroup Tag.E8 K),
        ∃ gβ : ↥(adjointGroup Tag.E8 K) × (K ≃+* K),
          η = MulAut.conj gβ.1 * entrywiseAdjointAut Tag.E8 gβ.2 :=
      fun η => (hNF η).exists
    obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, -⟩ :=
      odd_entrywise_canonical_core_data h2 hNF' σ
    exact idxCoreAt_of_conj
      (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e8 (fun _ => rfl) (fun _ => by simp)
        (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) δ hδ

private theorem idxCoreAt_adjointE6 {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E6 K)) :
    ∀ x : MulAut ↥(adjointGroup Tag.E6 K), x ^ p = 1 →
      x ∉ innAutDerived ↥(adjointGroup Tag.E6 K) → IdxCoreAt p (.E6 q) x := by
  have hf : 1 ≤ q.exponent := q.exponent_pos
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI hchar : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p q.exponent_pos hK'
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp hpq
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E6 (fixSubfield σ))) := by
    intro σ hσp
    by_cases h3 : p = 3
    · subst h3
      exact not_coprime_three_card_adjointE6_fixSubfield q.prime_p (Ne.symm hpq) hf hK' σ
    · have hp5 : 5 ≤ p := by
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      haveI : Finite (fixSubfield σ) := Subtype.finite
      rw [← Nat.Prime.dvd_iff_not_coprime hp,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
      refine dvd_ordE6_of_degCount_pos hp (by omega) Nat.card_pos ?_
      rw [card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp]
      exact degCount_E6_pos_of_dvd_card hp hp5 hpK hcard
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : ↥(adjointGroup Tag.E6 K) →*
      MulAut ↥(adjointGroup Tag.E6 K)).range := fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxord
  by_cases h3 : p = 3
  · subst h3
    have hxI : x ∉ e6Inndiag K := fun hmem =>
      hxo (commutator_le_innAutDerived _
        (CFSG.HardMathSupport.Dickson.Sec6.I923.e6Inndiag_le_commutator (K := K) hmem))
    have hx3 : x ^ 3 = 1 := hxp
    by_cases hℓ2 : q.p = 2
    ·
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', hℓ2]
      obtain ⟨σ, hσp, hpf, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag q.prime_p hf
        K hK' Nat.prime_three (by norm_num) hx3 hxI
      obtain ⟨f', hff'⟩ := hpf
      have hpf : 3 ∣ q.exponent := ⟨f', hff'⟩
      have hf'1 : 1 ≤ f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0, mul_zero] at hff'
          omega
        · exact h0
      obtain ⟨σ₀, hσ₀, hzp⟩ := CFSG.RankThree.PartOne.Sec66T.exists_canonical_generator hf hK2
        hσp (by norm_num) hff'
      have hσ₀ord : orderOf σ₀ = 3 := by
        rw [← Nat.card_zpowers, ← hzp, Nat.card_zpowers, hσp]
      have hK'' : Nat.card K = 2 ^ (f' * 3) := by rw [hK', hℓ2, hff', mul_comm]
      obtain ⟨-, -, -, hJC, hsimple, hnc, -, hNδ, hnormal, -, -⟩ :=
        even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hf'1 (by norm_num) K
          hK'' σ₀ hσ₀
      have hcore : IdxCoreAt 3 (.E6 q) (entrywiseAdjointAut Tag.E6 σ₀) :=
        idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e6 (fun _ => rfl) (fun _ => by simp)
          (fun _ _ => trivial) Nat.prime_three hpf hK' hσ₀ord hJC hsimple hnc hNδ hnormal
          (hdvd σ₀ hσ₀ord)
      have hz : Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ) =
          Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ₀) := by
        have h1 := MonoidHom.map_zpowers
          (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ
        have h2 := MonoidHom.map_zpowers
          (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ₀
        rw [hzp] at h1
        exact h1.symm.trans h2
      exact idxCoreAt_of_conj
        (idxCoreAt_of_fixSubgroup_eq (fixSub_eq_of_zpowers_eq hz.symm) hcore) ψ hψ
    ·
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      haveI hchar : CharP K q.p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          q.prime_p q.exponent_pos hK'
      haveI hcharA : CharP (AlgebraicClosure K) q.p :=
        charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q.p
      obtain ⟨σ, hσp, hpf, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag q.prime_p hf
        K hK' Nat.prime_three (by norm_num) hx3 hxI
      obtain ⟨-, -, -, -, ρ, -, -, -, -, -, -, -, -, -, -, -, hfixer⟩ :=
        CFSG.RankThree.PartOne.KE.odd_E6_rational_inner_diagonal_graph_field_automorphism_structure
          q.prime_p hℓ2 hf K hK' (AlgebraicClosure K)
          (iterateFrobenius (AlgebraicClosure K) q.p q.exponent)
          (fun c => by rw [iterateFrobenius_def, hK']) _ _ rfl rfl
      obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, -⟩ :=
        odd_entrywise_canonical_core_data_of_fixer (τ := .E6) hℓ2 σ (fixer_of_rational σ hfixer)
      exact idxCoreAt_of_conj
        (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e6 (fun _ => rfl) (fun _ => by simp)
          (fun _ _ => trivial) Nat.prime_three hpf hK' hσp hJC hsimple hnc hNδ hnormal
          (hdvd σ hσp)) ψ hψ
  · have hp5 : 5 ≤ p := by
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    by_cases hℓ2 : q.p = 2
    ·
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', hℓ2]
      obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
      obtain ⟨⟨σ, -, hσp, ψ, hψ⟩, ⟨f', hff'⟩, -⟩ :=
        even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK2 Θ hΘ hp
          (by omega) ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp
      have hf'1 : 1 ≤ f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0, mul_zero] at hff'
          omega
        · exact h0
      obtain ⟨σ₀, hσ₀, hzp⟩ := CFSG.RankThree.PartOne.Sec66T.exists_canonical_generator hf hK2
        hσp hp.pos hff'
      have hσ₀ord : orderOf σ₀ = p := by
        rw [← Nat.card_zpowers, ← hzp, Nat.card_zpowers, hσp]
      have hK'' : Nat.card K = 2 ^ (f' * p) := by rw [hK', hℓ2, hff', mul_comm]
      obtain ⟨-, -, -, hJC, hsimple, hnc, -, hNδ, hnormal, -, -⟩ :=
        even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hf'1 hp.two_le K hK''
          σ₀ hσ₀
      have hpf : p ∣ q.exponent := ⟨f', hff'⟩
      have hcore : IdxCoreAt p (.E6 q) (entrywiseAdjointAut Tag.E6 σ₀) :=
        idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e6 (fun _ => rfl) (fun _ => by simp)
          (fun _ _ => trivial) hp hpf hK' hσ₀ord hJC hsimple hnc hNδ hnormal (hdvd σ₀ hσ₀ord)
      have hz : Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ) =
          Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ₀) := by
        have h1 := MonoidHom.map_zpowers
          (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ
        have h2 := MonoidHom.map_zpowers
          (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ₀
        rw [hzp] at h1
        exact h1.symm.trans h2
      exact idxCoreAt_of_conj
        (idxCoreAt_of_fixSubgroup_eq (fixSub_eq_of_zpowers_eq hz.symm) hcore) ψ hψ
    ·
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      haveI hchar : CharP K q.p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          q.prime_p q.exponent_pos hK'
      haveI hcharA : CharP (AlgebraicClosure K) q.p :=
        charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q.p
      obtain ⟨-, ⟨σ, δ, hσp, hδ⟩, -⟩ :=
        CFSG.RankThree.PartOne.KE.odd_E6_noninner_large_prime_field_descent_and_local_core_trivial
          q.prime_p hℓ2 hf K hK' hp (by omega) ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp
      obtain ⟨-, -, -, -, ρ, -, -, -, -, -, -, -, -, -, -, -, hfixer⟩ :=
        CFSG.RankThree.PartOne.KE.odd_E6_rational_inner_diagonal_graph_field_automorphism_structure
          q.prime_p hℓ2 hf K hK' (AlgebraicClosure K)
          (iterateFrobenius (AlgebraicClosure K) q.p q.exponent)
          (fun c => by rw [iterateFrobenius_def, hK']) _ _ rfl rfl
      have hpf : p ∣ q.exponent := by
        have := (card_fixSubfield q.prime_p q.exponent_pos hK' σ).1
        rwa [hσp] at this
      obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, -⟩ :=
        odd_entrywise_canonical_core_data_of_fixer (τ := .E6) hℓ2 σ (fixer_of_rational σ hfixer)
      exact idxCoreAt_of_conj
        (idxCoreAt_exc_entrywise Even.chevalleyBridgesAll.e6 (fun _ => rfl) (fun _ => by simp)
          (fun _ _ => trivial) hp hpf hK' hσp hJC hsimple hnc hNδ hnormal (hdvd σ hσp)) δ hδ

theorem lieOuterIdx_excUntwisted : LieOuterIdx isExcUntwistedIdx := by
  intro d p hp hp2 hpc hP hpdvd hnExc
  obtain ⟨i, hv⟩ := d
  cases i with
  | G2 q =>
    rw [TauCeti.LieTypeIndex.characteristic_G2] at hpc
    obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    haveI : Finite (ModGL Tag.G2 K) := finite_modGL
    haveI : Finite ↥(adjointGroup Tag.G2 K) := Subtype.finite
    have hK' : Nat.card K = q.p ^ q.exponent := hKcard.trans (TauCeti.PrimePower.card_def q)
    have hpdvd' : p ∣ Nat.card ↥(adjointGroup Tag.G2 K) := by
      rw [← Nat.card_congr eK.toEquiv]
      exact hpdvd
    have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact outerIdxAt_of_mulEquiv hp eK.symm
      (outerIdxAt_of_idxCoreAt hp (idxCoreAt_adjointG2 hq3 hKcard hK' hKchar hp hp2 hpc hpdvd'))
  | F4 q =>
    rw [TauCeti.LieTypeIndex.characteristic_F4] at hpc
    obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
    haveI : Finite (ModGL Tag.F4 K) := finite_modGL
    haveI : Finite ↥(adjointGroup Tag.F4 K) := Subtype.finite
    have hK' : Nat.card K = q.p ^ q.exponent := hKcard.trans (TauCeti.PrimePower.card_def q)
    have hpdvd' : p ∣ Nat.card ↥(adjointGroup Tag.F4 K) := by
      rw [← Nat.card_congr eK.toEquiv]
      exact hpdvd
    exact outerIdxAt_of_mulEquiv hp eK.symm
      (outerIdxAt_of_idxCoreAt hp (idxCoreAt_adjointF4 hKcard hK' hp hp2 hpc hpdvd'))
  | E6 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E6] at hpc
    obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
    haveI : Finite (ModGL Tag.E6 K) := finite_modGL
    haveI : Finite ↥(adjointGroup Tag.E6 K) := Subtype.finite
    have hK' : Nat.card K = q.p ^ q.exponent := hKcard.trans (TauCeti.PrimePower.card_def q)
    have hpdvd' : p ∣ Nat.card ↥(adjointGroup Tag.E6 K) := by
      rw [← Nat.card_congr eK.toEquiv]
      exact hpdvd
    exact outerIdxAt_of_mulEquiv hp eK.symm
      (outerIdxAt_of_idxCoreAt hp (idxCoreAt_adjointE6 hKcard hK' hp hp2 hpc hpdvd'))
  | E7 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E7] at hpc
    obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
    haveI : Finite (ModGL Tag.E7 K) := finite_modGL
    haveI : Finite ↥(adjointGroup Tag.E7 K) := Subtype.finite
    have hK' : Nat.card K = q.p ^ q.exponent := hKcard.trans (TauCeti.PrimePower.card_def q)
    have hpdvd' : p ∣ Nat.card ↥(adjointGroup Tag.E7 K) := by
      rw [← Nat.card_congr eK.toEquiv]
      exact hpdvd
    exact outerIdxAt_of_mulEquiv hp eK.symm
      (outerIdxAt_of_idxCoreAt hp (idxCoreAt_adjointE7 hKcard hK' hp hp2 hpc hpdvd'))
  | E8 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E8] at hpc
    obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
    haveI : Finite (ModGL Tag.E8 K) := finite_modGL
    haveI : Finite ↥(adjointGroup Tag.E8 K) := Subtype.finite
    have hK' : Nat.card K = q.p ^ q.exponent := hKcard.trans (TauCeti.PrimePower.card_def q)
    have hpdvd' : p ∣ Nat.card ↥(adjointGroup Tag.E8 K) := by
      rw [← Nat.card_congr eK.toEquiv]
      exact hpdvd
    exact outerIdxAt_of_mulEquiv hp eK.symm
      (outerIdxAt_of_idxCoreAt hp (idxCoreAt_adjointE8 hKcard hK' hp hp2 hpc hpdvd'))
  | A n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedA n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | B n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | C n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | D n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedD n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedE6 q => exact absurd hP (by simp [isExcUntwistedIdx])
  | trialityD4 q => exact absurd hP (by simp [isExcUntwistedIdx])
  | suzuki k => exact absurd hP (by simp [isExcUntwistedIdx])
  | reeG2 k => exact absurd hP (by simp [isExcUntwistedIdx])
  | reeF4 k => exact absurd hP (by simp [isExcUntwistedIdx])
  | tits => exact absurd hP (by simp [isExcUntwistedIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
