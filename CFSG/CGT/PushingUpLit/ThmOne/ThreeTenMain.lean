module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeTenStab
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeTenOff
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeSixMain
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneOmegaNorm
public import CFSG.CGT.PushingUpLit.ThmOne.OmegaNormMain

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ThreeTen.exists_omegaFourOutcomeSharp_normalizer (hA : AschbacherEmbeddingAmbK')
    {X R H : Subgroup G} (hX : InClassX ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsMaximalTwoLocal H)
    (hHc : IsCharacteristicP 2 ↥H) (hK : CFSG.IsKGroup ↥H) (hns : ¬ (X.subgroupOf H).IsSubnormal)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) :
    ∃ D : Subgroup G, X ≤ D ∧ D ≤ H ∧
      IsPGroup 2 ↥(D ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G)) ∧
      OmegaFourOutcomeSharp (omegaOneCenterIn (oTwoIn H)) X D ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  obtain ⟨D, hYD, hDs, -, hD2, hΩ⟩ :=
    exists_omegaFourOutcomeSharp_subgroupOf hA hX hR hXR hsub hNH hH hHc hK hns hmax
  have hXH : X ≤ H := hXR.trans hNH
  have hV : IsElemAbelian 2 (omegaOneCenterIn (pCore 2 ↥H)) :=
    (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp
      (isElementaryAbelian_omegaOneCenterIn _)
  have : (omegaOneCenterIn (pCore 2 ↥H)).Normal := SixThree.normal_omegaOneCenterIn _
  have hNN := normalizer_le_normalizer_of_omegaFourOutcomeSharp hV hΩ hYD hDs hD2
  refine ⟨D.map H.subtype, ?_, Subgroup.map_subtype_le D, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hXH]
    exact Subgroup.map_mono hYD
  · refine (hD2.map H.subtype).to_le ?_
    rintro g ⟨⟨d, hdD, rfl⟩, hgC⟩
    exact ⟨d, Subgroup.mem_inf.mpr ⟨hdD, ThreeSix.subgroupOf_le_centralizer_omegaOneCenterIn le_rfl
      (show d ∈ (Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G)).subgroupOf H
        from hgC)⟩, rfl⟩
  · have h := ThreeSix.omegaFourOutcomeSharp_map H.subtype_injective hΩ
    rwa [ThreeSix.map_omegaOneCenterIn_pCore, Subgroup.map_subgroupOf_eq_of_le hXH] at h
  · rintro g ⟨hgH, hgN⟩
    have h1 : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.normalizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [← ThreeSix.map_mem_normalizer_map_iff H.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hXH]
      exact hgN
    exact coe_mem_normalizer_map (hNN h1)

theorem ThreeTen.not_le_centralizer_of_isSubnormal {X M R D W V : Subgroup G}
    (hX : oResidualTwo ↥X = ⊤) (hsub : (X.subgroupOf M).IsSubnormal) (hXD : X ≤ D)
    (hnsD : ¬ (X.subgroupOf D).IsSubnormal) (hNV : Subgroup.normalizer (V : Set G) ≤ M)
    (hVR : V ≤ R) (hWV : W ≤ V) (hUW : blockU X ≤ W) (hDW : D ≤ Subgroup.normalizer (W : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hRC : R ≤ centralizerModCore X)
    (hDCR : D ⊓ Subgroup.centralizer (W : Set G) ≤ R) :
    ¬ V ≤ Subgroup.centralizer (W : Set G) := by
  intro hVC
  refine hnsD (isSubnormal_of_conj_le hsub hXD fun h hh x hx => hNV ?_)
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have hvR := hVR hv
  have hcD : h * v * h⁻¹ * v⁻¹ ∈ D := by
    have h1 : v * h⁻¹ * v⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hRD hvR) _).mp (D.inv_mem hh)
    simpa [mul_assoc] using D.mul_mem hh h1
  have hcC : h * v * h⁻¹ * v⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
    mul_mem (ThreeTen.mem_centralizer_conj_of_normalizes (hDW hh) (hVC hv)) (inv_mem (hVC hv))
  have hv'R : h * v * h⁻¹ ∈ R := by
    simpa using R.mul_mem (hDCR ⟨hcD, hcC⟩) hvR
  have hc : x * (h * v * h⁻¹) * x⁻¹ * (h * v * h⁻¹)⁻¹ ∈ blockU X := by
    have e : x * (h * v * h⁻¹) * x⁻¹ * (h * v * h⁻¹)⁻¹ =
        ((h * v * h⁻¹) * x * (h * v * h⁻¹)⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (commutator_mem_blockU_of_mem_centralizerModCore hX (hRC hv'R) hx)
  have hc' : h⁻¹ * (x * (h * v * h⁻¹) * x⁻¹ * (h * v * h⁻¹)⁻¹) * h ∈ V := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hDW (D.inv_mem hh)) _).mp (hUW hc)
    rw [inv_inv] at h1
    exact hWV h1
  have e : h⁻¹ * x * h * v * (h⁻¹ * x * h)⁻¹ =
      h⁻¹ * (x * (h * v * h⁻¹) * x⁻¹ * (h * v * h⁻¹)⁻¹) * h * v := by group
  rw [e]
  exact V.mul_mem hc' hv

theorem ThreeTen.false_of_omegaFourOutcomeSharp {X M R D V : Subgroup G} (hX : IsShortGroup ↥X)
    (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M})
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) (hV : IsElemAbelian 2 V) (hVR : V ≤ R)
    (hDV : D ≤ Subgroup.normalizer (V : Set G)) (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hXD : X ≤ D) (hVX : ⁅V, X⁆ = blockU X)
    (hΩ : OmegaFourOutcomeSharp V X D) (hDCR : D ⊓ Subgroup.centralizer (V : Set G) ≤ R) :
    False := by
  have hRC : R ≤ centralizerModCore X := hR.1.trans inf_le_left
  have hV2 : IsPGroup 2 ↥V := hR.2.1.to_le hVR
  obtain ⟨n, hn, -, hUW, hnat⟩ := ThreeSix.card_blockU_of_omegaFourOutcomeSharp hXD hVX hΩ
  have hRW := commutator_le_blockU_of_omegaFourOutcomeSharp_of_le_centralizerModCore hV hDV hΩ
    hXD hX hVX hR.2.1 hRD hRV hRC
  obtain ⟨hres, -, -, -, -, -, -, hWC, hDCV, hnsD, -⟩ := hΩ
  have hWV : ⁅D, V⁆ ≤ V := commutator_le_of_le_normalizer hDV
  have hWe : IsElemAbelian 2 ⁅D, V⁆ := OmegaNorm.isElemAbelian_of_le_omega hV hWV
  have hDW : D ≤ Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G) := fun d hd =>
    OmegaNorm.mem_normalizer_commutator_omega (Subgroup.le_normalizer hd) (hDV hd)
  have hRW' : R ≤ Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G) := fun r hr =>
    OmegaNorm.mem_normalizer_commutator_omega (hRD hr) (hRV hr)
  have hWD : ⁅D, ⁅D, V⁆⁆ = ⁅D, V⁆ := by
    have h := SixThree.commutator_commutator_eq (SubTwo.noTwoQuotient_of_oResidualTwo hres) hV2
      hDV
    rw [Subgroup.commutator_comm V D] at h
    rw [Subgroup.commutator_comm D ⁅D, V⁆]
    exact h
  have hV'R := normalClosureIn_le_of_commutator_le hX hMc hXM hsub hR (hWV.trans hVR) hRW
  have hWV' : ⁅D, V⁆ ≤ normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) ⁅D, V⁆ :=
    le_normalClosureIn
  have hV'1 : normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) ⁅D, V⁆ ≠ ⊥ :=
    fun h => blockU_ne_bot_of_short hX (le_bot_iff.mp (h ▸ hUW.trans hWV'))
  have hNV := normalizer_normalClosureIn_le_of_threeOne h31 hXM (hXD.trans hDW)
    (hR.2.1.to_le hV'R) hV'1
  have h311 := ThreeTen.not_le_centralizer_of_isSubnormal hX.residual_eq hsub hXD hnsD hNV hV'R
    hWV' hUW hDW hRD hRC ((le_inf inf_le_left hDCV).trans hDCR)
  refine h311 ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨k, hk, w, hw, rfl⟩
  have hmem : ∀ g ∈ M ⊓ Subgroup.centralizer (blockU X : Set G),
      (⁅D, V⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (D : Set G) ⊓ Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G) := by
    rintro g hg _ ⟨w', hw', rfl⟩
    have h1 : (MulAut.conj g).toMonoidHom w' ∈ R :=
      hV'R (Subgroup.subset_closure ⟨g, hg, w', hw', rfl⟩)
    exact ⟨hRD h1, hRW' h1⟩
  exact ThreeTen.le_centralizer_of_isNatBy hWe hDW hn hnat hWC hWD (hmem k hk)
    (hmem k⁻¹ (inv_mem hk)) ⟨w, hw, rfl⟩

theorem false_of_threeSix (hA : AschbacherEmbeddingAmbK') {X M R H : Subgroup G}
    (hX : InClassX ↥X) (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M})
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) (hH : IsMaximalTwoLocal H)
    (hHc : IsCharacteristicP 2 ↥H) (hK : CFSG.IsKGroup ↥H)
    (hJH : Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ≤ H)
    (hns : ¬ (X.subgroupOf H).IsSubnormal)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) : False := by
  obtain ⟨hR', hXR, hsub', hNH⟩ := ThreeSix.hyps_of_sectionThree hX.1 hMc hXM hsub h31 hR hJH
  obtain ⟨hOR, -, -, hVX, -, -, hSyl, -⟩ := threeSix_facts hX.1 hMc hXM hsub h31 hR hHc hJH hns
  obtain ⟨D, hXD, hDH, hD2, hΩ, hND⟩ :=
    ThreeTen.exists_omegaFourOutcomeSharp_normalizer hA hX hR' hXR hsub' hNH hH hHc hK hns hmax
  have hHV := ThreeSix.le_normalizer_omegaOneCenterIn H
  have hRH : R ≤ H := Subgroup.le_normalizer.trans hNH
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := fun r hr =>
    hND ⟨hRH hr, (hR'.1.trans (Glue.centralizerModCore_le_normalizer X)) hr⟩
  have hDC : D ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) ≤ R := by
    refine (ThreeTen.le_of_isSylowOf_of_normalizes_two hSyl hD2 (inf_le_inf_right _ hDH)
      fun r hr => ?_).trans inf_le_left
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hRD (Subgroup.mem_inf.mp hr).1, ?_⟩
    exact Subgroup.mem_normalizer_fintype fun c hc =>
      ThreeTen.mem_centralizer_conj_of_normalizes (hHV (hRH (Subgroup.mem_inf.mp hr).1)) hc
  exact ThreeTen.false_of_omegaFourOutcomeSharp hX.1 hMc hXM hsub h31 hR
    ((SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp
      (isElementaryAbelian_omegaOneCenterIn _))
    ((omegaOneCenterIn_le _).trans hOR) (hDH.trans hHV) (hRH.trans hHV) hRD hXD hVX hΩ hDC

end CFSG.CGT.PushingUpLit.ThmOne
