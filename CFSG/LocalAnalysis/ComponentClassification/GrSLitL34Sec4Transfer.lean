module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoCentralCore
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G]

theorem map_centralizer_subtype (M : Subgroup G) (a : M) :
    (centralizer ({a} : Set M)).map M.subtype = M ⊓ centralizer ({(a : G)} : Set G) := by
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, subtype_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, congrArg Subtype.val hz⟩
  · rintro ⟨hyM, hy⟩
    exact ⟨⟨y, hyM⟩, Subtype.ext hy, rfl⟩

theorem map_subgroupOf_subtype {M J : Subgroup G} (hJM : J ≤ M) :
    (J.subgroupOf M).map M.subtype = J := by
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hJM]

theorem map_conjugate_subtype (M : Subgroup G) (K : Subgroup M) (g : M) :
    (conjugate K g).map M.subtype = conjugate (K.map M.subtype) (g : G) := by
  unfold conjugate
  rw [map_map, map_map]
  rfl

theorem isPComponent_centralizer_subgroupOf [Finite G] {M J : Subgroup G} {a : G} (haM : a ∈ M)
    (hJM : J ≤ M) (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) :
    J.subgroupOf M ≤ centralizer ({(⟨a, haM⟩ : M)} : Set M) ∧
      IsPComponent 2 ((J.subgroupOf M).subgroupOf (centralizer ({(⟨a, haM⟩ : M)} : Set M))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a' : M := ⟨a, haM⟩
  set C' : Subgroup M := centralizer ({a'} : Set M)
  have hle : J.subgroupOf M ≤ C' := by
    intro j hj
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJa (mem_subgroupOf.mp hj)))
  refine ⟨hle, ?_⟩
  rw [← CatFactsSp4.isPComponent_map_subgroupOf_iff 2 M.subtype M.subtype_injective hle,
    map_subgroupOf_subtype hJM, map_centralizer_subtype]
  exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJM hJa) inf_le_right hJ

theorem mem_oddIn_centralizer_subgroupOf [Finite G] {M : Subgroup G} {x : G} (hxM : x ∈ M)
    {d : G} (hdM : d ∈ M) (hd : d ∈ oddIn (centralizer ({x} : Set G))) :
    (⟨d, hdM⟩ : M) ∈ oddIn (centralizer ({(⟨x, hxM⟩ : M)} : Set M)) := by
  set x' : M := ⟨x, hxM⟩
  set H : Subgroup M := centralizer ({x'} : Set M)
  set D : Subgroup M := (oddIn (centralizer ({x} : Set G))).subgroupOf M
  have hDH : D ≤ H := by
    intro y hy
    have hy' := (map_subtype_le _ : oddIn (centralizer ({x} : Set G)) ≤ centralizer ({x} : Set G))
      (mem_subgroupOf.mp hy)
    rw [mem_centralizer_singleton_iff] at hy' ⊢
    exact Subtype.ext hy'
  have hnorm : ∀ h ∈ H, ∀ y ∈ D, h * y * h⁻¹ ∈ D := by
    intro h hh y hy
    rw [mem_subgroupOf] at hy ⊢
    have hh' : (h : G) ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hh ⊢
      exact congrArg Subtype.val hh
    simpa using conj_mem_oddIn hh' hy
  have hodd : Odd (Nat.card D) := by
    have h1 : Nat.card D ∣ Nat.card (oddIn (centralizer ({x} : Set G))) := by
      rw [← card_map_of_injective M.subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat (odd_card_map_pPrimeCore _) h1
  exact le_map_pPrimeCore hDH hnorm hodd (mem_subgroupOf.mpr (by simpa using hd))

theorem oddIn_inf_le_normalizer (hSol : SolomonCommutingCoreInput) {X : Type} [Group X]
    [Finite X] {e u : X} (he : orderOf e = 2) (hu : orderOf u = 2) (heu : e * u = u * e)
    {L : Subgroup X} (hLu : L ≤ centralizer ({u} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({u} : Set X)))) :
    oddIn (centralizer ({e} : Set X)) ⊓ centralizer ({u} : Set X) ≤ normalizer (L : Set X) := by
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he; exact absurd he (by norm_num)
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; exact absurd hu (by norm_num)
  have he2 : e * e = 1 := by rw [← pow_two, ← he, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hS := isElemTwo_zpowers he2
  have hT := isElemTwo_zpowers hu2
  have hST : ∀ y ∈ zpowers e, ∀ z ∈ zpowers u, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_zpow (show Commute e u from heu) i j)).eq
  have h := hSol X (zpowers e) (zpowers u)
    (fun hb => he1 (by rw [← mem_bot, ← hb]; exact mem_zpowers e))
    (fun hb => hu1 (by rw [← mem_bot, ← hb]; exact mem_zpowers u))
    hS.1 hS.2 hT.1 hT.2 hST
  obtain ⟨-, h2, -⟩ := h
  have hLu' : L ≤ centralizer (zpowers u : Set X) := by rwa [centralizer_zpowers_eq]
  have hL' : IsPComponent 2 (L.subgroupOf (centralizer (zpowers u : Set X))) := by
    rwa [centralizer_zpowers_eq]
  have h3 := (h2 L hLu' hL').1
  rwa [centralizer_zpowers_eq, centralizer_zpowers_eq] at h3

theorem commutator_le_left_of_le_normalizer {H K : Subgroup G}
    (hK : K ≤ normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  have h1 : k * h⁻¹ * k⁻¹ ∈ H := (mem_normalizer_iff.mp (hK hk) h⁻¹).mp (inv_mem hh)
  rw [show h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) by group]
  exact mul_mem hh h1

theorem gsUnbalancingTriple_subgroupOf [Finite G] (hSol : SolomonCommutingCoreInput)
    {M J : Subgroup G} {a x : G} (h : GSUnbalancingTriple a x J) (haM : a ∈ M) (hxM : x ∈ M)
    (hJM : J ≤ M) (hDM : oddIn (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G) ≤ M) :
    GSUnbalancingTriple (⟨a, haM⟩ : M) ⟨x, hxM⟩ (J.subgroupOf M) := by
  obtain ⟨ha, hx, hax, hJa, hJ, hJx, hJD⟩ := gsUnbalancingTriple_iff.mp h
  set a' : M := ⟨a, haM⟩
  set x' : M := ⟨x, hxM⟩
  set J' : Subgroup M := J.subgroupOf M
  have ha' : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hx' : orderOf x' = 2 := by rw [← Subgroup.orderOf_coe]; exact hx
  have hax' : a' * x' = x' * a' := Subtype.ext hax
  obtain ⟨hJa', hJ'⟩ := isPComponent_centralizer_subgroupOf haM hJM hJa hJ
  have hinj : Function.Injective (map M.subtype) := map_injective M.subtype_injective
  have hmapJ : J'.map M.subtype = J := map_subgroupOf_subtype hJM
  refine gsUnbalancingTriple_iff.mpr ⟨ha', hx', hax', hJa', hJ', ?_, ?_⟩
  · apply hinj
    rw [map_commutator, hmapJ, MonoidHom.map_zpowers]
    exact hJx
  · set D' : Subgroup M := oddIn (centralizer ({x'} : Set M)) ⊓ centralizer ({a'} : Set M)
    set D₁ : Subgroup M :=
      (oddIn (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G)).subgroupOf M
    have hD₁ : D₁ ≤ D' := by
      intro d hd
      have hd' := mem_subgroupOf.mp hd
      refine mem_inf.mpr ⟨mem_oddIn_centralizer_subgroupOf hxM d.2 (mem_inf.mp hd').1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hd').2)
    have hmapD : D₁.map M.subtype =
        oddIn (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G) :=
      map_subgroupOf_subtype hDM
    have heq₁ : ⁅J', D₁⁆ = J' := by
      apply hinj
      rw [map_commutator, hmapJ, hmapD]
      exact hJD
    have hDN : D' ≤ normalizer (J' : Set M) :=
      oddIn_inf_le_normalizer hSol hx' ha' hax'.symm hJa' hJ'
    exact le_antisymm (commutator_le_left_of_le_normalizer hDN)
      (heq₁.symm.le.trans (commutator_mono le_rfl hD₁))

theorem isL34Type_subgroupOf {M J : Subgroup G} (hJM : J ≤ M)
    (h : IsL34Type (J ⧸ Open.fusionZStar J)) :
    IsL34Type (J.subgroupOf M ⧸ Open.fusionZStar (J.subgroupOf M)) :=
  GSThmB.OddQuot.lieModel_of_equiv
    (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hJM).symm) h

theorem isL34Type_map_subtype {M : Subgroup G} {K : Subgroup M}
    (h : IsL34Type (K ⧸ Open.fusionZStar K)) :
    IsL34Type (K.map M.subtype ⧸ Open.fusionZStar (K.map M.subtype)) :=
  GSThmB.OddQuot.lieModel_of_equiv
    (Sol78.fusionZStarQuotCongr (K.equivMapOfInjective M.subtype M.subtype_injective)) h

theorem exists_component_of_unbalancedKGroup [Finite G] (hKG : L34UnbalancedKGroupInput)
    (hSol : SolomonCommutingCoreInput) (hK : Assembly.KProper Blueprint.Catalog G)
    {M J : Subgroup G} (hM : M ≠ ⊤) {a x : G} (h : GSUnbalancingTriple a x J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (haM : a ∈ M) (hxM : x ∈ M) (hJM : J ≤ M)
    (hDM : oddIn (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G) ≤ M) :
    ∃ K : Subgroup G, K ≤ M ∧ IsPComponent 2 (K.subgroupOf M) ∧
      ((IsL34Type (K ⧸ Open.fusionZStar K) ∧ J ⊔ oddIn M = K ⊔ oddIn M) ∨
        (Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) ∧ J ≤ K ⊔ oddIn M) ∨
        (IsL34Type (K ⧸ Open.fusionZStar K) ∧ conjugate K a ≠ K ∧
          J ≤ K ⊔ conjugate K a ⊔ oddIn M)) := by
  have hM' : SectionRank.IsKGroupCat ↥M := isKGroupCat_of_ne_top hK hM
  obtain ⟨K, hKc, hcase⟩ := hKG ↥M hM' ⟨a, haM⟩ ⟨x, hxM⟩ (J.subgroupOf M)
    (gsUnbalancingTriple_subgroupOf hSol h haM hxM hJM hDM) (isL34Type_subgroupOf hJM hL34)
  set K' : Subgroup G := K.map M.subtype with hK'
  have hmapJ : (J.subgroupOf M).map M.subtype = J := map_subgroupOf_subtype hJM
  have hmapO : (pPrimeCore 2 ↥M).map M.subtype = oddIn M := rfl
  have heK : K ≃* K' := K.equivMapOfInjective M.subtype M.subtype_injective
  refine ⟨K', map_subtype_le K, GrSLit.isPComponent_map_subgroupOf hKc, ?_⟩
  rcases hcase with ⟨hT, heq⟩ | ⟨⟨e⟩, hle⟩ | ⟨hT, hne, hle⟩
  · refine Or.inl ⟨isL34Type_map_subtype hT, ?_⟩
    have := congrArg (map M.subtype) heq
    rwa [Subgroup.map_sup, Subgroup.map_sup, hmapJ, hmapO] at this
  · refine Or.inr (Or.inl ⟨⟨(Sol78.coreQuotCongr heK).symm.trans e⟩, ?_⟩)
    have := map_mono (f := M.subtype) hle
    rwa [Subgroup.map_sup, hmapJ, hmapO] at this
  · refine Or.inr (Or.inr ⟨isL34Type_map_subtype hT, fun hc => hne ?_, ?_⟩)
    · apply map_injective M.subtype_injective
      rw [map_conjugate_subtype]
      exact hc
    · have := map_mono (f := M.subtype) hle
      rwa [Subgroup.map_sup, Subgroup.map_sup, hmapJ, hmapO, map_conjugate_subtype] at this

end CFSG.ComponentClassification.GrSLit.GrS4
