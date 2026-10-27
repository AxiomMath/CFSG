module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aKernel
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace OddQuot

section General

variable {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']

omit [Finite H] [Finite H'] in
theorem subtype_comp_subgroupMap (φ : H →* H') (X : Subgroup H) :
    (X.map φ).subtype.comp (φ.subgroupMap X) = φ.comp X.subtype := rfl

omit [Finite H] [Finite H'] in
theorem ker_subgroupMap_eq (φ : H →* H') (X : Subgroup H) :
    (φ.subgroupMap X).ker = (φ.domRestrict X).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

omit [Finite H] [Finite H'] in
theorem not_two_dvd_card_ker_domRestrict (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker)
    (X : Subgroup H) : ¬ 2 ∣ Nat.card (φ.domRestrict X).ker :=
  Nat.prime_two.coprime_iff_not_dvd.mp (CatalogueBPrimeJoin.coprime_card_restriction_kernel 2 φ
    (Nat.prime_two.coprime_iff_not_dvd.mpr hφ) X)

omit [Finite H] [Finite H'] in
theorem not_two_dvd_card_ker_subgroupMap (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker)
    (X : Subgroup H) : ¬ 2 ∣ Nat.card (φ.subgroupMap X).ker := by
  rw [ker_subgroupMap_eq]
  exact not_two_dvd_card_ker_domRestrict φ hφ X

omit [Finite H] [Finite H'] in
theorem map_subgroupOf_subgroupMap (φ : H →* H') {L X : Subgroup H} (hLX : L ≤ X) :
    (L.subgroupOf X).map (φ.subgroupMap X) = (L.map φ).subgroupOf (X.map φ) := by
  ext ⟨y, hy⟩
  rw [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨x, hxL, hxy⟩
    exact mem_map.mpr ⟨x, hxL, congrArg Subtype.val hxy⟩
  · intro hyL
    obtain ⟨x, hxL, hxy⟩ := mem_map.mp hyL
    exact ⟨⟨x, hLX hxL⟩, hxL, Subtype.ext hxy⟩

theorem map_oddCoreIn (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker) (X : Subgroup H) :
    (oddCoreIn X).map φ = oddCoreIn (X.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (prime_complement_kernel_core_preimage (φ.subgroupMap X) (φ.subgroupMap_surjective X)
    (not_two_dvd_card_ker_subgroupMap φ hφ X)).2
  unfold oddCoreIn
  rw [← h, map_map, map_map, subtype_comp_subgroupMap]

theorem map_layerIn (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker) (X : Subgroup H) :
    (layerIn X).map φ = layerIn (X.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel (φ.subgroupMap X)
    (φ.subgroupMap_surjective X) (not_two_dvd_card_ker_subgroupMap φ hφ X)
  unfold layerIn
  rw [← h, map_map, map_map, subtype_comp_subgroupMap]

theorem isPComponent_map (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker) {L X : Subgroup H}
    (hLX : L ≤ X) (hL : IsPComponent 2 (L.subgroupOf X)) :
    IsPComponent 2 ((L.map φ).subgroupOf (X.map φ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (φ.subgroupMap X) (φ.subgroupMap_surjective X) (not_two_dvd_card_ker_subgroupMap φ hφ X)
  rw [← map_subgroupOf_subgroupMap φ hLX]
  exact hbij.mapsTo hL

theorem eq_of_map_eq (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker) {L M X : Subgroup H}
    (hLX : L ≤ X) (hMX : M ≤ X) (hL : IsPComponent 2 (L.subgroupOf X))
    (hM : IsPComponent 2 (M.subgroupOf X)) (h : L.map φ = M.map φ) : L = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (φ.subgroupMap X) (φ.subgroupMap_surjective X) (not_two_dvd_card_ker_subgroupMap φ hφ X)
  have h1 : L.subgroupOf X = M.subgroupOf X := hbij.injOn hL hM (by
    rw [map_subgroupOf_subgroupMap φ hLX, map_subgroupOf_subgroupMap φ hMX, h])
  rwa [subgroupOf_inj, inf_of_le_left hLX, inf_of_le_left hMX] at h1

theorem nonempty_quotient_pPrimeCore_equiv (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker)
    (X : Subgroup H) : Nonempty (X ⧸ pPrimeCore 2 X ≃* X.map φ ⧸ pPrimeCore 2 (X.map φ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv φ X
    (not_two_dvd_card_ker_domRestrict φ hφ X)
  exact ⟨e⟩

omit [Finite H'] in
theorem exists_sylow_map (φ : H →* H') {R Y : Subgroup H} (hRY : R ≤ Y)
    (hR : ∃ R' : Sylow 2 ↥Y, (R' : Subgroup _) = R.subgroupOf Y) :
    ∃ R' : Sylow 2 ↥(Y.map φ), (R' : Subgroup _) = (R.map φ).subgroupOf (Y.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R', hR'⟩ := hR
  refine ⟨R'.mapSurjective (φ.subgroupMap_surjective Y), ?_⟩
  rw [Sylow.coe_mapSurjective, hR', map_subgroupOf_subgroupMap φ hRY]

omit [Finite H] [Finite H'] in
theorem map_inf_centralizer (φ : H →* H') {E Y : Subgroup H} (hE : IsPGroup 2 E)
    (hEY : E ≤ normalizer (Y : Set H)) (hker : ¬ 2 ∣ Nat.card (φ.domRestrict Y).ker) :
    (Y ⊓ centralizer (E : Set H)).map φ =
      Y.map φ ⊓ centralizer ((E.map φ : Subgroup H') : Set H') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := SignalizerFunctor.Helpers.conjugationAction E Y hEY
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨y, hy.1, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨e, he, rfl⟩
    simpa only [map_mul] using congrArg φ (mem_centralizer_iff.mp hy.2 e he)
  · intro z hz
    obtain ⟨y, hyY, hyz⟩ := hz.1
    let r := φ.domRestrict Y
    let fibre : SubMulAction E Y :=
      ⟨{w | r w = z}, by
        intro e w hw
        change φ ((e : H) * w * (e : H)⁻¹) = z
        rw [map_mul, map_mul, map_inv]
        change φ e * r w * (φ e)⁻¹ = z
        rw [hw]
        have hc := mem_centralizer_iff.mp hz.2 (φ e) (mem_map_of_mem φ e.2)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]⟩
    have hfibre : Nat.card fibre = Nat.card r.ker := by
      have heq : {w : Y | r w = z} = r ⁻¹' {r (⟨y, hyY⟩ : Y)} := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change (r w = z) ↔ r w = φ y
        rw [hyz]
      exact (Nat.card_congr (Set.equivOfEq heq)).trans
        (Nat.card_congr (r.fiberEquivKer (⟨y, hyY⟩ : Y)))
    have hnd : ¬ 2 ∣ Nat.card fibre := by
      rw [hfibre]
      exact hker
    obtain ⟨w, hw⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card fibre hnd
    refine ⟨w.val.val, ⟨w.val.2, mem_centralizer_iff.mpr fun e he => ?_⟩, w.2⟩
    have h1 := congrArg (fun v : fibre => v.val.val) (hw (⟨e, he⟩ : E))
    change e * w.val.val * e⁻¹ = w.val.val at h1
    exact mul_inv_eq_iff_eq_mul.mp h1

omit [Finite H] [Finite H'] in
theorem map_conjClosure (φ : H →* H') (T Y : Subgroup H) :
    (conjClosure T Y).map φ = conjClosure (T.map φ) (Y.map φ) := by
  unfold conjClosure
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy => ?_
    rw [map_conjugate]
    exact le_iSup₂_of_le (φ y) (mem_map_of_mem φ hy) le_rfl
  · refine iSup₂_le fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hz
    refine le_iSup_of_le y ?_
    rw [Subgroup.map_iSup, ← map_conjugate]
    exact le_iSup_of_le hy le_rfl

end General

section Quotient

variable {H : Type*} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem odd_card_pPrimeCore : Odd (Nat.card (pPrimeCore 2 H)) :=
  Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem not_two_dvd_card_ker : ¬ 2 ∣ Nat.card (π).ker := by
  rw [QuotientGroup.ker_mk']
  exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card

theorem inf_pPrimeCore_eq_bot {R : Subgroup H} (hR : IsPGroup 2 R) :
    R ⊓ pPrimeCore 2 H = ⊥ :=
  eq_bot_of_le_two_group_of_le_odd hR odd_card_pPrimeCore inf_le_left inf_le_right

theorem injOn_of_isPGroup {R : Subgroup H} (hR : IsPGroup 2 R) : Set.InjOn π R := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ R ⊓ pPrimeCore 2 H := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hx) hy, ?_⟩
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H), MonoidHom.mem_ker, map_mul, map_inv, hxy,
      inv_mul_cancel]
  rw [inf_pPrimeCore_eq_bot hR, mem_bot] at h1
  exact (inv_mul_eq_one.mp h1)

theorem le_of_map_le {R E₁ E₂ : Subgroup H} (hR : IsPGroup 2 R) (h1 : E₁ ≤ R) (h2 : E₂ ≤ R)
    (h : E₁.map π ≤ E₂.map π) : E₁ ≤ E₂ := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := mem_map.mp (h (mem_map_of_mem π hx))
  rwa [injOn_of_isPGroup hR (h2 hy) (h1 hx) hyx] at hy

theorem map_inf_of_le {R E₁ E₂ : Subgroup H} (hR : IsPGroup 2 R) (h1 : E₁ ≤ R) (h2 : E₂ ≤ R) :
    (E₁ ⊓ E₂).map π = E₁.map π ⊓ E₂.map π := by
  refine le_antisymm (le_inf (map_mono inf_le_left) (map_mono inf_le_right)) ?_
  rintro z ⟨hz1, hz2⟩
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hz1
  obtain ⟨y, hy, hyx⟩ := mem_map.mp hz2
  rw [injOn_of_isPGroup hR (h2 hy) (h1 hx) hyx] at hy
  exact mem_map_of_mem π (mem_inf.mpr ⟨hx, hy⟩)

theorem card_map_of_isPGroup {E : Subgroup H} (hE : IsPGroup 2 E) :
    Nat.card (E.map π) = Nat.card E := by
  have hinj : Function.Injective ((π).subgroupMap E) := by
    intro x y hxy
    exact Subtype.ext (injOn_of_isPGroup hE x.2 y.2 (congrArg Subtype.val hxy))
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, (π).subgroupMap_surjective E⟩)).symm

omit [Finite H] in
theorem map_inf_comap_eq {R : Subgroup H} {E : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hE : E ≤ R.map π) : (R ⊓ E.comap π).map π = E := by
  refine le_antisymm ?_ fun z hz => ?_
  · rw [map_le_iff_le_comap]
    exact inf_le_right
  · obtain ⟨x, hx, rfl⟩ := mem_map.mp (hE hz)
    exact mem_map_of_mem π (mem_inf.mpr ⟨hx, hz⟩)

theorem inf_pPrimeCore_le_oddCoreIn (X : Subgroup H) : X ⊓ pPrimeCore 2 H ≤ oddCoreIn X := by
  have hn : ((pPrimeCore 2 H).subgroupOf X).Normal := inferInstance
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 H).subgroupOf X)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ (pPrimeCore_coprime_card (p := 2) (G := H))
    rw [show Nat.card ((pPrimeCore 2 H).subgroupOf X) = Nat.card ↥(pPrimeCore 2 H ⊓ X) by
      rw [← inf_subgroupOf_right]
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : (pPrimeCore 2 H).subgroupOf X ≤ pPrimeCore 2 X := le_sSup ⟨hn, hcop⟩
  have h1 := map_mono (f := X.subtype) hle
  rw [subgroupOf_map_subtype] at h1
  rw [inf_comm]
  exact h1

theorem normalizer_map_eq {E : Subgroup H} (hE : IsPGroup 2 E) :
    normalizer ((E.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) =
      (normalizer (E : Set H)).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 E) := ⟨hE⟩
  exact normalizer_map_quotient_eq_map_normalizer 2 E (pPrimeCore 2 H) inferInstance
    pPrimeCore_coprime_card

theorem centralizer_map_eq {E : Subgroup H} (hE : IsPGroup 2 E) :
    centralizer ((E.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) =
      (centralizer (E : Set H)).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 E) := ⟨hE⟩
  exact centralizer_map_quotient_eq_map_centralizer 2 E (pPrimeCore 2 H) inferInstance
    pPrimeCore_coprime_card

theorem centralizer_singleton_map_eq {t : H} (ht : t * t = 1) :
    centralizer ({π t} : Set (H ⧸ pPrimeCore 2 H)) = (centralizer ({t} : Set H)).map π :=
  (map_centralizer_eq odd_card_pPrimeCore ht).symm

theorem map_inf_coreActionKernel {X Y : Subgroup H} (hYX : Y ≤ normalizer (X : Set H)) :
    (Y ⊓ coreActionKernel X).map π = Y.map π ⊓ coreActionKernel (X.map π) := by
  have hO := map_oddCoreIn π not_two_dvd_card_ker X
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgY, hgC⟩ := mem_inf.mp hg
    obtain ⟨hgN, hgJ⟩ := mem_coreActionKernel.mp hgC
    refine mem_inf.mpr ⟨mem_map_of_mem π hgY, mem_coreActionKernel.mpr
      ⟨le_normalizer_map π (mem_map_of_mem π hgN), fun j hj => ?_⟩⟩
    obtain ⟨j', hj', rfl⟩ := mem_map.mp hj
    have h1 := mem_map_of_mem π (hgJ j' hj')
    simp only [map_mul, map_inv] at h1
    change π j'⁻¹ * (π g)⁻¹ * π j' * π g ∈ oddCoreIn (X.map π)
    rw [← hO, map_inv]
    exact h1
  · rintro _ ⟨⟨g, hgY, rfl⟩, hgC⟩
    refine mem_map_of_mem π (mem_inf.mpr ⟨hgY, mem_coreActionKernel.mpr ⟨hYX hgY, ?_⟩⟩)
    intro j hj
    have hgN := hYX hgY
    have hc : j⁻¹ * g⁻¹ * j * g ∈ X := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hgN) j).mp hj
      rw [inv_inv] at h1
      rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
      exact mul_mem (inv_mem hj) h1
    have h1 : π j⁻¹ * (π g)⁻¹ * π j * π g ∈ oddCoreIn (X.map π) := by
      rw [map_inv]
      exact (mem_coreActionKernel.mp hgC).2 (π j) (mem_map_of_mem π hj)
    rw [← hO] at h1
    obtain ⟨o, ho, hoc⟩ := mem_map.mp (show π (j⁻¹ * g⁻¹ * j * g) ∈ (oddCoreIn X).map π by
      simpa only [map_mul, map_inv] using h1)
    have hoX : o ∈ X := map_subtype_le _ ho
    have hk : o⁻¹ * (j⁻¹ * g⁻¹ * j * g) ∈ X ⊓ pPrimeCore 2 H := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hoX) hc, ?_⟩
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H), MonoidHom.mem_ker, map_mul, map_inv, hoc,
        inv_mul_cancel]
    have h2 := mul_mem ho (inf_pPrimeCore_le_oddCoreIn X hk)
    rwa [mul_inv_cancel_left] at h2

theorem map_fixedLayer {J E : Subgroup H} (hE : IsPGroup 2 E)
    (hEJ : E ≤ normalizer (J : Set H)) :
    (GSLit.fixedLayer J E).map π = GSLit.fixedLayer (J.map π) (E.map π) := by
  have h1 := map_layerIn π not_two_dvd_card_ker (J ⊓ centralizer (E : Set H))
  rw [map_inf_centralizer π hE hEJ (not_two_dvd_card_ker_domRestrict π not_two_dvd_card_ker J)]
    at h1
  exact h1

end Quotient

end OddQuot

end CFSG.ComponentClassification.GSThmB
