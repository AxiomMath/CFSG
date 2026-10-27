module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPDiag
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagCover
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCorollaryC
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCClimb
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCRankGap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReach39
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankTwoMaximality
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem index_dvd_card_of_ker_le {A B : Type*} [Group A] [Group B] (f : A →* B)
    {N : Subgroup A} (h : f.ker ≤ N) : N.index ∣ Nat.card B :=
  calc N.index ∣ f.ker.index := index_dvd_of_le h
    _ = Nat.card f.range := index_ker f
    _ ∣ Nat.card B := card_subgroup_dvd_card f.range

omit [Finite G] in
private theorem card_dvd_index_of_surjective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) {N : Subgroup A} (h : N ≤ f.ker) : Nat.card B ∣ N.index :=
  calc Nat.card B = Nat.card f.range := by rw [f.range_eq_top_of_surjective hf, card_top]
    _ = f.ker.index := (index_ker f).symm
    _ ∣ N.index := index_dvd_of_le h

omit [Finite G] in
private theorem oddCoreIn_le (H : Subgroup G) : oddCoreIn H ≤ H := map_subtype_le _

omit [Finite G] in
private theorem le_normalizer_oddCoreIn (H : Subgroup G) :
    H ≤ normalizer (oddCoreIn H : Set G) := fun _ hh =>
  UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pPrimeCore 2 ↥H)
    (le_normalizer hh)

omit [Finite G] in
private theorem conj_mem_oddCoreIn {H : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ oddCoreIn H) : h * x * h⁻¹ ∈ oddCoreIn H :=
  (mem_normalizer_iff.mp (le_normalizer_oddCoreIn H hh) x).mp hx

omit [Finite G] in
private theorem normal_inf_subgroupOf {Y R : Subgroup G} (hYR : Y ≤ normalizer (R : Set G)) :
    ((Y ⊓ R).subgroupOf Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨hnY, hnR⟩ := mem_inf.mp hn
  rw [coe_mul, coe_mul, coe_inv]
  exact mem_inf.mpr ⟨mul_mem (mul_mem g.2 hnY) (inv_mem g.2),
    (mem_normalizer_iff.mp (hYR g.2) n).mp hnR⟩

omit [Finite G] in
private theorem le_normalizer_iSup {ι : Sort*} {X : Subgroup G} {f : ι → Subgroup G}
    (h : ∀ i, X ≤ normalizer (f i : Set G)) :
    X ≤ normalizer ((⨆ i, f i : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => mem_normalizer_iff_map_conj_eq.mp (h i hg)

omit [Finite G] in
private theorem isSolvable_of_le {A B : Subgroup G} (h : A ≤ B) (hB : Group.IsSolvable ↥B) :
    Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (inclusion_injective h)

omit [Finite G] in
private theorem isSolvable_of_commutator_le {Y X : Subgroup G} (hX : Group.IsSolvable ↥X)
    (h : ⁅Y, Y⁆ ≤ X) : Group.IsSolvable ↥Y := by
  have hle : ∀ x : ↥(_root_.commutator ↥Y), ((x : ↥Y) : G) ∈ X := fun x =>
    h (Y.map_subtype_commutator ▸ mem_map_of_mem Y.subtype x.2)
  let f : ↥(_root_.commutator ↥Y) →* ↥X :=
    (Y.subtype.comp (_root_.commutator ↥Y).subtype).codRestrict X hle
  have hf : Function.Injective f := fun a b hab => by
    have h1 := congrArg (fun x : ↥X => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have : Group.IsSolvable ↥(_root_.commutator ↥Y) := Group.isSolvable_of_isSolvable_injective hf
  exact Group.isSolvable_of_ker_le_range (_root_.commutator ↥Y).subtype Abelianization.of
    (by rw [Abelianization.ker_of, range_subtype])

private theorem not_isSolvable_of_quasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q

private def centO (H X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ oddCoreIn H}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun x hx => by
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_oddCoreIn ha.1 (hb.2 x hx)) (ha.2 x hx)⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun x hx => by
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_oddCoreIn (inv_mem ha.1) (inv_mem (ha.2 x hx))⟩

omit [Finite G] in
private theorem mem_centO {H X : Subgroup G} {g : G} :
    g ∈ centO H X ↔ g ∈ H ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ oddCoreIn H :=
  Iff.rfl

omit [Finite G] in
private theorem le_centO {H A X : Subgroup G} (hAH : A ≤ H) (h : ⁅A, X⁆ ≤ oddCoreIn H) :
    A ≤ centO H X := fun a ha => ⟨hAH ha, fun x hx => by
  have := h (commutator_mem_commutator ha hx)
  rwa [commutatorElement_def] at this⟩

omit [Finite G] in
private theorem commutator_le_of_le_centO {H A X : Subgroup G} (h : A ≤ centO H X) :
    ⁅A, X⁆ ≤ oddCoreIn H := by
  rw [commutator_le]
  intro a ha x hx
  rw [commutatorElement_def]
  exact (h ha).2 x hx

theorem isPerfect_of_isPComponent {H K : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) : Group.IsPerfect K := by
  have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hK
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKH).toMonoidHom)
    (subgroupOfEquivOfLe hKH).surjective

theorem isQuasisimple_of_isPComponent {H K : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
  ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K H hKH).mp hK).2.2

theorem not_isSolvable_of_isQuasisimple {Y : Subgroup G}
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) : ¬ Group.IsSolvable ↥Y := fun hs =>
  not_isSolvable_of_quasisimple hYq inferInstance

theorem isSolvable_of_le_oddCoreIn {H Y : Subgroup G} (hY : Y ≤ oddCoreIn H) :
    Group.IsSolvable ↥Y :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Odd.of_dvd_nat (UnbalancedGS.odd_card_map_pPrimeCore_two H)
    (card_dvd_of_le hY))

theorem isSolvable_fusionZStar (Y : Type) [Group Y] [Finite Y] :
    Group.IsSolvable ↥(Open.fusionZStar Y) := by
  rw [Sol78.fusionZStar_eq_comap]
  set π := QuotientGroup.mk' (pPrimeCore 2 Y)
  set Z := center (Y ⧸ pPrimeCore 2 Y)
  have hle : pPrimeCore 2 Y ≤ Z.comap π := by
    intro y hy
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
    exact one_mem _
  let g : ↥(Z.comap π) →* ↥Z := (π.comp (Z.comap π).subtype).codRestrict Z fun x => x.2
  have : Group.IsSolvable ↥(pPrimeCore 2 Y) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have : Group.IsSolvable ↥Z :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp b.2 a)
  refine Group.isSolvable_of_ker_le_range (inclusion hle) g fun x hx => ?_
  have hx' : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact ⟨⟨x, hx'⟩, rfl⟩

omit [Finite G] in
theorem le_layerIn_of_isPComponent {H K : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) : K ≤ layerIn H :=
  GSLit.le_map_pLayer_of_isPComponent hKH hK

theorem layerIn_le_normalizer {H K : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) : layerIn H ≤ normalizer (K : Set G) :=
  GrSLit.GrS5.layerIn_le_normalizer hKH hK

omit [Finite G] in
theorem layerIn_eq_iSup (H : Subgroup G) :
    layerIn H = ⨆ (N : Subgroup G) (_ : N ≤ H) (_ : IsPComponent 2 (N.subgroupOf H)), N := by
  refine le_antisymm ?_
    (iSup₂_le fun N hNH => iSup_le fun hN => le_layerIn_of_isPComponent hNH hN)
  rw [layerIn, pLayer, map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  have hLe : (L.map H.subtype).subgroupOf H = L :=
    comap_map_eq_self_of_injective H.subtype_injective L
  exact le_iSup₂_of_le (L.map H.subtype) (map_subtype_le L)
    (le_iSup_of_le (by rw [hLe]; exact hL) le_rfl)

theorem isPerfect_layerIn (H : Subgroup G) : Group.IsPerfect ↥(layerIn H) := by
  have h := LBalance.pLayer_perfect 2 H
  rwa [LBalance.Asm.lBalancePLayer_eq_map] at h

theorem isPComponent_layerIn_of_isSimpleGroup {C : Subgroup G}
    (hs : IsSimpleGroup (↥(layerIn C) ⧸ pPrimeCore 2 ↥(layerIn C))) :
    IsPComponent 2 ((layerIn C).subgroupOf C) := by
  have hL : (layerIn C).subgroupOf C = pLayer ↥C 2 :=
    comap_map_eq_self_of_injective C.subtype_injective _
  rw [hL]
  apply Seven.isPComponent_pLayer_of_isSimpleGroup
  let e : ↥(pLayer ↥C 2) ≃* ↥(layerIn C) :=
    (pLayer ↥C 2).equivMapOfInjective C.subtype C.subtype_injective
  exact (Sol78.coreQuotCongr e).isSimpleGroup

theorem isPComponent_conjugate {H M : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G))
    (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H)) :
    conjugate M g ≤ H ∧ IsPComponent 2 ((conjugate M g).subgroupOf H) := by
  set N := normalizer (H : Set G)
  have hHN : H ≤ N := le_normalizer
  have hHn : (H.subgroupOf N).IsSubnormal :=
    ((normal_subgroupOf_iff_le_normalizer hHN).mpr le_rfl).isSubnormal
  have hM' : IsPComponent 2 (M.subgroupOf N) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hMH hHN hHn).mpr hM
  have h1 := UnbalancedLayer.isPComponent_conjugate hM' (⟨g, hg⟩ : N)
  rw [conjugate_subgroupOf_eq] at h1
  have hle : conjugate M g ≤ H := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have h2 := (mem_normalizer_iff.mp (inv_mem hg) _).mp (hMH hy)
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h2
  exact ⟨hle, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hle hHN hHn).mp h1⟩

theorem isPComponent_of_le_of_subnormal {U V K : Subgroup G} (hKU : K ≤ U) (hUV : U ≤ V)
    (hU : (U.subgroupOf V).IsSubnormal) (hK : IsPComponent 2 (K.subgroupOf U)) :
    IsPComponent 2 (K.subgroupOf V) :=
  (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hKU hUV hU).mpr hK

theorem isPComponent_of_le_of_le {U V K : Subgroup G} (hKU : K ≤ U) (hUV : U ≤ V)
    (hK : IsPComponent 2 (K.subgroupOf V)) : IsPComponent 2 (K.subgroupOf U) :=
  CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKU hUV hK

theorem commutator_le_oddCoreIn_of_ne {H J N : Subgroup G} (hJH : J ≤ H) (hNH : N ≤ H)
    (hJ : IsPComponent 2 (J.subgroupOf H)) (hN : IsPComponent 2 (N.subgroupOf H))
    (hne : J ≠ N) : ⁅J, N⁆ ≤ oddCoreIn H :=
  CorC.commutator_le_oddIn_of_ne hJH hNH hJ hN hne

theorem eq_of_le_of_le_of_not_isSolvable {H M M' Y : Subgroup G} (hMH : M ≤ H) (hM'H : M' ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) (hM' : IsPComponent 2 (M'.subgroupOf H))
    (hYM : Y ≤ M) (hYM' : Y ≤ M') (hY : ¬ Group.IsSolvable ↥Y) : M = M' := by
  by_contra hne
  apply hY
  have h1 := GrSLit.GrS5.commutator_le_inf_oddIn hMH hM'H hM hM' hne
  have h2 : ⁅Y, Y⁆ ≤ oddCoreIn M := (commutator_mono hYM hYM').trans (h1.trans inf_le_left)
  exact isSolvable_of_commutator_le (isSolvable_of_le_oddCoreIn le_rfl) h2

omit [Finite G] in
theorem commutator_sup_le_oddCoreIn {H K A B : Subgroup G} (hKH : K ≤ H) (hAH : A ≤ H)
    (hBH : B ≤ H) (hA : ⁅K, A⁆ ≤ oddCoreIn H) (hB : ⁅K, B⁆ ≤ oddCoreIn H) :
    ⁅K, A ⊔ B⁆ ≤ oddCoreIn H := by
  rw [commutator_comm] at hA hB ⊢
  exact commutator_le_of_le_centO (sup_le (le_centO hAH hA) (le_centO hBH hB))

theorem le_of_not_isSolvable_inf {Y R : Subgroup G} (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) (hYR : Y ≤ normalizer (R : Set G))
    (hR : ¬ Group.IsSolvable ↥(Y ⊓ R)) : Y ≤ R := by
  set N : Subgroup ↥Y := (Y ⊓ R).subgroupOf Y
  have hN : N.Normal := normal_inf_subgroupOf hYR
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Y)
  have hNπ : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases LocalCores.quasisimple_normal_subgroups hYq hNπ with htop | hcen
  · have hle : (⊤ : Subgroup ↥Y) ≤ N ⊔ pPrimeCore 2 ↥Y := by
      have h := comap_map_eq π N
      rw [htop, comap_top, QuotientGroup.ker_mk'] at h
      exact h.le
    have hsol : Group.IsSolvable ↥(pPrimeCore 2 ↥Y) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    have h := RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hN.isSubnormal
      (Group.IsPerfect.top_iff.mpr hYp) hle
    intro y hy
    exact (mem_inf.mp (mem_subgroupOf.mp (h (mem_top ⟨y, hy⟩)))).2
  · exfalso
    apply hR
    have hNZ : N ≤ Open.fusionZStar ↥Y := by
      rw [Sol78.fusionZStar_eq_comap]
      exact map_le_iff_le_comap.mp hcen
    have hNs : Group.IsSolvable ↥N := isSolvable_of_le hNZ (isSolvable_fusionZStar ↥Y)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (inf_le_left : Y ⊓ R ≤ Y)).symm.toMonoidHom)
      (subgroupOfEquivOfLe (inf_le_left : Y ⊓ R ≤ Y)).symm.injective

theorem inf_le_fusionZStar_of_isSolvable {Y R : Subgroup G}
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) (hYR : Y ≤ normalizer (R : Set G))
    (hR : Group.IsSolvable ↥(Y ⊓ R)) : Y ⊓ R ≤ (Open.fusionZStar ↥Y).map Y.subtype := by
  set N : Subgroup ↥Y := (Y ⊓ R).subgroupOf Y
  have hN : N.Normal := normal_inf_subgroupOf hYR
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Y)
  have hNπ : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have hNs : Group.IsSolvable ↥N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (inf_le_left : Y ⊓ R ≤ Y)).toMonoidHom)
    (subgroupOfEquivOfLe (inf_le_left : Y ⊓ R ≤ Y)).injective
  rcases LocalCores.quasisimple_normal_subgroups hYq hNπ with htop | hcen
  · exfalso
    have h1 : Group.IsSolvable ↥(N.map π) :=
      Group.isSolvable_of_surjective (π.subgroupMap_surjective N)
    rw [htop] at h1
    exact not_isSolvable_of_quasisimple hYq
      (Group.isSolvable_of_surjective (f := (topEquiv : ↥(⊤ : Subgroup (↥Y ⧸ pPrimeCore 2 ↥Y))
        ≃* _).toMonoidHom) topEquiv.surjective)
  · have hNZ : N ≤ Open.fusionZStar ↥Y := by
      rw [Sol78.fusionZStar_eq_comap]
      exact map_le_iff_le_comap.mp hcen
    intro x hx
    exact ⟨⟨x, (mem_inf.mp hx).1⟩, hNZ (mem_subgroupOf.mpr hx), rfl⟩

theorem card_quot_fusionZStar_le (Y : Type) [Group Y] [Finite Y] :
    Nat.card (Y ⧸ Open.fusionZStar Y) ≤ Nat.card (Y ⧸ pPrimeCore 2 Y) :=
  index_antitone (Sol78.pPrimeCore_le_fusionZStar Y)

theorem card_quot_fusionZStar_le_of_le {Y K : Subgroup G} (hYK : Y ≤ K) :
    Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) ≤ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by
  set f : ↥Y →* ↥K ⧸ pPrimeCore 2 ↥K := (QuotientGroup.mk' _).comp (inclusion hYK) with hf
  have hker : f.ker ≤ Open.fusionZStar ↥Y := by
    refine le_trans ?_ (Sol78.pPrimeCore_le_fusionZStar ↥Y)
    refine UnbalancedGS.le_pPrimeCore_two_of_normal_odd inferInstance ?_
    have h1 : f.ker = (pPrimeCore 2 ↥K).comap (inclusion hYK) := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (card_comap_dvd_of_injective _ _ (inclusion_injective hYK))
  exact Nat.le_of_dvd Nat.card_pos (index_dvd_card_of_ker_le f hker)

theorem card_quot_fusionZStar_eq_of_equiv {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) :
    Nat.card (A ⧸ Open.fusionZStar A) = Nat.card (B ⧸ Open.fusionZStar B) :=
  Nat.card_congr (Sol78.fusionZStarQuotOfCore e).toEquiv

theorem le_of_perfect_of_le_sup_solvable {A N W : Subgroup G} (hNA : N ≤ normalizer (A : Set G))
    (hN : Group.IsSolvable ↥N) (hWp : ⁅W, W⁆ = W) (hW : W ≤ A ⊔ N) : W ≤ A := by
  set H := A ⊔ N
  have hAH : A ≤ H := le_sup_left
  have hNH : N ≤ H := le_sup_right
  have hAn : (A.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).mpr (sup_le le_normalizer hNA)
  set π := QuotientGroup.mk' (A.subgroupOf H) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hNH)) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf H) q
    have hh : (h : G) ∈ ((A ⊔ N : Subgroup G) : Set G) := h.2
    rw [coe_mul_of_right_le_normalizer_left A N hNA] at hh
    obtain ⟨α, hα, n, hn, hαn⟩ := hh
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    have h1 : (((Subgroup.inclusion hNH ⟨n, hn⟩)⁻¹ * h : H) : G) = n⁻¹ * α * n⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv, Subgroup.coe_inclusion]
      rw [← hαn]
      group
    rw [h1]
    exact (mem_normalizer_iff.mp (inv_mem (hNA hn)) α).mp hα
  have hQs : Group.IsSolvable (↥H ⧸ A.subgroupOf H) := Group.isSolvable_of_surjective hsurj
  have hWH : W ≤ H := hW
  have hWperf : Group.IsPerfect ↥W := (Subgroup.isPerfect_iff (H := W)).mpr hWp
  have hWHp : Group.IsPerfect ↥(W.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hWH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hWH).symm.surjective
  have himp : Group.IsPerfect ↥((W.subgroupOf H).map π) :=
    Group.IsPerfect.ofSurjective (π.subgroupMap_surjective _)
  have hbot : (W.subgroupOf H).map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥((W.subgroupOf H).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hs : Group.IsSolvable ↥((W.subgroupOf H).map π) := inferInstance
    exact Group.IsPerfect.not_isSolvable _ hs
  intro w hw
  have h1 : π ⟨w, hWH hw⟩ = 1 := by
    have h2 : π ⟨w, hWH hw⟩ ∈ (W.subgroupOf H).map π := ⟨⟨w, hWH hw⟩, hw, rfl⟩
    rw [hbot] at h2
    exact h2
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

private theorem le_of_le_sup_oddCoreIn {H K W : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) (hWp : ⁅W, W⁆ = W) (hW : W ≤ K ⊔ oddCoreIn H) :
    W ≤ K :=
  le_of_perfect_of_le_sup_solvable (UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hKH hK)
    (isSolvable_of_le_oddCoreIn le_rfl) hWp hW

private theorem le_sup_others_or_dvd {H K₀ Y : Subgroup G} (hK₀H : K₀ ≤ H)
    (hK₀ : IsPComponent 2 (K₀.subgroupOf H)) (hYH : Y ≤ layerIn H) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) :
    Y ≤ (⨆ (N : Subgroup G) (_ : N ≤ H) (_ : IsPComponent 2 (N.subgroupOf H)) (_ : N ≠ K₀), N) ⊔
      oddCoreIn H ∨
    Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) ∣ Nat.card (↥K₀ ⧸ Open.fusionZStar ↥K₀) := by
  set S := ⨆ (N : Subgroup G) (_ : N ≤ H) (_ : IsPComponent 2 (N.subgroupOf H)) (_ : N ≠ K₀), N
  set O := oddCoreIn H
  set R := S ⊔ O
  set Z := (Open.fusionZStar ↥K₀).map K₀.subtype
  set R' := Z ⊔ R
  have hLK₀ : layerIn H ≤ normalizer (K₀ : Set G) := layerIn_le_normalizer hK₀H hK₀
  have hLS : layerIn H ≤ normalizer (S : Set G) :=
    le_normalizer_iSup fun N => le_normalizer_iSup fun hN => le_normalizer_iSup fun hNp =>
      le_normalizer_iSup fun _ => layerIn_le_normalizer hN hNp
  have hLO : layerIn H ≤ normalizer (O : Set G) :=
    (map_subtype_le _).trans (le_normalizer_oddCoreIn H)
  have hLZ : layerIn H ≤ normalizer (Z : Set G) := hLK₀.trans
    (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K₀ (Open.fusionZStar ↥K₀))
  have hLR : layerIn H ≤ normalizer (R : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_sup S O ⟨hLS hg, hLO hg⟩
  have hLR' : layerIn H ≤ normalizer (R' : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_sup Z R ⟨hLZ hg, hLR hg⟩
  have hK₀L : K₀ ≤ layerIn H := le_layerIn_of_isPComponent hK₀H hK₀
  have hZK₀ : Z ≤ K₀ := map_subtype_le _
  have hLKS : layerIn H ≤ K₀ ⊔ S := by
    rw [layerIn_eq_iSup]
    refine iSup₂_le fun N hN => iSup_le fun hNp => ?_
    by_cases hNK : N = K₀
    · exact hNK ▸ le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le N hN (le_iSup₂_of_le hNp hNK le_rfl))
  by_cases hsol : Group.IsSolvable ↥(Y ⊓ R')
  ·
    right
    have hYZ : Y ⊓ R' ≤ (Open.fusionZStar ↥Y).map Y.subtype :=
      inf_le_fusionZStar_of_isSolvable hYq (hYH.trans hLR') hsol
    set T := K₀ ⊔ R'
    have hR'T : R' ≤ T := le_sup_right
    have hK₀T : K₀ ≤ T := le_sup_left
    have hYT : Y ≤ T :=
      hYH.trans (hLKS.trans (sup_le_sup_left (le_sup_left.trans le_sup_right) K₀))
    have hR'n : (R'.subgroupOf T).Normal :=
      (normal_subgroupOf_iff_le_normalizer hR'T).mpr (sup_le (hK₀L.trans hLR') le_normalizer)
    have hφ :
        Function.Surjective ((QuotientGroup.mk' (R'.subgroupOf T)).comp (inclusion hK₀T)) := by
      intro q
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
      have ht : (t : G) ∈ ((K₀ ⊔ R' : Subgroup G) : Set G) := t.2
      rw [coe_mul_of_left_le_normalizer_right K₀ R' (hK₀L.trans hLR')] at ht
      obtain ⟨k, hk, r, hr, hkr⟩ := ht
      refine ⟨⟨k, hk⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_subgroupOf]
      have h1 : (((inclusion hK₀T ⟨k, hk⟩)⁻¹ * t : T) : G) = r := by
        simp only [coe_mul, coe_inv, coe_inclusion]
        rw [← hkr]
        group
      rw [h1]
      exact hr
    have hZφ : Open.fusionZStar ↥K₀ ≤
        ((QuotientGroup.mk' (R'.subgroupOf T)).comp (inclusion hK₀T)).ker := by
      intro z hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact (le_sup_left : Z ≤ R') (mem_map_of_mem K₀.subtype hz)
    have hχ : ((QuotientGroup.mk' (R'.subgroupOf T)).comp (inclusion hYT)).ker ≤
        Open.fusionZStar ↥Y := by
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf] at hy
      obtain ⟨y', hy', hyy'⟩ := hYZ (mem_inf.mpr ⟨y.2, hy⟩)
      have h1 : y' = y := Subtype.ext hyy'
      rw [← h1]
      exact hy'
    exact (index_dvd_card_of_ker_le _ hχ).trans (card_dvd_index_of_surjective hφ hZφ)
  · left
    have hYR' : Y ≤ R' := le_of_not_isSolvable_inf hYp hYq (hYH.trans hLR') hsol
    have : Group.IsSolvable ↥(Open.fusionZStar ↥K₀) := isSolvable_fusionZStar ↥K₀
    have hZs : Group.IsSolvable ↥Z :=
      Group.isSolvable_of_surjective (K₀.subtype.subgroupMap_surjective _)
    exact le_of_perfect_of_le_sup_solvable ((hZK₀.trans hK₀L).trans hLR) hZs
      (isPerfect_iff.mp hYp) (by rw [sup_comm]; exact hYR')

private theorem commutator_le_of_le_sup_others {H K₀ Y : Subgroup G} (hK₀H : K₀ ≤ H)
    (hK₀ : IsPComponent 2 (K₀.subgroupOf H))
    (hY : Y ≤ (⨆ (N : Subgroup G) (_ : N ≤ H) (_ : IsPComponent 2 (N.subgroupOf H))
      (_ : N ≠ K₀), N) ⊔ oddCoreIn H) : ⁅Y, K₀⁆ ≤ oddCoreIn H := by
  refine commutator_le_of_le_centO (hY.trans (sup_le ?_ ?_))
  · exact iSup₂_le fun N hN => iSup₂_le fun hNp hne =>
      le_centO hN (commutator_le_oddCoreIn_of_ne hN hK₀H hNp hK₀ hne)
  · refine le_centO (oddCoreIn_le H) (commutator_le.mpr fun o ho k hk => ?_)
    rw [commutatorElement_def]
    have h1 := mul_mem ho (conj_mem_oddCoreIn (hK₀H hk) (inv_mem ho))
    rwa [show o * (k * o⁻¹ * k⁻¹) = o * k * o⁻¹ * k⁻¹ by group] at h1

theorem le_sup_others_of_card_lt_zStar {H K₀ Y : Subgroup G} (hK₀H : K₀ ≤ H)
    (hK₀ : IsPComponent 2 (K₀.subgroupOf H)) (hYH : Y ≤ layerIn H) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hcard : Nat.card (↥K₀ ⧸ Open.fusionZStar ↥K₀) < Nat.card (↥Y ⧸ Open.fusionZStar ↥Y)) :
    Y ≤ (⨆ (N : Subgroup G) (_ : N ≤ H) (_ : IsPComponent 2 (N.subgroupOf H)) (_ : N ≠ K₀), N) ⊔
      oddCoreIn H := by
  rcases le_sup_others_or_dvd hK₀H hK₀ hYH hYp hYq with h | h
  · exact h
  · exact absurd (Nat.le_of_dvd Nat.card_pos h) (not_le.mpr hcard)

theorem commutator_le_oddCoreIn_of_card_lt {H K₀ Y : Subgroup G} (hK₀H : K₀ ≤ H)
    (hK₀ : IsPComponent 2 (K₀.subgroupOf H)) (hYH : Y ≤ layerIn H) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hcard : Nat.card (↥K₀ ⧸ Open.fusionZStar ↥K₀) < Nat.card (↥Y ⧸ Open.fusionZStar ↥Y)) :
    ⁅Y, K₀⁆ ≤ oddCoreIn H :=
  commutator_le_of_le_sup_others hK₀H hK₀
    (le_sup_others_of_card_lt_zStar hK₀H hK₀ hYH hYp hYq hcard)

theorem card_quot_fusionZStar_dvd_of_not_commutator_le {H K₀ Y : Subgroup G} (hK₀H : K₀ ≤ H)
    (hK₀ : IsPComponent 2 (K₀.subgroupOf H)) (hYH : Y ≤ layerIn H) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) (hY : ¬ ⁅Y, K₀⁆ ≤ oddCoreIn H) :
    Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) ∣ Nat.card (↥K₀ ⧸ Open.fusionZStar ↥K₀) :=
  (le_sup_others_or_dvd hK₀H hK₀ hYH hYp hYq).resolve_left fun h =>
    hY (commutator_le_of_le_sup_others hK₀H hK₀ h)

theorem le_of_commutator_le_others {H K Y : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) (hYH : Y ≤ layerIn H) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hY : ∀ N : Subgroup G, N ≤ H → IsPComponent 2 (N.subgroupOf H) → N ≠ K →
      ⁅Y, N⁆ ≤ oddCoreIn H) : Y ≤ K := by
  set S := ⨆ (N : Subgroup G) (_ : N ≤ H) (_ : IsPComponent 2 (N.subgroupOf H)) (_ : N ≠ K), N
  set O := oddCoreIn H
  have hSH : S ≤ H := iSup₂_le fun N hN => iSup₂_le fun _ _ => hN
  have hSL : S ≤ layerIn H :=
    iSup₂_le fun N hN => iSup₂_le fun hNp _ => le_layerIn_of_isPComponent hN hNp
  have hSY : S ≤ centO H Y := iSup₂_le fun N hN => iSup₂_le fun hNp hne =>
    le_centO hN (by rw [commutator_comm]; exact hY N hN hNp hne)
  have hSK : S ≤ centO H K := iSup₂_le fun N hN => iSup₂_le fun hNp hne =>
    le_centO hN (commutator_le_oddCoreIn_of_ne hN hKH hNp hK hne)
  set Z' := S ⊓ centO H S
  have hZ'comm : ⁅Z', Z'⁆ ≤ O :=
    (commutator_mono le_rfl inf_le_left).trans (commutator_le_of_le_centO inf_le_right)
  have hZ's : Group.IsSolvable ↥Z' :=
    isSolvable_of_commutator_le (isSolvable_of_le_oddCoreIn le_rfl) hZ'comm
  have hZ'N : Z' ≤ normalizer ((K ⊔ O : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_sup K O
      ⟨layerIn_le_normalizer hKH hK (hSL (mem_inf.mp hg).1),
        le_normalizer_oddCoreIn H (hSH (mem_inf.mp hg).1)⟩
  have hLKS : layerIn H ≤ K ⊔ S := by
    rw [layerIn_eq_iSup]
    refine iSup₂_le fun N hN => iSup_le fun hNp => ?_
    by_cases hNK : N = K
    · exact hNK ▸ le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le N hN (le_iSup₂_of_le hNp hNK le_rfl))
  have hSnK : S ≤ normalizer (K : Set G) := hSL.trans (layerIn_le_normalizer hKH hK)
  have hYKZ : Y ≤ (K ⊔ O) ⊔ Z' := by
    intro y hy
    have hy' : y ∈ ((K ⊔ S : Subgroup G) : Set G) := hLKS (hYH hy)
    rw [coe_mul_of_right_le_normalizer_left K S hSnK] at hy'
    obtain ⟨k, hk, s, hs, rfl⟩ := hy'
    refine mul_mem (mem_sup_left (mem_sup_left hk))
      (mem_sup_right (mem_inf.mpr ⟨hs, mem_centO.mpr ⟨hSH hs, fun s' hs' => ?_⟩⟩))
    have h1 : s' * (k * s) * s'⁻¹ * (k * s)⁻¹ ∈ O := (hSY hs').2 (k * s) hy
    have h2 : s' * k * s'⁻¹ * k⁻¹ ∈ O := (hSK hs').2 k hk
    have h3 : k⁻¹ * ((s' * k * s'⁻¹ * k⁻¹)⁻¹ * (s' * (k * s) * s'⁻¹ * (k * s)⁻¹)) * k⁻¹⁻¹ ∈ O :=
      conj_mem_oddCoreIn (inv_mem (hKH hk)) (mul_mem (inv_mem h2) h1)
    have h4 := inv_mem h3
    rwa [show (k⁻¹ * ((s' * k * s'⁻¹ * k⁻¹)⁻¹ * (s' * (k * s) * s'⁻¹ * (k * s)⁻¹)) *
      k⁻¹⁻¹)⁻¹ = s * s' * s⁻¹ * s'⁻¹ by group] at h4
  have hYKO : Y ≤ K ⊔ O :=
    le_of_perfect_of_le_sup_solvable hZ'N hZ's (isPerfect_iff.mp hYp) hYKZ
  exact le_of_le_sup_oddCoreIn hKH hK (isPerfect_iff.mp hYp) hYKO

theorem exists_not_commutator_le {H Y : Subgroup G} (hYH : Y ≤ layerIn H)
    (hYp : Group.IsPerfect Y) (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) :
    ∃ K : Subgroup G, K ≤ H ∧ IsPComponent 2 (K.subgroupOf H) ∧ ¬ ⁅Y, K⁆ ≤ oddCoreIn H := by
  by_contra h
  push Not at h
  apply not_isSolvable_of_isQuasisimple hYq
  have hL : layerIn H ≤ centO H Y := by
    rw [layerIn_eq_iSup]
    exact iSup₂_le fun N hN => iSup_le fun hNp =>
      le_centO hN (by rw [commutator_comm]; exact h N hN hNp)
  exact isSolvable_of_commutator_le (isSolvable_of_le_oddCoreIn le_rfl)
    ((commutator_mono hYH le_rfl).trans (commutator_le_of_le_centO hL))

theorem le_of_le_layerIn_of_nonsolvable_quasisimple {H K Y Y' : Subgroup G} (hKH : K ≤ H)
    (hK : IsPComponent 2 (K.subgroupOf H)) (hYH : Y ≤ layerIn H) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) (hY'Y : Y' ≤ Y) (hY'K : Y' ≤ K)
    (hY' : ¬ Group.IsSolvable ↥Y') : Y ≤ K := by
  have hYN : Y ≤ normalizer ((K ⊔ oddCoreIn H : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_sup K (oddCoreIn H)
      ⟨layerIn_le_normalizer hKH hK (hYH hg), le_normalizer_oddCoreIn H (map_subtype_le _ (hYH hg))⟩
  have hns : ¬ Group.IsSolvable ↥(Y ⊓ (K ⊔ oddCoreIn H)) := fun hs =>
    hY' (isSolvable_of_le (le_inf hY'Y (hY'K.trans le_sup_left)) hs)
  exact le_of_le_sup_oddCoreIn hKH hK (isPerfect_iff.mp hYp)
    (le_of_not_isSolvable_inf hYp hYq hYN hns)

theorem layerIn_inf_centralizer_le {H A : Subgroup G} (hA : IsPGroup 2 A)
    (hAH : A ≤ normalizer (H : Set G)) :
    layerIn (H ⊓ centralizer (A : Set G)) ≤ layerIn H := by
  set X := H ⊔ A
  have hHX : H ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hXN : X ≤ normalizer (H : Set G) := sup_le le_normalizer hAH
  set D := X ⊓ centralizer (A : Set G) with hD
  have hXH : layerIn X ≤ layerIn H := by
    rw [layerIn_eq_iSup X]
    refine iSup₂_le fun L hLX => iSup_le fun hL => ?_
    have : Group.IsNilpotent ↥A := hA.isNilpotent
    have hAs : Group.IsSolvable ↥A := inferInstance
    have hLH : L ≤ H := le_of_perfect_of_le_sup_solvable hAH hAs
      (isPerfect_iff.mp (isPerfect_of_isPComponent hLX hL)) hLX
    exact le_layerIn_of_isPComponent hLH (isPComponent_of_le_of_le hLH hHX hL)
  refine le_trans ?_ hXH
  rw [layerIn_eq_iSup (H ⊓ centralizer (A : Set G))]
  refine iSup₂_le fun T hT => iSup_le fun hTp => ?_
  have hCD : H ⊓ centralizer (A : Set G) ≤ D := inf_le_inf_right _ hHX
  have hCn : ((H ⊓ centralizer (A : Set G)).subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCD).mpr fun d hd =>
      normalizer_inf_mem (hXN (mem_inf.mp hd).1) (le_normalizer (mem_inf.mp hd).2)
  have hTD : IsPComponent 2 (T.subgroupOf D) :=
    isPComponent_of_le_of_subnormal hT hCD hCn.isSubnormal hTp
  have hTD' : T ≤ D := hT.trans hCD
  have hbal := ClassicalInvolution.l2PrimeBalance ↥X (A.subgroupOf X) hA.comap_subtype
  have hcen : centralizer ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) = D.subgroupOf X := by
    rw [hD, inf_subgroupOf_left]
    ext x
    rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx a ha
      exact congrArg Subtype.val (hx ⟨a, hAX ha⟩ ha)
    · intro hx a ha
      exact Subtype.ext (hx a ha)
  rw [hcen] at hbal
  have hT1 : (T.subgroupOf X).subgroupOf (D.subgroupOf X) ≤ pLayer ↥(D.subgroupOf X) 2 :=
    le_sSup ((UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hTD)
  have hTXD : T.subgroupOf X ≤ D.subgroupOf X := fun x hx => hTD' hx
  have hT2 : T.subgroupOf X ≤ pLayer ↥X 2 := by
    refine le_trans ?_ hbal
    have h1 := map_mono (f := (D.subgroupOf X).subtype) hT1
    rwa [map_subgroupOf_eq_of_le hTXD] at h1
  have h1 := map_mono (f := X.subtype) hT2
  rwa [map_subgroupOf_eq_of_le (hTD'.trans inf_le_left)] at h1

theorem le_layerIn_of_isPComponent_inf_centralizer {H A T : Subgroup G} (hA : IsPGroup 2 A)
    (hAH : A ≤ normalizer (H : Set G)) (hTH : T ≤ H ⊓ centralizer (A : Set G))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (A : Set G)))) : T ≤ layerIn H :=
  (le_layerIn_of_isPComponent hTH hT).trans (layerIn_inf_centralizer_le hA hAH)

theorem isSylowIn_inf_of_subnormal {S C M : Subgroup G} (hS : Seven.IsSylowIn S C)
    (hMC : M ≤ C) (hM : (M.subgroupOf C).IsSubnormal) : Seven.IsSylowIn (S ⊓ M) M := by
  obtain ⟨hSC, R, hR⟩ := hS
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hM
  let e : ↥(M.subgroupOf C) ≃* ↥M := subgroupOfEquivOfLe hMC
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨inf_le_right, P.mapSurjective he, ?_⟩
  apply map_injective M.subtype_injective
  have hcomp : M.subtype.comp e.toMonoidHom = C.subtype.comp (M.subgroupOf C).subtype := by
    ext x
    rfl
  rw [subgroupOf_map_subtype, inf_of_le_left (inf_le_right : S ⊓ M ≤ M), Sylow.coe_mapSurjective,
    map_map, hcomp, ← map_map, hP, map_inf_eq _ _ C.subtype C.subtype_injective, hR,
    subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hSC, inf_of_le_left hMC]

theorem exists_normal_index_two {B F : Subgroup G} (hB : IsPGroup 2 B) (hFB : F ≤ B)
    (hFn : B ≤ normalizer (F : Set G)) (hne : F ≠ B) :
    ∃ F' : Subgroup G, F ≤ F' ∧ F' ≤ B ∧ B ≤ normalizer (F' : Set G) ∧
      Nat.card F' = 2 * Nat.card F := by
  set N := F.subgroupOf B with hN
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hFB).mpr hFn
  have hQ : IsPGroup 2 (↥B ⧸ N) := hB.to_quotient N
  have hQnt : Nontrivial (↥B ⧸ N) := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    exact hne (le_antisymm hFB (subgroupOf_eq_top.mp h))
  have hZ : Nontrivial (center (↥B ⧸ N)) := hQ.center_nontrivial
  have h2 : 2 ∣ Nat.card (center (↥B ⧸ N)) := by
    rcases (hQ.to_subgroup (center (↥B ⧸ N))).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set D := zpowers (z : ↥B ⧸ N) with hD
  have hDZ : D ≤ center (↥B ⧸ N) := zpowers_le.mpr z.2
  have hDn : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hDZ hx) g, mul_inv_cancel_right]
    exact hx⟩
  set F₀ := D.comap (QuotientGroup.mk' N) with hF₀
  have hF₀n : F₀.Normal := hDn.comap _
  have hNF₀ : N ≤ F₀ := by
    intro x hx
    rw [hF₀, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  refine ⟨F₀.map B.subtype, ?_, map_subtype_le _, ?_, ?_⟩
  · intro f hf
    exact ⟨⟨f, hFB hf⟩, hNF₀ hf, rfl⟩
  · intro b hb
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨⟨b, hb⟩ * y' * ⟨b, hb⟩⁻¹, hF₀n.conj_mem y' hy' ⟨b, hb⟩, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      refine ⟨⟨b, hb⟩⁻¹ * y' * ⟨b, hb⟩⁻¹⁻¹, hF₀n.conj_mem y' hy' _, ?_⟩
      have hyy'' : (y' : G) = b * y * b⁻¹ := hyy'
      simp only [coe_subtype, coe_mul, coe_inv, inv_inv, hyy'']
      group
  ·
    have hmap : F₀.map (QuotientGroup.mk' N) = D :=
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) D
    have hrel : N.relIndex F₀ = 2 := by
      have h1 := relIndex_ker (K := F₀) (QuotientGroup.mk' N)
      rw [QuotientGroup.ker_mk', hmap, hD, Nat.card_zpowers, Subgroup.orderOf_coe, hz] at h1
      exact h1
    have hcard := relIndex_mul_card (H := N) (K := F₀)
    rw [hrel, inf_of_le_left hNF₀] at hcard
    rw [card_map_of_injective B.subtype_injective, ← hcard, hN,
      Nat.card_congr (subgroupOfEquivOfLe hFB).toEquiv]

end CFSG.ComponentClassification.GSThmB.A10T
