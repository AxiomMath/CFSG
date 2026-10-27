module

public import CFSG.GroupTheory.Fitting.GeneralizedFittingOvergroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleRank
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedCommutingKernel
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedInheritance
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndX
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACentral
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedHulls

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreIn_le_base (X : Subgroup G) : FooteLit.oddCoreIn X ≤ base X := by
  dsimp [base]
  refine le_sup_of_le_left ?_
  change (pPrimeCore 2 ↥X).map X.subtype ≤
    (((pCore 2 (↥X ⧸ pPrimeCore 2 ↥X)).comap
      (QuotientGroup.mk' (pPrimeCore 2 ↥X))).map X.subtype)
  exact Subgroup.map_mono CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p

theorem oddCoreIn_inf_eq (H X : Subgroup G) (hbase : base X ≤ H) :
    FooteLit.oddCoreIn (H ⊓ X) = FooteLit.oddCoreIn X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Xbar := ↥X ⧸ pPrimeCore 2 ↥X
  let π : ↥X →* Xbar := QuotientGroup.mk' (pPrimeCore 2 ↥X)
  have hOH : pPrimeCore 2 ↥X ≤ (H ⊓ X).subgroupOf X := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hbase (oddCoreIn_le_base X ⟨z, hz, rfl⟩), z.2⟩
  have hObar : pPrimeCore 2 Xbar = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (p := 2) Nat.prime_two
  have hbaseF : pCore 2 Xbar ⊔ layer Xbar = generalizedFitting Xbar := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Xbar 2 hObar]
  have hmapBase : ((base X).subgroupOf X).map π = generalizedFitting Xbar := by
    rw [← hbaseF]
    have h := CFSG.ComponentClassification.Sol76T13.R12.map_oddTwoCoreIn_sup_twoLayerIn
      (G := G) X
    simpa [base, π, Xbar] using h
  have hbaseLe : (base X).subgroupOf X ≤ (H ⊓ X).subgroupOf X := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact ⟨hbase hz, z.2⟩
  have hF : generalizedFitting Xbar ≤ ((H ⊓ X).subgroupOf X).map π := by
    rw [← hmapBase]
    exact Subgroup.map_mono hbaseLe
  have hcore := CFSG.map_pPrimeCore_eq_of_quotient (X := ↥X) (p := 2)
    (H := (H ⊓ X).subgroupOf X) hOH hF
  have hmap := congrArg (Subgroup.map X.subtype) hcore
  rw [CFSG.pPrimeCore_map_subgroupOf 2 (H ⊓ X) X inf_le_right] at hmap
  simpa only [FooteLit.oddCoreIn] using hmap

theorem inf_oddCoreIn_le_oddCoreIn (H X : Subgroup G) (hbase : base X ≤ H) :
    FooteLit.oddCoreIn H ⊓ X ≤ FooteLit.oddCoreIn X := by
  have hOle : FooteLit.oddCoreIn H ≤ H :=
    (oddCoreIn_le_base H).trans (base_le H)
  have hEq := oddCoreIn_inf_eq H X hbase
  have h : (H ⊓ X) ⊓ FooteLit.oddCoreIn H ≤ FooteLit.oddCoreIn (H ⊓ X) :=
    CFSG.ComponentClassification.GSThmB.B5a.inf_oddCoreIn_le_of_le
      (X := H ⊓ X) (Y := H) inf_le_left
  have hleft : (H ⊓ X) ⊓ FooteLit.oddCoreIn H = FooteLit.oddCoreIn H ⊓ X := by
    rw [inf_assoc, inf_comm X (FooteLit.oddCoreIn H), ← inf_assoc,
      inf_eq_right.mpr hOle]
  rw [hEq, hleft] at h
  exact h

theorem inf_oddCoreIn_le_oddCoreIn_centralizer (H : Subgroup G) (t : G)
    (hbase : base (Subgroup.centralizer ({t} : Set G)) ≤ H) :
    FooteLit.oddCoreIn H ⊓ Subgroup.centralizer ({t} : Set G) ≤
      FooteLit.oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
  inf_oddCoreIn_le_oddCoreIn H (Subgroup.centralizer ({t} : Set G)) hbase

open Subgroup CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.Sol76.Sig
open scoped commutatorElement Pointwise

theorem theta_eq_oddCoreIn_inf_centralizer {H E F : Subgroup G}
    (hF2 : IsPGroup 2 F) (hFH : F ≤ H)
    (hEF : E ≤ centralizer (F : Set G))
    (hfixE : ∀ e ∈ E, e ≠ 1 →
      oddCoreIn H ⊓ centralizer ({e} : Set G) ≤
        oddCoreIn (centralizer ({e} : Set G)))
    (hfixF : oddCoreIn H ⊓ centralizer (F : Set G) ≤
      oddCoreIn (centralizer (F : Set G)))
    (htheta : ∀ e ∈ E, e ≠ 1 → theta F e ≤ oddCoreIn H) :
    ∀ e ∈ E, e ≠ 1 → theta F e = oddCoreIn H ⊓ centralizer ({e} : Set G) := by
  intro e he he1
  have hF_Ce : F ≤ centralizer ({e} : Set G) := by
    intro f hf
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp (hEF he) f hf
  have htheta_le_centralizer : theta F e ≤ centralizer ({e} : Set G) :=
    (theta_le_oddCoreIn hF_Ce).trans (Subgroup.map_subtype_le _)
  refine le_antisymm (le_inf (htheta e he he1) htheta_le_centralizer) ?_
  set R : Subgroup G := oddCoreIn H with hR
  set X : Subgroup G := R ⊓ centralizer ({e} : Set G) with hX
  have hXR : X ≤ R := hX.le.trans inf_le_left
  have hXodd : Odd (Nat.card X) := by
    have hdvd : Nat.card X ∣ Nat.card R := Subgroup.card_dvd_of_le hXR
    exact Nat.coprime_two_left.mp
      (Nat.Coprime.coprime_dvd_right hdvd (Sol76.coprime_card_oddCoreIn H))
  have hFX : F ≤ Subgroup.normalizer (X : Set G) := by
    intro f hf
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (H := R) (K := centralizer ({e} : Set G))
      ⟨Sol76.le_normalizer_oddCoreIn H (hFH hf), Subgroup.le_normalizer (hF_Ce hf)⟩
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization
    2 Nat.prime_two F X hF2 hFX (Nat.coprime_two_left.mpr hXodd)
  have hcomm : ⁅X, F⁆ ≤ theta F e := by
    have hXO : X ≤ oddCoreIn (centralizer ({e} : Set G)) :=
      hX.le.trans (hfixE e he he1)
    exact (Subgroup.commutator_mono hXO le_rfl).trans le_sup_left
  have hfixed : X ⊓ centralizer (F : Set G) ≤ theta F e := by
    have hXO : X ≤ oddCoreIn (centralizer ({e} : Set G)) :=
      hX.le.trans (hfixE e he he1)
    have hXF : X ⊓ centralizer (F : Set G) ≤
        oddCoreIn (centralizer (F : Set G)) :=
      (inf_le_inf hXR le_rfl).trans hfixF
    exact (le_inf (inf_le_left.trans hXO) hXF).trans le_sup_right
  exact hfac.symm.le.trans (sup_le hcomm hfixed)

theorem oddCoreIn_eq_wGroup {H E F : Subgroup G}
    (hE : IsKleinFour E) (hEH : E ≤ H)
    (hF2 : IsPGroup 2 F) (hFH : F ≤ H)
    (hEF : E ≤ centralizer (F : Set G))
    (hfixE : ∀ e ∈ E, e ≠ 1 →
      oddCoreIn H ⊓ centralizer ({e} : Set G) ≤
        oddCoreIn (centralizer ({e} : Set G)))
    (hfixF : oddCoreIn H ⊓ centralizer (F : Set G) ≤
      oddCoreIn (centralizer (F : Set G)))
    (htheta : ∀ e ∈ E, e ≠ 1 → theta F e ≤ oddCoreIn H) :
    oddCoreIn H = wGroup E F := by
  have hpoint := theta_eq_oddCoreIn_inf_centralizer hF2 hFH hEF hfixE hfixF htheta
  refine le_antisymm ?_ ?_
  · have hER : E ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
      hEH.trans (Sol76.le_normalizer_oddCoreIn H)
    refine (le_iSup_inf_centralizer_of_isKleinFour hE hER
      (Sol76.coprime_card_oddCoreIn H)).trans ?_
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    exact (hpoint e he he1).ge.trans (theta_le_wGroup he he1)
  · refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    exact htheta e he he1

theorem oddCoreIn_inf_centralizer_le_of_involution {H F : Subgroup G} {v : G}
    (hvF : v ∈ F)
    (hfixv : oddCoreIn H ⊓ centralizer ({v} : Set G) ≤
      oddCoreIn (centralizer ({v} : Set G))) :
    oddCoreIn H ⊓ centralizer (F : Set G) ≤
      oddCoreIn (centralizer (F : Set G)) := by
  have hCF : centralizer (F : Set G) ≤ centralizer ({v} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hvF)
  have hXv : oddCoreIn H ⊓ centralizer (F : Set G) ≤
      oddCoreIn (centralizer ({v} : Set G)) :=
    (inf_le_inf le_rfl hCF).trans hfixv
  have hle : oddCoreIn H ⊓ centralizer (F : Set G) ≤
      centralizer (F : Set G) ⊓ oddCoreIn (centralizer ({v} : Set G)) :=
    le_inf inf_le_right hXv
  exact hle.trans
    (CFSG.ComponentClassification.GSThmB.B5a.inf_oddCoreIn_le_of_le hCF)

omit [Finite G] in
theorem le_oddCoreIn_normalizer_of_odd {W : Subgroup G} (hWodd : Odd (Nat.card W)) :
    W ≤ oddCoreIn (Subgroup.normalizer (W : Set G)) :=
  le_oddCoreIn Subgroup.le_normalizer le_rfl hWodd

theorem oddTwoCoreIn_le_of_actual_component {X H J A : Subgroup G}
    (hJ : IsTwoComponentIn J X) (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hOX : oddCoreIn X ≤ H)
    (hCXA : X ⊓ Subgroup.centralizer (A : Set G) ≤ H) :
    oddTwoCoreIn X ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥X := CFSG.pPrimeCore 2 ↥X
  let Xbar := ↥X ⧸ O
  let π : ↥X →* Xbar := QuotientGroup.mk' O
  let Jbar : Subgroup Xbar := (J.subgroupOf X).map π
  let Abar : Subgroup Xbar := (A.subgroupOf X).map π
  have hAX : A ≤ X := hAJ.trans hJ.1
  have hA2sub : IsPGroup 2 (A.subgroupOf X) :=
    IsPGroup.of_injective hA2 (Subgroup.subgroupOfEquivOfLe hAX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAX).injective
  have hJbar : IsComponent Jbar :=
    CFSG.ComponentClassification.Sol76T13.R12.isComponent_image hJ
  have hJbar_le_layer : Jbar ≤ CFSG.layer Xbar :=
    CFSG.LocalCores.component_le_layer hJbar
  have hAbar_le_Jbar : Abar ≤ Jbar := by
    dsimp only [Abar, Jbar, π]
    apply Subgroup.map_mono
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr (hAJ (Subgroup.mem_subgroupOf.mp ha))
  have hPcore_le_centA : CFSG.pCore 2 Xbar ≤
      Subgroup.centralizer (Abar : Set Xbar) := by
    have hcent_layer_J : Subgroup.centralizer (CFSG.layer Xbar : Set Xbar) ≤
        Subgroup.centralizer (Jbar : Set Xbar) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      exact hx y (hJbar_le_layer hy)
    have hcent_J_A : Subgroup.centralizer (Jbar : Set Xbar) ≤
        Subgroup.centralizer (Abar : Set Xbar) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      exact hx y (hAbar_le_Jbar hy)
    exact (CFSG.WholeGroup.pCore_le_centralizer_layer (G := Xbar) 2).trans
      (hcent_layer_J.trans hcent_J_A)
  have hodd : ¬ 2 ∣ Nat.card π.ker := by
    rw [show π.ker = O from QuotientGroup.ker_mk' _]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥X))
  have hmapC : (Subgroup.centralizer
        ((A.subgroupOf X : Subgroup ↥X) : Set ↥X)).map π =
      Subgroup.centralizer (Abar : Set Xbar) :=
    CFSG.ComponentClassification.GrSLit.map_centralizer_eq_of_odd_ker π
      (QuotientGroup.mk'_surjective _) hodd hA2sub
  have hPcore_le_mapC : CFSG.pCore 2 Xbar ≤
      (Subgroup.centralizer
        ((A.subgroupOf X : Subgroup ↥X) : Set ↥X)).map π := by
    rw [hmapC]
    exact hPcore_le_centA
  have hcomap : (CFSG.pCore 2 Xbar).comap π ≤
      Subgroup.centralizer
        ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) ⊔ O := by
    have h : (CFSG.pCore 2 Xbar).comap π ≤
        ((Subgroup.centralizer
          ((A.subgroupOf X : Subgroup ↥X) : Set ↥X)).map π).comap π :=
      Subgroup.comap_mono (f := π) hPcore_le_mapC
    rw [Subgroup.comap_map_eq (f := π)
      (H := Subgroup.centralizer
        ((A.subgroupOf X : Subgroup ↥X) : Set ↥X)), QuotientGroup.ker_mk'] at h
    exact h
  have hmapSup : ((Subgroup.centralizer
        ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) ⊔ O).map X.subtype) ≤ H := by
    rw [Subgroup.map_sup]
    apply sup_le
    · have hCXA' : (Subgroup.centralizer
          ((A.subgroupOf X : Subgroup ↥X) : Set ↥X)).map X.subtype ≤
          X ⊓ Subgroup.centralizer (A : Set G) :=
        le_inf (Subgroup.map_subtype_le _)
          (CFSG.Goldschmidt.G37.map_centralizer_subgroupOf_le hAX)
      exact hCXA'.trans hCXA
    · change oddCoreIn X ≤ H
      exact hOX
  change ((CFSG.pCore 2 Xbar).comap π).map X.subtype ≤ H
  exact (Subgroup.map_mono hcomap).trans hmapSup

open CFSG.ComponentClassification.UnbalancedLayer

theorem twoComponent_le_of_other_component_and_fixedCentralizer
    {X H J M A : Subgroup G} (hJ : IsTwoComponentIn J X)
    (hM : IsTwoComponentIn M X) (hMJ : M ≠ J)
    (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hOX : oddCoreIn X ≤ H) (hC : X ⊓ centralizer (A : Set G) ≤ H) : M ≤ H := by
  have hAK : A ≤ coreActionKernel M := hAJ.trans
    (GrSLit.Single.le_coreActionKernel_of_ne hM.1 hJ.1 hM.2 hJ.2 hMJ)
  have hAN : A ≤ normalizer (M : Set G) := fun a ha => (hAK ha).1
  have hact : ∀ a ∈ A, ∀ m ∈ M,
      a * m * a⁻¹ * m⁻¹ ∈ (pPrimeCore 2 M).map M.subtype := by
    intro a ha m hm
    have h := (hAK (A.inv_mem ha)).2 m⁻¹ (M.inv_mem hm)
    have hi := ((pPrimeCore 2 M).map M.subtype).inv_mem h
    simpa only [inv_inv, mul_inv_rev, mul_assoc] using hi
  have hlift := GrSLit.le_pLayer_inf_centralizer_sup hM.1 hM.2
    (hAJ.trans hJ.1) hA2 hAN hact
  refine hlift.trans (sup_le ?_ ?_)
  · exact (Subgroup.map_subtype_le _).trans
      ((inf_le_inf hM.1 le_rfl).trans hC)
  · exact (FooteLit.oddCoreIn_le_of_isTwoComponentIn hM).trans hOX

theorem twoLayerIn_le_of_component_and_fixedCentralizer
    {X H J A : Subgroup G} (hJ : IsTwoComponentIn J X) (hJH : J ≤ H)
    (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hOX : oddCoreIn X ≤ H) (hC : X ⊓ centralizer (A : Set G) ≤ H) :
    twoLayerIn X ≤ H := by
  apply Sol76T13.twoLayerIn_le_of_forall
  intro M hM
  by_cases hMJ : M = J
  · exact hMJ ▸ hJH
  · exact twoComponent_le_of_other_component_and_fixedCentralizer hJ hM hMJ hAJ hA2 hOX hC

theorem base_le_of_actual_component_and_fixedCentralizer
    {X H J A : Subgroup G} (hJ : IsTwoComponentIn J X) (hJH : J ≤ H)
    (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hOX : oddCoreIn X ≤ H) (hC : X ⊓ centralizer (A : Set G) ≤ H) : base X ≤ H :=
  sup_le (oddTwoCoreIn_le_of_actual_component hJ hAJ hA2 hOX hC)
    (twoLayerIn_le_of_component_and_fixedCentralizer hJ hJH hAJ hA2 hOX hC)

theorem coreRecovery_of_localBase {H E F : Subgroup G}
    (hE : IsKleinFour E) (hEH : E ≤ H) (hF2 : IsPGroup 2 F) (hFH : F ≤ H)
    (hEF : E ≤ centralizer (F : Set G))
    (hbaseE : ∀ e ∈ E, e ≠ 1 → base (centralizer ({e} : Set G)) ≤ H)
    {f : G} (hfF : f ∈ F) (hbaseF : base (centralizer ({f} : Set G)) ≤ H)
    (htheta : ∀ e ∈ E, e ≠ 1 → theta F e ≤ oddCoreIn H) :
    oddCoreIn H = wGroup E F ∧
      ∀ e ∈ E, e ≠ 1 → theta F e = oddCoreIn H ⊓ centralizer ({e} : Set G) := by
  have hfixE : ∀ e ∈ E, e ≠ 1 →
      oddCoreIn H ⊓ centralizer ({e} : Set G) ≤ oddCoreOfCentralizer e :=
    fun e he he1 => inf_oddCoreIn_le_oddCoreIn_centralizer H e (hbaseE e he he1)
  have hfixF := oddCoreIn_inf_centralizer_le_of_involution hfF
    (inf_oddCoreIn_le_oddCoreIn_centralizer H f hbaseF)
  exact ⟨oddCoreIn_eq_wGroup hE hEH hF2 hFH hEF hfixE hfixF htheta,
    theta_eq_oddCoreIn_inf_centralizer hF2 hFH hEF hfixE hfixF htheta⟩

theorem oddCoreIn_normalizer_eq_wGroup_of_originalW {W E F : Subgroup G}
    (hWodd : Odd (Nat.card W)) (hE : IsKleinFour E) (hF2 : IsPGroup 2 F)
    (hEH : E ≤ normalizer (W : Set G)) (hFH : F ≤ normalizer (W : Set G))
    (hEF : E ≤ centralizer (F : Set G)) (hWEF : W = wGroup E F)
    (hbaseE : ∀ e ∈ E, e ≠ 1 →
      base (centralizer ({e} : Set G)) ≤ normalizer (W : Set G))
    {f : G} (hfF : f ∈ F)
    (hbaseF : base (centralizer ({f} : Set G)) ≤ normalizer (W : Set G)) :
    oddCoreIn (normalizer (W : Set G)) = W ∧
      ∀ e ∈ E, e ≠ 1 → theta F e =
        oddCoreIn (normalizer (W : Set G)) ⊓ centralizer ({e} : Set G) := by
  have hWR := le_oddCoreIn_normalizer_of_odd hWodd
  have htheta : ∀ e ∈ E, e ≠ 1 → theta F e ≤ oddCoreIn (normalizer (W : Set G)) := by
    intro e he he1
    exact (theta_le_wGroup he he1).trans (hWEF.symm.le.trans hWR)
  obtain ⟨hcore, hpoint⟩ := coreRecovery_of_localBase hE hEH hF2 hFH hEF
    hbaseE hfF hbaseF htheta
  exact ⟨hcore.trans hWEF.symm, hpoint⟩

open scoped commutatorElement

omit [Finite G] in
private theorem core_quotient_map_eq_bot (H : Subgroup G) :
    ((oddCoreIn H).subgroupOf H).map (HbarMap H) = ⊥ := by
  have hOsub : (oddCoreIn H).subgroupOf H = pPrimeCore 2 ↥H := by
    ext x
    rw [Subgroup.mem_subgroupOf, oddCoreIn, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hOsub]
  exact (Subgroup.map_eq_bot_iff (H := pPrimeCore 2 ↥H)).mpr (by
    rw [HbarMap, QuotientGroup.ker_mk'])

theorem FixedShadowHull.image_eq_markedComponent
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {H Km V J : Subgroup G}
    (hKm : Km ∈ markedComponents S T H)
    (hJ : FixedShadowHull S T Km V J)
    (hJH : J ≤ H)
    (hcover : Km ≤ J ⊔ oddCoreIn H) :
    (J.subgroupOf H).map (HbarMap H) = (Km.subgroupOf H).map (HbarMap H) := by
  obtain ⟨-, ⟨eKm⟩, -⟩ := hKm.2
  obtain ⟨-, ⟨eJ⟩, -⟩ := hJ.marked
  have hEq : J ⊔ oddCoreIn H = Km ⊔ oddCoreIn H :=
    oddCoreImage_eq_of_contains_component (T := T) hKm.1 hJH hJ.marked.1 eKm eJ hcover
  have hOmap := core_quotient_map_eq_bot H
  have hmap := congrArg (fun X : Subgroup G => (X.subgroupOf H).map (HbarMap H)) hEq
  have hOH : oddCoreIn H ≤ H := Subgroup.map_subtype_le _
  simpa only [Subgroup.subgroupOf_sup hJH hOH,
    Subgroup.subgroupOf_sup hKm.1.1 hOH,
    Subgroup.map_sup, hOmap, sup_bot_eq] using hmap

theorem oddCoreIn_le_of_image_eq_markedComponent
    {S : Set (Subgroup G)} {T : Type*} [Group T] [IsSimpleGroup T]
    {H Km J : Subgroup G}
    (hKm : Km ∈ markedComponents S T H)
    (hJH : J ≤ H)
    (hJimage : (J.subgroupOf H).map (HbarMap H) =
      (Km.subgroupOf H).map (HbarMap H)) :
    oddCoreIn J ≤ oddCoreIn H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : ↥H →* Hbar H := HbarMap H
  let JH : Subgroup H := J.subgroupOf H
  let A : Subgroup (Hbar H) := (Km.subgroupOf H).map q
  have hA : IsComponent A := by
    dsimp [A]
    exact (markedComponent_image_simple_and_center
      (S := S) (T := T) (N := H) (K := Km) hKm).1
  have hAQ : CFSG.pPrimeCore 2 A = ⊥ := by
    have hsub := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (X := A) hA.2
    have hQ : CFSG.pPrimeCore 2 (Hbar H) = ⊥ :=
      CFSG.pPrimeCore_quotient_eq_bot (p := 2) Nat.prime_two
    rw [hQ] at hsub
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pPrimeCore 2 A) A.subtype_injective).mp
      (le_bot_iff.mp hsub)
  have hAeq : A = JH.map q := by
    simpa [A, JH, q] using hJimage.symm
  let g : JH →* A := (q.comp JH.subtype).codRestrict A (fun x => by
    rw [hAeq]
    exact Subgroup.mem_map_of_mem q x.2)
  have hg : Function.Surjective g := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ JH.map q := by
      rwa [← hAeq]
    rcases Subgroup.mem_map.mp ha' with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hmap := CFSG.map_pPrimeCore_le (p := 2) g hg
  have hmapbot : (CFSG.pPrimeCore 2 JH).map g = ⊥ := by
    rw [hAQ] at hmap
    exact le_bot_iff.mp hmap
  have hker : CFSG.pPrimeCore 2 JH ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxbot : g x ∈ (⊥ : Subgroup A) := by
      rw [← hmapbot]
      exact Subgroup.mem_map_of_mem g hx
    exact Subgroup.mem_bot.mp hxbot
  have hmapR : ((CFSG.pPrimeCore 2 JH).map JH.subtype).map H.subtype ≤ oddCoreIn H := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hgz1 : g z = 1 := by
      simpa [MonoidHom.mem_ker] using hker hz
    have hqz1 : q z.1 = 1 := congrArg Subtype.val hgz1
    have hzcore : z.1 ∈ CFSG.pPrimeCore 2 ↥H :=
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 ↥H) z.1).mp hqz1
    exact ⟨z.1, hzcore, rfl⟩
  have hoddJ : oddCoreIn J = ((CFSG.pPrimeCore 2 JH).map JH.subtype).map H.subtype := by
    dsimp [JH]
    change (CFSG.pPrimeCore 2 J).map J.subtype =
      ((CFSG.pPrimeCore 2 (J.subgroupOf H)).map (J.subgroupOf H).subtype).map H.subtype
    rw [CFSG.pPrimeCore_map_subgroupOf 2 J H hJH]
  rw [hoddJ]
  exact hmapR

omit [Finite G] in
private theorem image_centralizes_of_coreActionKernel
    {Y OV J Km H : Subgroup G}
    (_hYH : Y ≤ H) (hYOV : Y ≤ OV) (_hJH : J ≤ H)
    (hOV : OV ≤ UnbalancedLayer.coreActionKernel J)
    (hOJ : oddCoreIn J ≤ oddCoreIn H)
    (hJimage : (J.subgroupOf H).map (HbarMap H) =
      (Km.subgroupOf H).map (HbarMap H)) :
    (Y.subgroupOf H).map (HbarMap H) ≤
      Subgroup.centralizer ((Km.subgroupOf H).map (HbarMap H) : Set (Hbar H)) := by
  have hcommYJ : ⁅Y, J⁆ ≤ oddCoreIn J := by
    simpa only [commutator_comm] using
      CFSG.ComponentClassification.Sol76.Sig.commutator_le_oddCoreIn_of_le_coreActionKernel
        (hYOV.trans hOV)
  have hcomm : ⁅Y, J⁆ ≤ oddCoreIn H := hcommYJ.trans hOJ
  have hmapcomm : ⁅(Y.subgroupOf H).map (HbarMap H),
      (J.subgroupOf H).map (HbarMap H)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hb
    rw [Subgroup.mem_bot]
    have hmemG : ⁅(y : G), (j : G)⁆ ∈ oddCoreIn H :=
      hcomm (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hj))
    have hmemH : (⟨⁅(y : G), (j : G)⁆, Subgroup.map_subtype_le _ hmemG⟩ : ↥H) ∈
        (oddCoreIn H).subgroupOf H := hmemG
    have hzero : (HbarMap H) ⟨⁅(y : G), (j : G)⁆, Subgroup.map_subtype_le _ hmemG⟩ = 1 := by
      have hle : (oddCoreIn H).subgroupOf H ≤ (HbarMap H).ker :=
        (Subgroup.map_eq_bot_iff (H := (oddCoreIn H).subgroupOf H)).mp
          (core_quotient_map_eq_bot H)
      exact MonoidHom.mem_ker.mp (hle hmemH)
    have hsub : (⟨⁅(y : G), (j : G)⁆, Subgroup.map_subtype_le _ hmemG⟩ : ↥H) = ⁅y, j⁆ := by
      apply Subtype.ext
      exact (map_commutatorElement H.subtype y j).symm
    have hmap : (HbarMap H) ⁅y, j⁆ = 1 := by
      rwa [hsub] at hzero
    calc ⁅(HbarMap H) y, (HbarMap H) j⁆
        = (HbarMap H) ⁅y, j⁆ := (map_commutatorElement (HbarMap H) y j).symm
      _ = 1 := hmap
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmapcomm
  rwa [hJimage] at hcent

theorem theta_le_oddCoreIn_of_all_pure_containment
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {H Km Kn V : Subgroup G} {b : G}
    (hFam : IsomorphicFamily S T)
    (hKm : Km ∈ markedComponents S T H)
    (hKn : Kn ∈ markedComponents S T H)
    (hne : Km ≠ Kn)
    (hbKm : b ∈ Km) (hb2 : orderOf b = 2)
    [CFSG.IsElementaryAbelian 2 V]
    (hVne : V ≠ ⊥)
    (hVKn : V ≤ Kn)
    (_hVb : V ≤ Subgroup.centralizer ({b} : Set G))
    (hAllPure : ∀ K ∈ markedComponents S T H, ∀ t ∈ K, orderOf t = 2 →
      oddCoreIn (Subgroup.centralizer ({t} : Set G)) ≤ H ∧
      base (Subgroup.centralizer ({t} : Set G)) ≤ H)
    (hSchreier : ∀ v ∈ V, v ≠ 1 →
      CFSG.ComponentClassification.LBalance.SchreierSections
        ↥(Subgroup.centralizer ({v} : Set G))) :
    Sol76.Sig.theta V b ≤ oddCoreIn H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbH : b ∈ H := hKm.1.1 hbKm
  have hVH : V ≤ H := hVKn.trans hKn.1.1
  have hObH : oddCoreIn (Subgroup.centralizer ({b} : Set G)) ≤ H :=
    (hAllPure Km hKm b hbKm hb2).1
  have hV2 : IsPGroup 2 V := CFSG.IsElementaryAbelian.isPGroup 2 V
  have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
  obtain ⟨vV, hvZ, hv2V⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.exists_mem_center_orderOf_eq_two hV2
  let v : G := vV
  have hvV : v ∈ V := vV.2
  have hv2 : orderOf v = 2 := (Subgroup.orderOf_coe vV).trans hv2V
  have hv1 : v ≠ 1 := by
    intro hv
    have h1 : orderOf v = 1 := by rw [hv, orderOf_one]
    rw [hv2] at h1
    norm_num at h1
  have hVcentv : V ≤ Subgroup.centralizer ({v} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((mem_center_iff.mp hvZ) ⟨x, hx⟩))
  have hSchv : CFSG.ComponentClassification.LBalance.SchreierSections
      ↥(Subgroup.centralizer ({v} : Set G)) := hSchreier v hvV hv1
  have hbasev : base (Subgroup.centralizer ({v} : Set G)) ≤ H :=
    (hAllPure Kn hKn v (hVKn hvV) hv2).2
  have hST : MarkedST S T := markedST_of_isomorphicFamily (T := T) (family := S) hFam
  have hVK : V ≤ UnbalancedLayer.coreActionKernel Km :=
    hVKn.trans (GSThmB.B5a.le_coreActionKernel_of_ne hKm.1.1 hKn.1.1 hKm.1.2 hKn.1.2 hne)
  obtain ⟨J, hJHull⟩ := exists_fixedShadowHull hST hKm.2 hV2 hVK hVne
  have hcover : Km ≤ J ⊔ oddCoreIn H := by
    have hcov : Km = fixedShadow Km V ⊔ oddCoreIn Km :=
      (fixedShadow_sup_oddCoreIn_eq_of_cover
        (fixedShadow_cover_of_perfect hKm.2.1 hV2 hVK)).symm
    rw [hcov]
    exact sup_le (le_sup_of_le_left hJHull.fixedShadow_le)
      (le_sup_of_le_right (FooteLit.oddCoreIn_le_of_isTwoComponentIn hKm.1))
  have hJH : J ≤ H :=
    hJHull.le_of_base_le hvV hVcentv hV2 hSchv hbasev
  have hJimage : (J.subgroupOf H).map (HbarMap H) =
      (Km.subgroupOf H).map (HbarMap H) :=
    FixedShadowHull.image_eq_markedComponent hKm hJHull hJH hcover
  have hOJ : oddCoreIn J ≤ oddCoreIn H :=
    oddCoreIn_le_of_image_eq_markedComponent hKm hJH hJimage
  let q : ↥H →* Hbar H := HbarMap H
  let bH : H := ⟨b, hbH⟩
  have hbQ2 : orderOf (q bH) = 2 := by
    simpa [q, bH, HbarMap] using
      Sol78.F514.orderOf_mk_eq_two (by simpa [bH, Subgroup.orderOf_coe] using hb2)
  let A : Subgroup (Hbar H) := (Km.subgroupOf H).map q
  let B : Subgroup (Hbar H) := (Kn.subgroupOf H).map q
  have hA : IsComponent A := by
    dsimp [A]
    exact (markedComponent_image_simple_and_center
      (S := S) (T := T) (N := H) (K := Km) hKm).1
  have hB : IsComponent B := by
    dsimp [B]
    exact (markedComponent_image_simple_and_center
      (S := S) (T := T) (N := H) (K := Kn) hKn).1
  have hbA : q bH ∈ A := by
    dsimp [A]
    exact Subgroup.mem_map_of_mem q (by
      rw [Subgroup.mem_subgroupOf]
      simpa [bH] using hbKm)
  have hBneA : B ≠ A := by
    intro hBA
    apply hne
    apply Sol76T13.R12.eq_of_image_eq hKm.1 hKn.1
    simpa [A, B, q] using hBA.symm
  have hQO : CFSG.pPrimeCore 2 (Hbar H) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (p := 2) Nat.prime_two
  let Y : Subgroup (Hbar H) := ((oddCoreOfCentralizer b).subgroupOf H).map q
  let Cfull : Subgroup (Hbar H) := centralizer ({q bH} : Set (Hbar H))
  have hYfacts := image_oddCoreCentralizer_normal_in_full_quotient_centralizer H hbH hb2 hObH
  have hYleC : Y ≤ Cfull := hYfacts.1
  have hYodd : Odd (Nat.card Y) := hYfacts.2.1
  have hYnorm : (Y.subgroupOf Cfull).Normal := hYfacts.2.2.1
  have hYcentB : Y ≤ centralizer (B : Set (Hbar H)) :=
    odd_normal_centralizer_centralizes_other_components hA hbA hYleC hYnorm hYodd
      B hB hBneA
  have hVimgB : (V.subgroupOf H).map q ≤ B := by
    dsimp [B]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hVKn)
  have hcomm : ⁅oddCoreOfCentralizer b, V⁆ ≤ oddCoreIn H := by
    rw [Subgroup.commutator_le]
    intro x hx v hv
    have hxH : x ∈ H := hObH hx
    have hvH : v ∈ H := hVH hv
    let xH : H := ⟨x, hxH⟩
    let vH : H := ⟨v, hvH⟩
    have hxY : q xH ∈ Y := Subgroup.mem_map_of_mem q hx
    have hvB : q vH ∈ B := hVimgB (Subgroup.mem_map_of_mem q hv)
    have hcent := (Subgroup.mem_centralizer_iff.mp (hYcentB hxY)) (q vH) hvB
    have hzero : q ⁅xH, vH⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def]
      rw [← hcent]
      group
    have hcore : ⁅xH, vH⁆ ∈ pPrimeCore 2 H :=
      (QuotientGroup.eq_one_iff (N := pPrimeCore 2 H) ⁅xH, vH⁆).mp hzero
    exact ⟨⁅xH, vH⁆, hcore, (map_commutatorElement H.subtype xH vH)⟩
  let OV : Subgroup G := oddCoreIn (Subgroup.centralizer (V : Set G))
  let X : Subgroup G := oddCoreIn (Subgroup.centralizer ({b} : Set G)) ⊓ OV
  have hXH : X ≤ H := inf_le_left.trans hObH
  have hOVK : OV ≤ UnbalancedLayer.coreActionKernel J :=
    CFSG.ComponentClassification.Sol76.Sig.oddCoreIn_le_coreActionKernel hJHull.isTwoComponentIn
  have hYmapA : (X.subgroupOf H).map q ≤
      Subgroup.centralizer (A : Set (Hbar H)) :=
    image_centralizes_of_coreActionKernel
      hXH inf_le_right hJH hOVK hOJ (by simpa [A, q] using hJimage)
  have hObOdd : Odd (Nat.card (oddCoreIn (Subgroup.centralizer ({b} : Set G)))) :=
    odd_card_oddCoreIn _
  have hXoddG : Odd (Nat.card X) :=
    hObOdd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : X ≤ _))
  have hXoddH : Odd (Nat.card ↥(X.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
    exact hXoddG
  have hXodd : Odd (Nat.card ↥((X.subgroupOf H).map q)) :=
    hXoddH.of_dvd_nat (Subgroup.card_map_dvd (X.subgroupOf H) q)
  have hXY : (X.subgroupOf H).map q ≤
      Y := by
    dsimp [Y, q]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left)
  have hXbot : (X.subgroupOf H).map q = ⊥ :=
    eq_bot_of_odd_le_centralizer_remaining_component
      hQO hA hbA hbQ2 hYleC hYnorm hYodd hXY hXodd hYmapA
  have hXleR : X ≤ oddCoreIn H := by
    intro x hx
    have hxH : x ∈ H := hXH hx
    let xH : H := ⟨x, hxH⟩
    have hxXH : xH ∈ X.subgroupOf H := by
      simpa [xH, Subgroup.mem_subgroupOf] using hx
    have hmem : q xH ∈ (X.subgroupOf H).map q := Subgroup.mem_map_of_mem q hxXH
    rw [hXbot] at hmem
    have hqx1 : q xH = 1 := Subgroup.mem_bot.mp hmem
    have hxcore : xH ∈ CFSG.pPrimeCore 2 ↥H :=
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 ↥H) xH).mp hqx1
    exact ⟨xH, hxcore, rfl⟩
  rw [Sol76.Sig.theta]
  exact sup_le hcomm hXleR

theorem coreRecovery_of_marked_factors
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {H Km Kn B V : Subgroup G}
    (hFam : IsomorphicFamily S T)
    (hKm : Km ∈ markedComponents S T H) (hKn : Kn ∈ markedComponents S T H)
    (hne : Km ≠ Kn) (hB : IsKleinFour B) (hBKm : B ≤ Km)
    [CFSG.IsElementaryAbelian 2 V] (hVne : V ≠ ⊥) (hVKn : V ≤ Kn)
    (hVB : V ≤ centralizer (B : Set G))
    (hAllPure : ∀ K ∈ markedComponents S T H, ∀ t ∈ K, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H)
    (hSchreier : ∀ v ∈ V, v ≠ 1 →
      CFSG.ComponentClassification.LBalance.SchreierSections
        ↥(centralizer ({v} : Set G))) :
    oddCoreIn H = wGroup B V ∧
      ∀ b ∈ B, b ≠ 1 → theta V b = oddCoreIn H ⊓ centralizer ({b} : Set G) := by
  have hV2 : IsPGroup 2 V := CFSG.IsElementaryAbelian.isPGroup 2 V
  have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
  obtain ⟨v, -, hv2⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.exists_mem_center_orderOf_eq_two hV2
  have hvG2 : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hv2
  have hBV : B ≤ centralizer (V : Set G) := by
    intro b hb
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      ((Subgroup.mem_centralizer_iff.mp (hVB hv)) b hb).symm
  have hbaseB : ∀ b ∈ B, b ≠ 1 → base (centralizer ({b} : Set G)) ≤ H := by
    intro b hb hb1
    exact (hAllPure Km hKm b (hBKm hb)
      (CFSG.Goldschmidt75.orderOf_eq_two_of_isKleinFour hB hb hb1)).2
  have htheta : ∀ b ∈ B, b ≠ 1 → theta V b ≤ oddCoreIn H := by
    intro b hb hb1
    have hVb : V ≤ centralizer ({b} : Set G) := by
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hVB hv)) b hb).symm
    exact theta_le_oddCoreIn_of_all_pure_containment hFam hKm hKn hne (hBKm hb)
      (CFSG.Goldschmidt75.orderOf_eq_two_of_isKleinFour hB hb hb1)
      hVne hVKn hVb hAllPure hSchreier
  exact coreRecovery_of_localBase hB (hBKm.trans hKm.1.1) hV2
    (hVKn.trans hKn.1.1) hBV hbaseB v.2
    (hAllPure Kn hKn (v : G) (hVKn v.2) hvG2).2 htheta

theorem coreRecovery_zpowers_of_marked_factors
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {H Km Kn B : Subgroup G} {x : G}
    (hFam : IsomorphicFamily S T)
    (hKm : Km ∈ markedComponents S T H) (hKn : Kn ∈ markedComponents S T H)
    (hne : Km ≠ Kn) (hB : IsKleinFour B) (hBKm : B ≤ Km)
    (hxKn : x ∈ Kn) (hx2 : orderOf x = 2) (hxB : x ∈ centralizer (B : Set G))
    (hAllPure : ∀ K ∈ markedComponents S T H, ∀ t ∈ K, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H)
    (hSchreier : CFSG.ComponentClassification.LBalance.SchreierSections
      ↥(centralizer ({x} : Set G))) :
    oddCoreIn H = wGroup B (zpowers x) ∧
      ∀ b ∈ B, b ≠ 1 → theta (zpowers x) b =
        oddCoreIn H ⊓ centralizer ({b} : Set G) := by
  have hxpow : x ^ 2 = 1 := by
    simpa only [hx2] using pow_orderOf_eq_one x
  have : CFSG.IsElementaryAbelian 2 (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxpow
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    norm_num at hx2
  have hVne : zpowers x ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hx1
  apply coreRecovery_of_marked_factors hFam hKm hKn hne hB hBKm hVne
    (Subgroup.zpowers_le.mpr hxKn) (Subgroup.zpowers_le.mpr hxB) hAllPure
  intro v hv hv1
  obtain h1 | rfl := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hx2).mp hv
  · exact (hv1 h1).elim
  · exact hSchreier

theorem oddCoreIn_conjugate_eq_of_transported_fourgroup
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {H Km KmG Kx B : Subgroup G} {x g : G}
    (hFam : IsomorphicFamily S T)
    (hKm : Km ∈ markedComponents S T H) (hKmG : KmG ∈ markedComponents S T H)
    (hKx : Kx ∈ markedComponents S T H) (hne : Km ≠ Kx) (hneG : KmG ≠ Kx)
    (hB : IsKleinFour B) (hBKm : B ≤ Km) (hBgKmG : conjugate B g ≤ KmG)
    (hxKx : x ∈ Kx) (hx2 : orderOf x = 2) (hxB : x ∈ centralizer (B : Set G))
    (hg : g ∈ centralizer ({x} : Set G))
    (hAllPure : ∀ K ∈ markedComponents S T H, ∀ t ∈ K, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H)
    (hSchreier : CFSG.ComponentClassification.LBalance.SchreierSections
      ↥(centralizer ({x} : Set G))) :
    conjugate (oddCoreIn H) g = oddCoreIn H ∧
      g ∈ normalizer (oddCoreIn H : Set G) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hφx : φ x = x := by
    have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hfix : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [hcomm]
        _ = x := by group
    simpa only [φ, MulAut.conj_apply, inv_inv] using hfix
  have hBg : IsKleinFour (conjugate B g) :=
    CFSG.GorensteinWalter.isKleinFour_map_mulEquiv_cross B hB φ
  have hxBg : x ∈ centralizer (conjugate B g : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    have h := congrArg φ ((Subgroup.mem_centralizer_iff.mp hxB) b0 hb0)
    simpa only [map_mul, hφx, φ, MulEquiv.coe_toMonoidHom] using h
  have hrec := coreRecovery_zpowers_of_marked_factors hFam hKm hKx hne hB hBKm
    hxKx hx2 hxB hAllPure hSchreier
  have hrecG := coreRecovery_zpowers_of_marked_factors hFam hKmG hKx hneG hBg hBgKmG
    hxKx hx2 hxBg hAllPure hSchreier
  have hEq : conjugate (oddCoreIn H) g = oddCoreIn H := by
    calc conjugate (oddCoreIn H) g = conjugate (wGroup B (zpowers x)) g := by rw [hrec.1]
      _ = wGroup (conjugate B g) (zpowers x) := by
        change (wGroup B (zpowers x)).map φ.toMonoidHom =
          wGroup (B.map φ.toMonoidHom) (zpowers x)
        rw [Sol76.Sig.map_wGroup, MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, hφx]
      _ = oddCoreIn H := hrecG.1.symm
  have hi : g⁻¹ ∈ normalizer (oddCoreIn H : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq
  exact ⟨hEq, by simpa only [inv_inv] using (normalizer (oddCoreIn H : Set G)).inv_mem hi⟩

end CFSG.ComponentClassification.FooteMarked
