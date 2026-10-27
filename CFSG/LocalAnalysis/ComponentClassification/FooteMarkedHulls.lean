module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33
public import CFSG.ClassicalInvolution.Balance.FuzzyAdjAxis
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaImage
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {S : Set (Subgroup G)} {T : Type*} [Group T]

omit [Finite G] in
theorem classicalOddCoreIn_eq_oddCoreIn (X : Subgroup G) :
    CFSG.ClassicalInvolution.Balance.oddCoreIn X = FooteLit.oddCoreIn X := by
  unfold CFSG.ClassicalInvolution.Balance.oddCoreIn FooteLit.oddCoreIn
  congr 1
  unfold CFSG.Open.componentClassificationOddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_setOf_eq, Nat.coprime_two_left]

theorem coreActionKernel_le_trivialOnQuot (J : Subgroup G) :
    coreActionKernel J ≤ CFSG.ClassicalInvolution.Balance.Bootstrap.trivialOnQuot J := by
  intro a ha
  obtain ⟨haN, -⟩ := mem_coreActionKernel.mp ha
  refine ⟨haN, fun x hx => ?_⟩
  have hainv : a⁻¹ ∈ coreActionKernel J := (coreActionKernel J).inv_mem ha
  have hmem : x * a * x⁻¹ * a⁻¹ ∈ FooteLit.oddCoreIn J := by
    have h := (mem_coreActionKernel.mp hainv).2 x⁻¹ (J.inv_mem hx)
    simpa [FooteLit.oddCoreIn, mul_assoc] using h
  have hcomm : ⁅a, x⁆ ∈ FooteLit.oddCoreIn J := by
    rw [show ⁅a, x⁆ = (x * a * x⁻¹ * a⁻¹)⁻¹ by
      rw [commutatorElement_def]; group]
    exact (FooteLit.oddCoreIn J).inv_mem hmem
  rwa [← classicalOddCoreIn_eq_oddCoreIn] at hcomm

omit [Finite G] in
theorem fixedShadow_eq_perfectResidualOf (M U : Subgroup G) :
    fixedShadow M U =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (M ⊓ centralizer (U : Set G)) := rfl

omit [Finite G] in
theorem fixedShadow_le_centralizer (M U : Subgroup G) :
    fixedShadow M U ≤ centralizer (U : Set G) :=
  (Subgroup.map_subtype_le _).trans inf_le_right

theorem odd_card_oddCoreIn (H : Subgroup G) :
    Odd (Nat.card (FooteLit.oddCoreIn H)) := by
  rw [← classicalOddCoreIn_eq_oddCoreIn]
  exact CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn H

theorem fixedShadow_cover_of_perfect {M U : Subgroup G} (hM : Group.IsPerfect M)
    (hU2 : IsPGroup 2 U) (hU : U ≤ coreActionKernel M) :
    ∀ x ∈ M, ∃ i ∈ fixedShadow M U, ∃ n ∈ FooteLit.oddCoreIn M, x = i * n := by
  have hUtq : U ≤ CFSG.ClassicalInvolution.Balance.Bootstrap.trivialOnQuot M :=
    hU.trans (coreActionKernel_le_trivialOnQuot M)
  have hcover := CFSG.ClassicalInvolution.Balance.Bootstrap.exists_perfectResidual_mul
    (J := M) (A := U) hM hU2 hUtq
  intro x hx
  obtain ⟨i, hi, n, hn, hx'⟩ := hcover x hx
  refine ⟨i, ?_, n, ?_, hx'⟩
  · rwa [fixedShadow_eq_perfectResidualOf]
  · rwa [← classicalOddCoreIn_eq_oddCoreIn]

omit [Finite G] in
theorem fixedShadow_sup_oddCoreIn_eq_of_cover {M U : Subgroup G}
    (hcov : ∀ x ∈ M, ∃ i ∈ fixedShadow M U, ∃ n ∈ FooteLit.oddCoreIn M, x = i * n) :
    fixedShadow M U ⊔ FooteLit.oddCoreIn M = M := by
  refine le_antisymm (sup_le (fixedShadow_le M U) (Subgroup.map_subtype_le _)) ?_
  intro x hx
  obtain ⟨i, hi, n, hn, rfl⟩ := hcov x hx
  exact mul_mem (Subgroup.mem_sup_left hi) (Subgroup.mem_sup_right hn)

structure FixedShadowHull (S : Set (Subgroup G)) (T : Type*) [Group T]
    (M U J : Subgroup G) : Prop where
  isTwoComponentIn : IsTwoComponentIn J (centralizer (U : Set G))
  marked : Marked S T J
  cover : fixedShadow M U ⊔ oddCoreIn J = J
  normalClosure : conjClosure (fixedShadow M U)
    (twoLayerIn (centralizer (U : Set G))) = J

omit [Finite G] in
theorem exists_fixedShadowHull (hST : MarkedST S T) {M U : Subgroup G}
    (hM : Marked S T M) (hU2 : IsPGroup 2 U) (hU : U ≤ coreActionKernel M)
    (hUne : U ≠ ⊥) : ∃ J, FixedShadowHull S T M U J := by
  obtain ⟨J, hcomp, hmark, hclos, hcov⟩ := hST M hM U hU2 hU hUne
  exact ⟨J, hcomp, hmark, hcov, hclos⟩

omit [Finite G] in
theorem FixedShadowHull.fixedShadow_le {M U J : Subgroup G}
    (h : FixedShadowHull S T M U J) : fixedShadow M U ≤ J := by
  rw [← h.cover]
  exact le_sup_left

theorem FixedShadowHull.oddCoreIn_le_centralizer {M U J : Subgroup G}
    (h : FixedShadowHull S T M U J) :
    oddCoreIn J ≤ oddCoreIn (centralizer (U : Set G)) :=
  FooteLit.oddCoreIn_le_of_isTwoComponentIn h.isTwoComponentIn

omit [Finite G] in
theorem FixedShadowHull.le_of_fixedShadow_le {M U J H : Subgroup G}
    (h : FixedShadowHull S T M U J) (hSH : fixedShadow M U ≤ H)
    (hO : oddCoreIn J ≤ H) : J ≤ H := by
  rw [← h.cover]
  exact sup_le hSH hO

@[expose] def AllInvolutionOddCoreLe (E0 H : Subgroup G) : Prop :=
  ∀ z : G, z ∈ centralizer (E0 : Set G) →
    orderOf z = 2 → oddCoreOfCentralizer z ≤ H

theorem FixedShadowHull.le_of_fixedShadow_le_of_oddCore_le {M J H : Subgroup G} {z : G}
    (h : FixedShadowHull S T M (zpowers z) J) (_hz : orderOf z = 2)
    (hOz : oddCoreOfCentralizer z ≤ H) (hSH : fixedShadow M (zpowers z) ≤ H) : J ≤ H := by
  refine h.le_of_fixedShadow_le hSH ?_
  refine h.oddCoreIn_le_centralizer.trans ?_
  rw [CFSG.GroupTheory.centralizer_zpowers_eq]
  exact hOz

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) :
    IsPGroup 2 (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hz]
  norm_num

omit [Finite G] in
theorem zpowers_ne_bot_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) :
    zpowers z ≠ ⊥ := by
  refine Subgroup.zpowers_ne_bot.mpr ?_
  intro hz1
  rw [hz1, orderOf_one] at hz
  omega

theorem exists_fixedShadowHull_le_of_fixedShadow_le_of_oddCore_le
    (hST : MarkedST S T) {M : Subgroup G} (hM : Marked S T M) {z : G}
    (hz : orderOf z = 2) (hzK : z ∈ coreActionKernel M) {H : Subgroup G}
    (hOz : oddCoreOfCentralizer z ≤ H) (hSH : fixedShadow M (zpowers z) ≤ H) :
    ∃ J, FixedShadowHull S T M (zpowers z) J ∧ J ≤ H := by
  obtain ⟨J, hJ⟩ := exists_fixedShadowHull (S := S) (T := T) hST hM
    (isPGroup_zpowers_of_orderOf_eq_two hz) (Subgroup.zpowers_le.mpr hzK)
    (zpowers_ne_bot_of_orderOf_eq_two hz)
  exact ⟨J, hJ, hJ.le_of_fixedShadow_le_of_oddCore_le hz hOz hSH⟩

theorem exists_fixedShadowHull_le_of_source_le (hST : MarkedST S T) {M : Subgroup G}
    (hM : Marked S T M) {z : G} (hz : orderOf z = 2) (hzK : z ∈ coreActionKernel M)
    {H : Subgroup G} (hOz : oddCoreOfCentralizer z ≤ H) (hMH : M ≤ H) :
    ∃ J, FixedShadowHull S T M (zpowers z) J ∧ J ≤ H :=
  exists_fixedShadowHull_le_of_fixedShadow_le_of_oddCore_le hST hM hz hzK hOz
    ((fixedShadow_le M (zpowers z)).trans hMH)

theorem B0_le_fixedShadow {M : Subgroup G} (hM : Marked S T M) {v : G} (hv : orderOf v = 2)
    (hvK : v ∈ coreActionKernel M) {B0 : Subgroup G} (hB0M : B0 ≤ M)
    (hB02 : IsPGroup 2 B0) (hB0v : B0 ≤ centralizer ({v} : Set G)) :
    B0 ≤ fixedShadow M (zpowers v) := by
  classical
  have hMperf : Group.IsPerfect M := hM.1
  have hv2 : IsPGroup 2 (zpowers v) := isPGroup_zpowers_of_orderOf_eq_two hv
  have hvZ : zpowers v ≤ coreActionKernel M := Subgroup.zpowers_le.mpr hvK
  have hcov : ∀ x ∈ M, ∃ i ∈ fixedShadow M (zpowers v),
      ∃ n ∈ oddCoreIn M, x = i * n :=
    fixedShadow_cover_of_perfect hMperf hv2 hvZ
  have hsup : fixedShadow M (zpowers v) ⊔ oddCoreIn M = M :=
    fixedShadow_sup_oddCoreIn_eq_of_cover hcov
  set C : Subgroup G := M ⊓ centralizer (zpowers v) with hC
  set I : Subgroup G := fixedShadow M (zpowers v) with hI
  set O : Subgroup G := oddCoreIn M with hO
  have hB0v' : B0 ≤ centralizer (zpowers v) := by
    rwa [CFSG.GroupTheory.centralizer_zpowers_eq]
  have hB0C : B0 ≤ C := le_inf hB0M hB0v'
  have hIC : I ≤ C := le_inf (fixedShadow_le M (zpowers v)) (fixedShadow_le_centralizer M (zpowers v))
  have hIR : I = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf C := by
    rw [hI, fixedShadow_eq_perfectResidualOf]
  have hInorm : (I.subgroupOf C).Normal := by
    rw [hIR]
    have hle : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf C ≤ C :=
      Subgroup.map_subtype_le _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.le_normalizer.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains C))
  have hOodd : Odd (Nat.card (O.subgroupOf C)) := by
    let f : O.subgroupOf C →* O :=
      { toFun := fun x => ⟨(x.1 : G), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine (odd_card_oddCoreIn M).of_dvd_nat (Subgroup.card_dvd_of_injective f ?_)
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : O => (z : G)) hxy
  have hgen : I.subgroupOf C ⊔ O.subgroupOf C = ⊤ := by
    have : (I.subgroupOf C).Normal := hInorm
    apply eq_top_iff.mpr
    rintro c -
    have hcM : (c : G) ∈ M := c.2.1
    obtain ⟨i, hi, n, hn, hx⟩ := hcov (c : G) hcM
    have hiC : i ∈ C := hIC hi
    have hnC : n ∈ C := by
      have hn_eq : n = i⁻¹ * (c : G) := by
        rw [hx]; group
      rw [hn_eq]
      exact C.mul_mem (C.inv_mem hiC) c.2
    refine (Subgroup.mem_sup_of_normal_left).mpr ?_
    refine ⟨⟨i, hiC⟩, ?_, ⟨n, hnC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hi
    · rw [Subgroup.mem_subgroupOf]; exact hn
    · apply Subtype.ext
      simpa using hx.symm
  have hquotodd : Odd (Nat.card (C ⧸ I.subgroupOf C)) :=
    CFSG.ShultStronglyClosedTI.LocalTheta.normal_odd_supplement_quotient
      (I.subgroupOf C) (O.subgroupOf C) hOodd hgen
  set B : Subgroup C := B0.subgroupOf C with hB
  have hB2 : IsPGroup 2 B := hB02.comap_subtype
  have hBmapOdd : Odd (Nat.card (B.map (QuotientGroup.mk' (I.subgroupOf C)))) := by
    refine hquotodd.of_dvd_nat ?_
    simpa using Subgroup.card_dvd_of_le
      (H := B.map (QuotientGroup.mk' (I.subgroupOf C))) (K := ⊤) le_top
  have hBker : B ≤ (QuotientGroup.mk' (I.subgroupOf C)).ker :=
    CFSG.Wreathed.PrimewisePerfectLift.two_subgroup_le_kernel_of_odd_image
      B hB2 (QuotientGroup.mk' (I.subgroupOf C)) hBmapOdd
  intro x hx
  have hxC : x ∈ C := hB0C hx
  have hxsub : (⟨x, hxC⟩ : C) ∈ B := by
    rw [hB, Subgroup.mem_subgroupOf]
    exact hx
  have hxker := hBker hxsub
  rw [QuotientGroup.ker_mk'] at hxker
  exact Subgroup.mem_subgroupOf.mp hxker

theorem isTwoComponentIn_le_twoLayerIn_centralizer {v : G} {P J : Subgroup G}
    (hvP : v ∈ P)
    (hPX : P ≤ Subgroup.centralizer ({v} : Set G))
    (hP2 : IsPGroup 2 P)
    (hJ : IsTwoComponentIn J (Subgroup.centralizer (P : Set G)))
    (hS : LBalance.SchreierSections ↥(Subgroup.centralizer ({v} : Set G))) :
    J ≤ FooteLit.twoLayerIn (Subgroup.centralizer ({v} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := Subgroup.centralizer ({v} : Set G)
  have hCPX : Subgroup.centralizer (P : Set G) ≤ X := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg v hvP).symm
  have hP2' : IsPGroup 2 (P.subgroupOf X) :=
    hP2.comap_of_injective X.subtype X.subtype_injective
  have hbal := (LBalance.l_balance_clauses_of_schreierSections hS 2 Nat.prime_two
    (P.subgroupOf X) hP2').2
  have hmap := Subgroup.map_mono (f := X.subtype) hbal
  rw [CFSG.centralizer_subgroupOf_eq P X hPX] at hmap
  rw [LBalance.pLayer_nested_map 2 (Subgroup.centralizer (P : Set G)) X hCPX] at hmap
  rw [← Subgroup.subgroupOf_self X] at hmap
  rw [LBalance.pLayer_nested_map 2 X X le_rfl] at hmap
  have hcomp : CFSG.Open.lBalanceIsPComponent 2
      (Subgroup.centralizer (P : Set G)) J :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance 2
      (Subgroup.centralizer (P : Set G)) J hJ.1).mp hJ.2
  have hJle : J ≤ CFSG.Open.lBalancePLayer 2
      (Subgroup.centralizer (P : Set G)) :=
    le_sSup hcomp
  have hJX : J ≤ CFSG.Open.lBalancePLayer 2 X := hJle.trans hmap
  rw [LBalance.Asm.lBalancePLayer_eq_map] at hJX
  exact hJX

theorem FixedShadowHull.le_twoLayerIn_centralizer
    {S : Set (Subgroup G)} {T : Type*} [Group T] {M P J : Subgroup G}
    (h : FixedShadowHull S T M P J) {v : G} (hvP : v ∈ P)
    (hPX : P ≤ Subgroup.centralizer ({v} : Set G))
    (hP2 : IsPGroup 2 P)
    (hS : LBalance.SchreierSections ↥(Subgroup.centralizer ({v} : Set G))) :
    J ≤ FooteLit.twoLayerIn (Subgroup.centralizer ({v} : Set G)) :=
  isTwoComponentIn_le_twoLayerIn_centralizer hvP hPX hP2 h.isTwoComponentIn hS

theorem FixedShadowHull.le_of_base_le
    {S : Set (Subgroup G)} {T : Type*} [Group T] {M P J H : Subgroup G}
    (h : FixedShadowHull S T M P J) {v : G} (hvP : v ∈ P)
    (hPX : P ≤ Subgroup.centralizer ({v} : Set G))
    (hP2 : IsPGroup 2 P)
    (hS : LBalance.SchreierSections ↥(Subgroup.centralizer ({v} : Set G)))
    (hbase : base (Subgroup.centralizer ({v} : Set G)) ≤ H) :
    J ≤ H := by
  refine (h.le_twoLayerIn_centralizer hvP hPX hP2 hS).trans ?_
  exact (show FooteLit.twoLayerIn (Subgroup.centralizer ({v} : Set G)) ≤
      base (Subgroup.centralizer ({v} : Set G)) by
    dsimp [base]
    exact le_sup_right).trans hbase

end CFSG.ComponentClassification.FooteMarked
