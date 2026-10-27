module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientHyp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.GroupTheory.LocalCores.ComponentCentralizer
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.ComponentClassification.Sol76StrongEmb
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatalogueBPrimeJoin
open CFSG.ComponentClassification.Sol76
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

abbrev Hbar (H : Subgroup G) : Type _ := ↥H ⧸ pPrimeCore 2 ↥H

abbrev HbarMap (H : Subgroup G) : ↥H →* Hbar H :=
  QuotientGroup.mk' (pPrimeCore 2 ↥H)

theorem image_oddCoreCentralizer_normal_in_full_quotient_centralizer
    (H : Subgroup G) {b : G} (hbH : b ∈ H) (hb2 : orderOf b = 2)
    (hObH : oddCoreOfCentralizer b ≤ H) :
    let Y := ((oddCoreOfCentralizer b).subgroupOf H).map (HbarMap H)
    let CQ := centralizer ({HbarMap H ⟨b, hbH⟩} : Set (Hbar H))
    Y ≤ CQ ∧ Odd (Nat.card Y) ∧ (Y.subgroupOf CQ).Normal ∧
      (centralizer ({(⟨b, hbH⟩ : H)} : Set H)).map (HbarMap H) = CQ := by
  let bH : H := ⟨b, hbH⟩
  let Y := ((oddCoreOfCentralizer b).subgroupOf H).map (HbarMap H)
  let CQ := centralizer ({HbarMap H bH} : Set (Hbar H))
  let q : centralizer ({bH} : Set H) →* CQ :=
    ((HbarMap H).comp
          (Subgroup.centralizer ({bH} : Set H)).subtype).codRestrict
        (CQ) (by
          intro x
          rw [Subgroup.mem_centralizer_singleton_iff]
          change HbarMap H x.1 * HbarMap H (bH) =
            HbarMap H (bH) * HbarMap H x.1
          rw [← map_mul, ← map_mul]
          exact congrArg (HbarMap H)
            (Subgroup.mem_centralizer_singleton_iff.mp x.2))
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let O : Subgroup G := CFSG.ComponentClassification.FooteLit.oddCoreIn C
  let CH : Subgroup H := Subgroup.centralizer ({bH} : Set H)
  let D : Subgroup H := O.subgroupOf H
  have hOodd : Odd (Nat.card O) := by
    dsimp [O, CFSG.ComponentClassification.FooteLit.oddCoreIn]
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C))
  have hOleC : O ≤ C := by
    dsimp [O, CFSG.ComponentClassification.FooteLit.oddCoreIn]
    exact Subgroup.map_subtype_le _
  have hOsubNormalC : (O.subgroupOf C).Normal := by
    dsimp [O, CFSG.ComponentClassification.FooteLit.oddCoreIn]
    rw [← Subgroup.comap_subtype]
    rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    infer_instance
  let incl : CH →* C :=
    { toFun := fun x =>
        ⟨x.1.1, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val
            (Subgroup.mem_centralizer_singleton_iff.mp x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hDn : (D.subgroupOf CH).Normal := by
    have hEq : (O.subgroupOf C).comap incl = D.subgroupOf CH := by
      ext x
      rfl
    rw [← hEq]
    exact hOsubNormalC.comap incl
  have hDleCH : D ≤ CH := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxC : (x : G) ∈ C := hOleC (show (x : G) ∈ O from hx)
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hDodd : Odd (Nat.card D) := by
    dsimp [D]
    have hOH : O ≤ H := hObH
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
    exact hOodd
  have hYodd : Odd (Nat.card (Y)) := by
    change Odd (Nat.card (D.map (HbarMap H)))
    exact hDodd.of_dvd_nat (Subgroup.card_map_dvd D (HbarMap H))
  have hNodd : Odd (Nat.card (CFSG.pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hbH2 : orderOf (bH) = 2 := by
    simpa [bH, Subgroup.orderOf_coe] using hb2
  have hmapC : (Subgroup.centralizer ({bH} : Set H)).map (HbarMap H) =
      CQ := by
    simpa [HbarMap, CQ] using
      (CFSG.ComponentClassification.FooteLit.map_centralizer_mk'_of_odd
        (X := ↥H) (N := CFSG.pPrimeCore 2 ↥H) hNodd hbH2)
  have hYleCfull : Y ≤ CQ := by
    change D.map (HbarMap H) ≤ CQ
    rw [← hmapC]
    exact Subgroup.map_mono hDleCH
  have hNmap : (D.subgroupOf CH).map (q) =
      (Y).subgroupOf (CQ) := by
    ext y
    constructor
    · rintro ⟨x, hxN, rfl⟩
      exact Subgroup.mem_map_of_mem (HbarMap H) hxN
    · intro hy
      have hy' : (y : Hbar H) ∈ Y := Subgroup.mem_subgroupOf.mp hy
      rcases Subgroup.mem_map.mp hy' with ⟨x, hxO, hxy⟩
      have hxCH : x ∈ CH := hDleCH hxO
      refine ⟨⟨x, hxCH⟩, hxO, ?_⟩
      apply Subtype.ext
      exact hxy
  have hsurj : Function.Surjective q := by
    intro y
    have hy : (y : Hbar H) ∈ CH.map (HbarMap H) := by
      change (y : Hbar H) ∈ (centralizer ({bH} : Set H)).map (HbarMap H)
      rw [hmapC]
      exact y.2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hYnormal : ((Y).subgroupOf (CQ)).Normal := by
    rw [← hNmap]
    exact Subgroup.Normal.map hDn (q) hsurj
  exact ⟨hYleCfull, hYodd, hYnormal, hmapC⟩

theorem odd_normal_centralizer_centralizes_other_components
    {Q : Type} [Group Q] [Finite Q] {A Y : Subgroup Q} {b : Q}
    (hA : IsComponent A) (hbA : b ∈ A)
    (hYC : Y ≤ centralizer ({b} : Set Q))
    (hYn : (Y.subgroupOf (centralizer ({b} : Set Q))).Normal)
    (hYodd : Odd (Nat.card Y)) :
    ∀ B : Subgroup Q, IsComponent B → B ≠ A → Y ≤ centralizer (B : Set Q) := by
  intro B hB hBA
  let C := centralizer ({b} : Set Q)
  have hBC : B ≤ C := by
    have hcomm := (LocalCores.distinct_components_commute hB hA).resolve_left hBA
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hcent hx) b hbA).symm
  have hBsub : IsComponent (B.subgroupOf C) := LocalCores.component_overgroup hB hBC
  have hYoddC : Odd (Nat.card (Y.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv]
    exact hYodd
  have hYsolv : Group.IsSolvable (Y.subgroupOf C) := Milestones.odd_order_solvable hYoddC
  have hcomm := (LocalCores.component_solvable_centralizer hYsolv hYn.isSubnormal).1
    (B.subgroupOf C) hBsub
  rw [Subgroup.commutator_comm] at hcomm
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro y hy
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have h := Subgroup.mem_centralizer_iff.mp
    (hcent (show (⟨y, hYC hy⟩ : C) ∈ Y.subgroupOf C from hy))
    (⟨x, hBC hx⟩ : C) hx
  exact congrArg Subtype.val h

theorem odd_normal_centralizer_centralizes_fittingFactors
    {Q : Type} [Group Q] [Finite Q] {A Y : Subgroup Q} {b : Q}
    (hA : IsComponent A) (hbA : b ∈ A) (hb2 : orderOf b = 2)
    (hYC : Y ≤ centralizer ({b} : Set Q))
    (hYn : (Y.subgroupOf (centralizer ({b} : Set Q))).Normal)
    (hYodd : Odd (Nat.card Y)) :
    (∀ B : Subgroup Q, IsComponent B → B ≠ A → Y ≤ centralizer (B : Set Q)) ∧
      Y ≤ centralizer (pCore 2 Q : Set Q) := by
  have hT : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hDC : Y ≤ centralizer ((zpowers b : Subgroup Q) : Set Q) := by
    rwa [CFSG.GroupTheory.centralizer_zpowers_eq]
  have hDn : (Y.subgroupOf (centralizer ((zpowers b : Subgroup Q) : Set Q))).Normal := by
    rwa [CFSG.GroupTheory.centralizer_zpowers_eq]
  have hcomm := SmallLocal.normal_coprime_centralizer_centralizes_prime_core
    Nat.prime_two hT hDC hDn (Nat.coprime_two_left.mpr hYodd)
  exact ⟨odd_normal_centralizer_centralizes_other_components hA hbA hYC hYn hYodd,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm⟩

theorem eq_bot_of_odd_le_centralizer_remaining_component
    {Q : Type} [Group Q] [Finite Q] {A Y X : Subgroup Q} {b : Q}
    (hO : pPrimeCore 2 Q = ⊥) (hA : IsComponent A) (hbA : b ∈ A) (hb2 : orderOf b = 2)
    (hYC : Y ≤ centralizer ({b} : Set Q))
    (hYn : (Y.subgroupOf (centralizer ({b} : Set Q))).Normal)
    (hYodd : Odd (Nat.card Y)) (hXY : X ≤ Y) (hXodd : Odd (Nat.card X))
    (hXA : X ≤ centralizer (A : Set Q)) : X = ⊥ := by
  have hparts := odd_normal_centralizer_centralizes_fittingFactors hA hbA hb2 hYC hYn hYodd
  have hF : X ≤ centralizer (fittingSubgroup Q : Set Q) := by
    rw [Fitting_eq_pcore Q 2 hO]
    exact hXY.trans hparts.2
  have hE : ∀ B : Subgroup Q, IsComponent B → X ≤ centralizer (B : Set Q) := by
    intro B hB
    by_cases hBA : B = A
    · exact hBA ▸ hXA
    · exact hXY.trans (hparts.1 B hB hBA)
  exact GrSLit.eq_bot_of_odd_le_centralizer_generalizedFitting hO
    (LocalCores.le_centralizer_generalizedFitting hF hE) hXodd

end CFSG.ComponentClassification.FooteMarked
