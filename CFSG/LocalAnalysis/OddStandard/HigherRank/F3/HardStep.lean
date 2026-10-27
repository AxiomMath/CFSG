module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardComp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardLayer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardMType
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCaseII

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit
open CFSG.ASVolI.ChIJK (IsComponentIn)

theorem pPrimeCore_eq_bot_of_oddCore {Q : Type*} [Group Q] (h : CFSG.oddCore Q = ⊥) :
    pPrimeCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore] at h
  rwa [CFSG.pPrimeCore_eq_piCore]

private theorem mem_centralizer_mul {G : Type} [Group G] {a b x : G}
    (ha : x ∈ centralizer ({a} : Set G)) (hb : x ∈ centralizer ({b} : Set G)) :
    x ∈ centralizer ({a * b} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Commute.mul_right (Subgroup.mem_centralizer_singleton_iff.mp ha)
      (Subgroup.mem_centralizer_singleton_iff.mp hb))

private theorem catalog_quotCenter {G : Type} [Group G] (hK : Assembly.KProper Blueprint.Catalog G)
    {M : Subgroup G} (hM : M ≠ ⊤) (hq : CFSG.IsQuasisimple ↥M) :
    Blueprint.Catalog (↥M ⧸ center ↥M) := by
  haveI : IsSimpleGroup (↥M ⧸ center ↥M) := hq.2.1
  exact KCore.KProperNonab.catalogue_of_surjective SectionRank.catalog_isoInvariant hK M hM
    hq.2.2 (QuotientGroup.mk' (center ↥M)) (QuotientGroup.mk'_surjective _)

theorem false_of_ambient (hH : Harris82Theorem1KProper) (hL : CFSG.StandardType.GGLBalanceInput)
    (hbr : Assembly.CatalogImp Blueprint.Catalog Assembly.InCatalog) (hKR : T1.KnownRowThree)
    (hC3 : LinUnitInvolutionComponents) (hC4 : POmegaPlusNotLinUnit) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {ν₁ ν₂ w : G} (h₁ : orderOf ν₁ = 2) (h₂ : orderOf ν₂ = 2) (h₁₂ : ν₁ * ν₂ = ν₂ * ν₁)
    (hw : w = ν₁ * ν₂) (hw2 : orderOf w = 2) {A B : Subgroup G}
    (hA : IsComponentIn A (centralizer {w})) (hB : IsComponentIn B (centralizer {w}))
    (hAB : A ≤ centralizer (B : Set G)) (hν₁A : ν₁ ∈ A) (hAν₁ : A ≤ centralizer {ν₁})
    (hν₂B : ν₂ ∈ B) {n : ℕ} (hn : n = 4 ∨ n = 6)
    (hmA : Blueprint.LieModel (↥A ⧸ center ↥A) .POmegaPlus n 3 1)
    (hmB : Blueprint.LieModel (↥B ⧸ center ↥B) .POmegaPlus n 3 1) : False := by
  have hν₁ne : ν₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at h₁
    exact absurd h₁ (by norm_num)
  have hsq : ν₁ * ν₁ = 1 := by
    have := pow_orderOf_eq_one ν₁
    rwa [h₁, sq] at this
  have hw2sq : w ^ 2 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2] at this
  have hν₂w : ν₂ = ν₁ * w := by rw [hw, ← mul_assoc, hsq, one_mul]
  have hNtop : centralizer ({ν₁} : Set G) ≠ ⊤ :=
    StandardType.centralizer_singleton_ne_top_of_isSimpleGroup hnab hν₁ne
  have hKgrp : CFSG.Open.lBalanceIsKGroup ↥(centralizer ({ν₁} : Set G)) :=
    StandardType.lBalanceIsKGroup_of_kProper (Assembly.KProper.of_catalogImp hbr hK) hNtop
  have hO : pPrimeCore 2 ↥(centralizer ({ν₁} : Set G)) = ⊥ :=
    pPrimeCore_eq_bot_of_oddCore (hbal ν₁ h₁)
  have hν₁N : ν₁ ∈ centralizer ({ν₁} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hν₂N : ν₂ ∈ centralizer ({ν₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h₁₂.symm
  have hwN : w ∈ centralizer ({ν₁} : Set G) := by
    rw [hw]
    exact Subgroup.mul_mem _ hν₁N hν₂N
  have hBN : B ≤ centralizer ({ν₁} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp (hAB hν₁A)) b hb)
  have hA2 : IsTwoComponentIn A (centralizer ({ν₁} : Set G) ⊓ centralizer {w}) :=
    isTwoComponentIn_of_isComponentIn
      (isComponentIn_of_le_of_le hA (le_inf hAν₁ hA.1) inf_le_right) ⟨ν₁, hν₁A, h₁⟩
  have hB2 : IsTwoComponentIn B (centralizer ({ν₁} : Set G) ⊓ centralizer {w}) :=
    isTwoComponentIn_of_isComponentIn
      (isComponentIn_of_le_of_le hB (le_inf hBN hB.1) inf_le_right) ⟨ν₂, hν₂B, h₂⟩
  have hAle := le_layer_of_lBalance hL hKgrp hO hwN hw2sq hA2
  have hBle := le_layer_of_lBalance hL hKgrp hO hwN hw2sq hB2
  have hwE : w ∈ (layer ↥(centralizer ({ν₁} : Set G))).map
      (centralizer ({ν₁} : Set G)).subtype := by
    rw [hw]
    exact Subgroup.mul_mem _ (hAle hν₁A) (hBle hν₂B)
  obtain ⟨KA, hKA, hAKA⟩ := exists_component_ge hw2 hwN hO hwE hA2
  obtain ⟨KB, hKB, hBKB⟩ := exists_component_ge hw2 hwN hO hwE hB2
  by_cases hc : KA ≤ centralizer ({w} : Set G)
  ·
    have hAeq : A = KA := eq_of_le_of_isSubnormal hKA.2.1 hA.2.1 hAKA
      (isComponentIn_of_le_of_le hA hAKA hc).2.2
    have hAN : IsComponentIn A (centralizer ({ν₁} : Set G)) := by
      rw [hAeq]
      exact hKA
    exact false_of_pOmegaPlus_component hH hC4 hnab hK hcat h₁ hAN hν₁A hn hmA
  ·
    have hKAB : KA = KB := by
      rcases eq_or_le_centralizer_of_isComponentIn hKA hKB with h | h
      · exact h
      · exfalso
        apply hc
        intro x hx
        have hxν₂ : x ∈ centralizer ({ν₂} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr
            ((Subgroup.mem_centralizer_iff.mp (h hx)) ν₂ (hBKB hν₂B)).symm
        rw [hw]
        exact mem_centralizer_mul (hKA.1 hx) hxν₂
    have hBKA : B ≤ KA := by
      rw [hKAB]
      exact hBKB
    have hν₁KA : ν₁ ∈ KA := hAKA hν₁A
    have hν₂KA : ν₂ ∈ KA := hBKA hν₂B
    have hBν₂ : B ≤ centralizer ({ν₂} : Set G) := fun b hb => by
      rw [hν₂w]
      exact mem_centralizer_mul (hBN hb) (hB.1 hb)
    have hBY : IsComponentIn B (KA ⊓ centralizer ({ν₂} : Set G)) :=
      isComponentIn_of_le_of_le hB (le_inf hBKA hBν₂) (fun x hx => by
        rw [hw]
        exact mem_centralizer_mul (hKA.1 (Subgroup.mem_inf.mp hx).1) (Subgroup.mem_inf.mp hx).2)
    have hL' : IsComponentIn (B.subgroupOf KA) (centralizer {(⟨ν₂, hν₂KA⟩ : ↥KA)}) :=
      isComponentIn_subgroupOf_inf hν₂KA hBY
    have hc1 : (⟨ν₁, hν₁KA⟩ : ↥KA) ∈ center ↥KA := by
      rw [Subgroup.mem_center_iff]
      intro y
      ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKA.1 y.2)
    have hc1o : orderOf (⟨ν₁, hν₁KA⟩ : ↥KA) = 2 := (Subgroup.orderOf_mk ν₁ hν₁KA).trans h₁
    have hz2 : orderOf (⟨ν₂, hν₂KA⟩ : ↥KA) = 2 := (Subgroup.orderOf_mk ν₂ hν₂KA).trans h₂
    have hzc : (⟨ν₂, hν₂KA⟩ : ↥KA) ∉ center ↥KA := by
      intro hz
      apply hc
      intro x hx
      have hxν₂ : x ∈ centralizer ({ν₂} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x, hx⟩))
      rw [hw]
      exact mem_centralizer_mul (hKA.1 hx) hxν₂
    have hne : KA ≠ ⊤ := by
      intro htop
      apply hNtop
      rw [eq_top_iff]
      have := hKA.1
      rwa [htop] at this
    have hmL : Blueprint.LieModel (↥(B.subgroupOf KA) ⧸ center ↥(B.subgroupOf KA))
        .POmegaPlus n 3 1 :=
      lieModel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBKA).symm hmB
    exact false_of_component hH hnab hK hcat h₁ hKA hν₁KA
      (isMTypeSchur_of_caseII hKR hC3 hC4 hKA.2.1 (catalog_quotCenter hK hne hKA.2.1) hc1 hc1o
        hz2 hzc hL' hν₂B hn hmL)

end CFSG.OddStandard.HigherRank.F3
