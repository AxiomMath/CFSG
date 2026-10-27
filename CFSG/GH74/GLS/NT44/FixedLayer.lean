module

public import CFSG.GH74.GLS.C3.Layer1.Defs

import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedNormalGeneration
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open scoped commutatorElement

theorem le_pLayer_inf_centralizer_of_le_zStar
    {G : Type} [Group G] [Finite G] {P W Y : Subgroup G}
    (hEQ : CFSG.pLayer (CFSG.GH74.GLS.kBar P) 2 = ⊤)
    (hW2 : IsPGroup 2 W)
    (hWZ : W ≤ CFSG.GH74.GLS.zStar P)
    (hYW : Y ≤ W) :
    W ≤ (CFSG.pLayer ↥(P ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) 2).map
      (P ⊓ Subgroup.centralizer (Y : Set G)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := P ⊓ Subgroup.centralizer (Y : Set G)
  have hCP : C ≤ P := inf_le_left
  have hYP : Y ≤ P := fun y hy => (hWZ (hYW hy)).1
  have hYN : Y ≤ Subgroup.normalizer (P : Set G) :=
    hYP.trans (Subgroup.le_normalizer : P ≤ Subgroup.normalizer (P : Set G))
  let α : ↥Y →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  have hα : ∀ (a : ↥Y) (v : ↥P),
      ((α a v : ↥P) : G) = (a : G) * (v : G) * (a : G)⁻¹ :=
    fun a v => Subgroup.normalizerMonoidHom_apply_apply_coe P _ v
  have hαQ : ∀ (a : ↥Y) (v : ↥P),
      ((α a v : ↥P) : CFSG.GH74.GLS.kBar P) = (v : CFSG.GH74.GLS.kBar P) := by
    intro a v
    rw [eq_comm, QuotientGroup.eq]
    apply (Subgroup.mem_map_iff_mem P.subtype_injective).mp
    have h1 : ⁅((v⁻¹ : ↥P) : G), (a : G)⁆ ∈
        (CFSG.pPrimeCore 2 ↥P).map P.subtype := by
      have h := (hWZ (hYW a.2)).2.2.2 (v⁻¹) v⁻¹.2
      simpa only [CFSG.GH74.GLS.pPrimeCoreOf, Subgroup.coe_inv] using h
    show ((v : ↥P) : G)⁻¹ * ((α a v : ↥P) : G) ∈
      (CFSG.pPrimeCore 2 ↥P).map P.subtype
    rw [hα]
    have hcomm : ⁅((v⁻¹ : ↥P) : G), (a : G)⁆ =
        ((v : ↥P) : G)⁻¹ * ((a : G) * (v : G) * (a : G)⁻¹) := by
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
    rw [← hcomm]
    exact h1
  have hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    exact CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec (T := W) (K := P) hW2 hx hy
      (hWZ hx).1 (hWZ hy).2
  have hN : ¬ 2 ∣ Nat.card (CFSG.pPrimeCore 2 ↥P) := by
    have h1 : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 ↥P)) :=
      CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h1
  have hA : IsPGroup 2 ↥Y := hW2.to_le hYW
  have hEQ' : CFSG.pLayer (↥P ⧸ CFSG.pPrimeCore 2 ↥P) 2 = ⊤ := by
    simpa only [CFSG.GH74.GLS.kBar] using hEQ
  have hfix : CFSG.ComponentClassification.UnbalancedGS.actionFixedSubgroup α =
      C.subgroupOf P := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      rw [CFSG.ComponentClassification.UnbalancedGS.mem_actionFixedSubgroup] at hx
      refine ⟨x.2, ?_⟩
      change (x : G) ∈ Subgroup.centralizer (Y : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxy := hx (⟨y, hy⟩ : ↥Y)
      have hconj : (y : G) * ((x : ↥P) : G) * (y : G)⁻¹ = ((x : ↥P) : G) := by
        simpa only [hα] using congrArg (fun t : ↥P => (t : G)) hxy
      calc
        (y : G) * ((x : ↥P) : G) =
            ((y : G) * ((x : ↥P) : G) * (y : G)⁻¹) * (y : G) := by
          group
        _ = ((x : ↥P) : G) * (y : G) := by
          rw [hconj]
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [CFSG.ComponentClassification.UnbalancedGS.mem_actionFixedSubgroup]
      intro a
      apply Subtype.ext
      rw [hα]
      have hx' : (x : G) ∈ Subgroup.centralizer (Y : Set G) := hx.2
      rw [Subgroup.mem_centralizer_iff] at hx'
      have hcomm : (a : G) * ((x : ↥P) : G) = ((x : ↥P) : G) * (a : G) :=
        hx' (a : G) a.2
      rw [hcomm]
      group
  let V : Subgroup ↥P :=
    (CFSG.pLayer (CFSG.ComponentClassification.UnbalancedGS.actionFixedSubgroup α) 2).map
      (CFSG.ComponentClassification.UnbalancedGS.actionFixedSubgroup α).subtype
  obtain ⟨-, -, hVgen, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.core_trivial_fixed_layer_normal_generation
      (X := ↥P) (p := 2) Nat.prime_two (CFSG.pPrimeCore 2 ↥P)
      hN hA α hαQ hEQ' V rfl
  intro w hwW
  have hwP : w ∈ P := (hWZ hwW).1
  have hwCent : w ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcommW y (hYW hy) w hwW
  have hwC : w ∈ C := ⟨hwP, hwCent⟩
  have hwFix : (⟨w, hwP⟩ : ↥P) ∈
      CFSG.ComponentClassification.UnbalancedGS.actionFixedSubgroup α := by
    rw [CFSG.ComponentClassification.UnbalancedGS.mem_actionFixedSubgroup]
    intro a
    apply Subtype.ext
    rw [hα]
    have hcomm : (a : G) * w = w * (a : G) := hcommW (a : G) (hYW a.2) w hwW
    rw [hcomm]
    group
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hW2) ⟨w, hwW⟩
  have hwOrderW : orderOf w = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨w, hwW⟩ : ↥W)).trans hk
  have hwOrderP : orderOf (⟨w, hwP⟩ : ↥P) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨w, hwP⟩ : ↥P)).symm.trans hwOrderW
  have hwV : (⟨w, hwP⟩ : ↥P) ∈ V := by
    rw [hVgen]
    exact Subgroup.subset_closure ⟨hwFix, ⟨k, hwOrderP⟩⟩
  change (⟨w, hwP⟩ : ↥P) ∈
    (CFSG.pLayer (CFSG.ComponentClassification.UnbalancedGS.actionFixedSubgroup α) 2).map
      (CFSG.ComponentClassification.UnbalancedGS.actionFixedSubgroup α).subtype at hwV
  rw [hfix] at hwV
  obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp hwV
  let e : ↥(C.subgroupOf P) ≃* ↥C := Subgroup.subgroupOfEquivOfLe hCP
  have hzMap : e z ∈ CFSG.pLayer ↥C 2 := by
    have h := Subgroup.mem_map_of_mem e.toMonoidHom hz
    rwa [CFSG.ComponentClassification.UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e] at h
  refine Subgroup.mem_map.mpr ⟨e z, hzMap, ?_⟩
  have hzG : ((z : ↥(C.subgroupOf P)) : G) = w :=
    congrArg (fun t : ↥P => (t : G)) hzval
  have hez : ((e z : ↥C) : G) = ((z : ↥(C.subgroupOf P)) : G) := rfl
  exact hez.trans hzG

end CFSG.GH74.GLS.NT44

end
