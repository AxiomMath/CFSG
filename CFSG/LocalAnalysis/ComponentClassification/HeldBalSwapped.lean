module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixCore
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.OddStandard.Glue
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalSwappedLayer
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalSwappedTransport

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.UnbalancedLayer

open scoped commutatorElement

theorem isComponent_conjugate_swap {Q : Type*} [Group Q] [Finite Q] {M : Subgroup Q} {α : Q}
    (hα : α * α = 1) (hM : IsComponent M) (hne : conjugate M α ≠ M) :
    IsComponent (conjugate M α) ∧ (∀ x ∈ M, ∀ y ∈ conjugate M α, x * y = y * x) ∧
      (∀ x ∈ M, α * x * α⁻¹ ∈ conjugate M α) ∧ (∀ y ∈ conjugate M α, α * y * α⁻¹ ∈ M) := by
  have hN : IsComponent (conjugate M α) :=
    LocalCores.isComponent_map_mulEquiv (MulAut.conj α⁻¹) hM
  refine ⟨hN, ?_, ?_, ?_⟩
  · intro x hx y hy
    rcases LocalCores.distinct_components_commute hM hN with h | h
    · exact absurd h.symm hne
    · have hm : ⁅x, y⁆ ∈ ⁅M, conjugate M α⁆ := commutator_mem_commutator hx hy
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
  · intro x hx
    rw [mem_conjugate_iff]
    have e : α * (α * x * α⁻¹) * α⁻¹ = x := by
      rw [show α * (α * x * α⁻¹) * α⁻¹ = (α * α) * x * (α * α)⁻¹ by group, hα]
      simp
    rwa [e]
  · intro y hy
    exact mem_conjugate_iff.mp hy

theorem heldKSwapped_of_centralStep (h : HeldKDiagonalCentralStep) : HeldKSwapped := by
  intro X _ _ L hset hbal u hu a ha ha2 haC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup X := centralizer ({u} : Set X) with hD
  set a' : ↥D := ⟨a, ha⟩ with ha'
  set K : Subgroup X := gsFixedLayer L u with hK
  intro M hM hne hKM hKp
  have hstd : IsStandardSubgroup L := hset.2.2.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha'a' : a' * a' = 1 := Subtype.ext haa
  have hKLD : K ≤ L ⊓ D := gsFixedLayer_le_inf L u
  have hKL : K ≤ L := hKLD.trans inf_le_left
  have hKD : K ≤ D := hKLD.trans inf_le_right
  have hLa : L ≤ centralizer ({a} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haC x hx)
  have hev : 2 ∣ Nat.card L := by
    have h1 : orderOf (⟨u, hu.1⟩ : L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu.2.1
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) :=
    (OddStandard.isPComponent_two_of_standard
      (isStandardSubgroup_iff_standardComponentIsStandard.1 hstd) haC ha2 hev).2
  have hDcore : pPrimeCore 2 ↥D = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
    exact hbal u hu.2.1
  have hMc : IsComponent M := HeldFix.isComponent_of_isPComponent hDcore hM
  obtain ⟨hNc, hMN, hαM, hαN⟩ := isComponent_conjugate_swap ha'a' hMc hne
  set N : Subgroup ↥D := conjugate M a' with hN
  have hKD' : K.subgroupOf D ≤ centralizer ({a'} : Set ↥D) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxK : (x : X) ∈ K := hx
    have hxL : (x : X) ∈ L := hKL hxK
    have hc : (x : X) * a = a * (x : X) := mem_centralizer_singleton_iff.mp (hLa hxL)
    simpa using hc
  have hK0 : K.subgroupOf D ≠ ⊥ := by
    intro hbot
    have h1 : K = ⊥ := by
      have hmap := congrArg (Subgroup.map D.subtype) hbot
      rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, inf_of_le_left hKD] at hmap
    rw [hK] at h1
    exact hu.2.2 h1
  have hfixD : gsFixedLayer (M ⊔ N) a' = K.subgroupOf D :=
    gsFixedLayer_eq_of_isPComponent_swapped ha'a' hMN hαM hαN hMc.1 hK0 (le_inf hKM hKD') hKp
  have hfix : gsFixedLayer (M.map D.subtype ⊔ conjugate (M.map D.subtype) a) a = K := by
    have h1 := conjugate_map_subtype D M a'
    have e : N.map D.subtype = conjugate (M.map D.subtype) a := by
      simpa using h1.symm
    have h2 := gsFixedLayer_map_subtype D ha M N hKD hfixD
    rwa [e] at h2
  have hM' : IsPComponent 2 ((M.map D.subtype).subgroupOf D) := by
    have h1 : (M.map D.subtype).subgroupOf D = M :=
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective M
    rwa [h1]
  have hne' : conjugate (M.map D.subtype) a ≠ M.map D.subtype := by
    intro h1
    apply hne
    apply Subgroup.map_injective D.subtype_injective
    have h2 := conjugate_map_subtype D M a'
    rw [← h2]
    simpa using h1
  have hcentral : ∀ x ∈ (pPrimeCore 2 ↥(M.map D.subtype)).map (M.map D.subtype).subtype,
      ∀ m ∈ M.map D.subtype, x * m = m * x := by
    have hbot : pPrimeCore 2 ↥M = ⊥ := HeldFix.pPrimeCore_eq_bot_of_isPComponent hDcore hM
    have hbot' : pPrimeCore 2 ↥(M.map D.subtype) = ⊥ := pPrimeCore_map_subtype_eq_bot D M hbot
    intro x hx m hm
    rw [hbot'] at hx
    rw [Subgroup.map_bot, Subgroup.mem_bot] at hx
    rw [hx]
    simp
  exact h X L hset a u (M.map D.subtype) ha2 hLa hLc hu (map_subtype_le M) hM' hne' hfix hcentral

end CFSG.ComponentClassification.GrSLit
