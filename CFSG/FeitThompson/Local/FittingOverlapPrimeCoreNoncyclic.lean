module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem coe_eq_setOf_pow_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C] (H : Subgroup C) :
    (H : Set C) = {a : C | a ^ Nat.card H = 1} := by
  classical
  have _ : Fintype C := Fintype.ofFinite C
  have hsub : (H : Set C) ⊆ {a : C | a ^ Nat.card H = 1} := fun a ha =>
    orderOf_dvd_iff_pow_eq_one.1 (H.orderOf_dvd_natCard ha)
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  have h1 : ({a : C | a ^ Nat.card H = 1}).ncard
      = (Finset.univ.filter fun a : C => a ^ Nat.card H = 1).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp
  have h2 : (H : Set C).ncard = Nat.card H := (Nat.card_coe_set_eq _).symm
  rw [h1, h2]
  exact IsCyclic.card_pow_eq_one_le Nat.card_pos

theorem eq_of_natCard_eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H K : Subgroup C} (h : Nat.card H = Nat.card K) : H = K :=
  SetLike.coe_injective (by rw [coe_eq_setOf_pow_eq_one H, coe_eq_setOf_pow_eq_one K, h])

theorem natCard_subgroupOf_of_le' {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  rw [← Subgroup.card_map_of_injective (f := K.subtype) K.subtype_injective
    (K := H.subgroupOf K), Subgroup.map_subgroupOf_eq_of_le h]

theorem eq_of_le_of_natCard_eq_of_isCyclic {A : Subgroup G} [Finite A] [IsCyclic A]
    {H₁ H₂ : Subgroup G} (h1 : H₁ ≤ A) (h2 : H₂ ≤ A) (h : Nat.card H₁ = Nat.card H₂) :
    H₁ = H₂ := by
  rw [← Subgroup.map_subgroupOf_eq_of_le h1, ← Subgroup.map_subgroupOf_eq_of_le h2]
  congr 1
  exact eq_of_natCard_eq_of_isCyclic
    (by rw [natCard_subgroupOf_of_le' h1, natCard_subgroupOf_of_le' h2, h])

theorem le_normalizer_of_le_of_isCyclic {A : Subgroup G} [Finite A] [IsCyclic A] {P : Subgroup G}
    (hPA : P ≤ A) {K : Subgroup G} (hK : K ≤ normalizer (A : Set G)) :
    K ≤ normalizer (P : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hA : A.map (MulAut.conj k) = A := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hK hk)
  exact eq_of_le_of_natCard_eq_of_isCyclic (A := A) (hA ▸ Subgroup.map_mono hPA) hPA
    (Subgroup.card_map_of_injective (MulAut.conj k).injective)

section Transport

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem map_piCore_le_of_mulEquiv (π : Set ℕ) (e : X ≃* Y) :
    (piCore π X).map (e : X →* Y) ≤ piCore π Y := by
  rw [Subgroup.map_le_iff_le_comap]
  refine piCore_le fun N hN hN' => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_piCore (hN.map _ e.surjective) (isPiSubgroup_iff.2 fun q hq => ?_)
  rw [Subgroup.card_map_of_injective e.injective] at hq
  exact isPiSubgroup_iff.1 hN' q hq

theorem map_piCore_of_mulEquiv (π : Set ℕ) (e : X ≃* Y) :
    (piCore π X).map (e : X →* Y) = piCore π Y := by
  refine le_antisymm (map_piCore_le_of_mulEquiv π e) ?_
  calc piCore π Y = ((piCore π Y).map (e.symm : Y →* X)).map (e : X →* Y) := by
        rw [Subgroup.map_map]; ext y; simp
    _ ≤ _ := Subgroup.map_mono (map_piCore_le_of_mulEquiv π e.symm)

theorem map_pCore_of_mulEquiv (p : ℕ) (e : X ≃* Y) :
    (pCore p X).map (e : X →* Y) = pCore p Y := by
  rw [pCore_eq_piCore, pCore_eq_piCore, map_piCore_of_mulEquiv]

theorem map_fittingRaw_le (e : X ≃* Y) : (fittingRaw X).map (e : X →* Y) ≤ fittingRaw Y := by
  rw [Subgroup.map_le_iff_le_comap]
  refine fittingRaw_le fun N hN hN' => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_fittingRaw (hN.map _ e.surjective) ?_
  obtain ⟨q, hq, n, hn⟩ := isPrimePowerOrder_iff.1 hN'
  exact isPrimePowerOrder_iff.2 ⟨q, hq, n, by rwa [Subgroup.card_map_of_injective e.injective]⟩

theorem map_fittingRaw_of_mulEquiv (e : X ≃* Y) :
    (fittingRaw X).map (e : X →* Y) = fittingRaw Y := by
  refine le_antisymm (map_fittingRaw_le e) ?_
  calc fittingRaw Y = ((fittingRaw Y).map (e.symm : Y →* X)).map (e : X →* Y) := by
        rw [Subgroup.map_map]; ext y; simp
    _ ≤ _ := Subgroup.map_mono (map_fittingRaw_le e.symm)

theorem le_pCore_of_isPGroup_of_le_fittingRaw {p : ℕ} (hp : p.Prime) {Q : Subgroup X}
    (hQ : IsPGroup p Q) (hQF : Q ≤ fittingRaw X) : Q ≤ pCore p X := by
  have := Fact.mk hp
  have hFn : (fittingRaw X).Normal := fittingRaw_normal X
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := fittingRaw X)).exists_le_sylow
  have : ((S : Subgroup (fittingRaw X))).Characteristic := S.characteristic_of_normal inferInstance
  have hnorm : ((S : Subgroup (fittingRaw X)).map (fittingRaw X).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (S : Subgroup (fittingRaw X)).map (fittingRaw X).subtype ≤ pCore p X :=
    le_pCore hp hnorm (S.isPGroup'.map _)
  refine le_trans ?_ hle
  calc Q = (Q.subgroupOf (fittingRaw X)).map (fittingRaw X).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQF).symm
    _ ≤ _ := Subgroup.map_mono hS

end Transport

variable [Finite G]

theorem le_map_pCore_of_isPGroup_of_le_map_fittingRaw {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQF : Q ≤ (fittingRaw M).map M.subtype) :
    Q ≤ (pCore p M).map M.subtype := by
  have hQM : Q ≤ M := hQF.trans (Subgroup.map_subtype_le _)
  have hcomap : Q.subgroupOf M ≤ fittingRaw M := by
    have h := Subgroup.comap_mono (f := M.subtype) hQF
    rwa [Subgroup.comap_map_eq_self_of_injective M.subtype_injective] at h
  have h := le_pCore_of_isPGroup_of_le_fittingRaw hp (hQ.comap_subtype (K := M)) hcomap
  calc Q = (Q.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hQM).symm
    _ ≤ _ := Subgroup.map_mono h

omit [Finite G] in
theorem map_map_subtype_comm (φ : G ≃* G) (M : Subgroup G) (K : Subgroup M) :
    (K.map M.subtype).map (φ : G →* G)
      = (K.map (φ.subgroupMap M : M →* M.map (φ : G →* G))).map (M.map (φ : G →* G)).subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_map_fittingRaw_comm (φ : G ≃* G) (M : Subgroup G) :
    ((fittingRaw M).map M.subtype).map (φ : G →* G)
      = (fittingRaw (M.map (φ : G →* G))).map (M.map (φ : G →* G)).subtype := by
  rw [map_map_subtype_comm, map_fittingRaw_of_mulEquiv]

theorem map_map_pCore_comm (φ : G ≃* G) (M : Subgroup G) (p : ℕ) :
    ((pCore p M).map M.subtype).map (φ : G →* G)
      = (pCore p (M.map (φ : G →* G))).map (M.map (φ : G →* G)).subtype := by
  rw [map_map_subtype_comm, map_pCore_of_mulEquiv]

theorem le_normalizer_map_pCore (M : Subgroup G) (p : ℕ) :
    M ≤ normalizer (((pCore p M).map M.subtype : Subgroup G) : Set G) := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).1 ?_
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact pCore_normal p M

theorem not_isCyclic_map_pCore_of_dvd_natCard_inf_fittingRaw_conj [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M) {p : ℕ}
    (hp : p.Prime)
    (hpX : p ∣ Nat.card ((fittingRaw M).map M.subtype ⊓
      ((fittingRaw M).map M.subtype).map (MulAut.conj g⁻¹ : G →* G) : Subgroup G)) :
    ¬ IsCyclic ((pCore p M).map M.subtype) := by
  have := Fact.mk hp
  intro hcyc
  set φ : G ≃* G := MulAut.conj g⁻¹ with hφ
  set F : Subgroup G := (fittingRaw M).map M.subtype with hF
  set Op : Subgroup G := (pCore p M).map M.subtype with hOp
  set N : Subgroup G := M.map (φ : G →* G) with hN
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := (F ⊓ F.map (φ : G →* G) : Subgroup G)) p hpX
  set P : Subgroup G := Subgroup.zpowers (x : G) with hP
  have hPcard : Nat.card P = p := by
    rw [hP, Nat.card_zpowers, ← hx, Subgroup.orderOf_coe]
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hxF : (x : G) ∈ F ⊓ F.map (φ : G →* G) := x.2
  have hPF : P ≤ F := Subgroup.zpowers_le.2 hxF.1
  have hPF' : P ≤ F.map (φ : G →* G) := Subgroup.zpowers_le.2 hxF.2
  have hPOp : P ≤ Op := le_map_pCore_of_isPGroup_of_le_map_fittingRaw hp hPp hPF
  have hPOp' : P ≤ (pCore p N).map N.subtype := by
    refine le_map_pCore_of_isPGroup_of_le_map_fittingRaw hp hPp ?_
    rwa [hN, ← map_map_fittingRaw_comm]
  have hOpN : (pCore p N).map N.subtype = Op.map (φ : G →* G) := by
    rw [hN, ← map_map_pCore_comm]
  have hcyc' : IsCyclic (Op.map (φ : G →* G)) := (MulEquiv.isCyclic (φ.subgroupMap Op)).1 hcyc
  have hMP : M ≤ normalizer (P : Set G) :=
    le_normalizer_of_le_of_isCyclic (A := Op) hPOp (le_normalizer_map_pCore M p)
  have hNP : N ≤ normalizer (P : Set G) := by
    refine le_normalizer_of_le_of_isCyclic (A := Op.map (φ : G →* G)) (hOpN ▸ hPOp') ?_
    rw [← hOpN, hN]
    exact le_normalizer_map_pCore N p
  have hlt : normalizer (P : Set G) < ⊤ := normalizer_lt_top_of_isPGroup hna hp hPne hPp
  have hNM : IsCoatom N := isCoatom_map_conj hM _
  have hMeq : M = normalizer (P : Set G) := by
    rcases eq_or_lt_of_le hMP with h | h
    · exact h
    · exact absurd (hM.2 _ h) hlt.ne
  have hNeq : N = normalizer (P : Set G) := by
    rcases eq_or_lt_of_le hNP with h | h
    · exact h
    · exact absurd (hNM.2 _ h) hlt.ne
  have hginv : g⁻¹ ∈ normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hNeq.trans hMeq.symm)
  rw [normalizer_coe_eq_of_isCoatom hna hM] at hginv
  exact hg (by simpa using M.inv_mem hginv)

theorem not_isCyclic_map_pCore_of_dvd_natCard_inf_fittingRaw_conj' (_hodd : Odd (Nat.card G))
    (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {M : Subgroup G} (hM : IsCoatom M)
    {g : G} (hg : g ∉ M) {p : ℕ} (hp : p.Prime)
    (hpX : p ∣ Nat.card ((fittingRaw M).map M.subtype ⊓
      ((fittingRaw M).map M.subtype).map (MulAut.conj g⁻¹ : G →* G) : Subgroup G)) :
    ¬ IsCyclic ((pCore p M).map M.subtype) :=
  have := hsimple
  not_isCyclic_map_pCore_of_dvd_natCard_inf_fittingRaw_conj hna hM hg hp hpX

end

end CFSG.FeitThompson
