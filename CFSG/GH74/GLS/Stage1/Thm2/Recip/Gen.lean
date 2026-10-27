module

import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Core
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Elt

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_of_barMk_mem {J : Subgroup Y} (hJ : TwoComponents.IsTwoComponent J) {v : Y}
    (hv : ∃ n : ℕ, v ^ (2 ^ n) = 1) (h : TwoThin.barMk Y v ∈ J.map (TwoThin.barMk Y)) : v ∈ J := by
  have hres := TwoComponentSubnormal.ambient_residual_preimage (TwoThin.barMk Y)
    TwoThin.barMk_surjective TwoThin.odd_card_ker_barMk J hJ
  set M := (J.map (TwoThin.barMk Y)).comap (TwoThin.barMk Y) with hM
  have hvM : v ∈ M := h
  let v' : ↥M := ⟨v, hvM⟩
  obtain ⟨n, hn⟩ := hv
  have hpg : IsPGroup 2 ↥(zpowers v') := by
    have : v' ^ (2 ^ n) = 1 := Subtype.ext hn
    exact isPGroup_zpowers_of_pow_eq_one this
  have hv' : v' ∈ TwoResidual.subgroup ↥M :=
    TwoResidual.twoSubgroup_le (zpowers v') hpg (mem_zpowers v')
  rw [← hres]
  exact ⟨v', hv', rfl⟩

end Elt

section Conj

variable {G : Type} [Group G]

theorem conjSub_map_eq {Y : Type} [Group Y] {M : Subgroup Y} {q : Y}
    (hq : q ∈ normalizer (M : Set Y)) :
    conjSub (TwoThin.barMk Y q)⁻¹ (M.map (TwoThin.barMk Y)) = M.map (TwoThin.barMk Y) := by
  have h : conjSub (TwoThin.barMk Y q)⁻¹ (M.map (TwoThin.barMk Y)) =
      (conjSub q⁻¹ M).map (TwoThin.barMk Y) := by
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [h]
  congr 1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hq)

theorem map_centralizer_singleton_conj (t g : G) :
    (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * t * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ centralizer ({t} : Set G) := hw
    rw [mem_centralizer_singleton_iff] at hw'
    rw [mem_centralizer_singleton_iff]
    have h1 : (MulAut.conj g).toMonoidHom w = g * w * g⁻¹ := by simp [MulAut.conj_apply]
    rw [h1]
    calc g * w * g⁻¹ * (g * t * g⁻¹) = g * (w * t) * g⁻¹ := by group
      _ = g * (t * w) * g⁻¹ := by rw [hw']
      _ = g * t * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hz
    rw [mem_centralizer_singleton_iff] at hz
    refine ⟨g⁻¹ * z * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    show g⁻¹ * z * g ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * z) * g := by rw [hz]
      _ = t * (g⁻¹ * z * g) := by group

theorem isPCompIn_map_conj [Finite G] {X K : Subgroup G} (h : IsPCompIn 2 X K) (g : G) :
    IsPCompIn 2 (X.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  refine TwoThin.isPCompIn_two_iff.mpr ⟨Subgroup.map_mono h.1, ?_⟩
  let c : G ≃* G := MulAut.conj g
  let e : ↥X ≃* ↥(X.map c.toMonoidHom) := MulEquiv.subgroupMap c X
  have hmap : (K.subgroupOf X).map e.toMonoidHom =
      (K.map c.toMonoidHom).subgroupOf (X.map c.toMonoidHom) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
      have hkX : k ∈ X := h.1 hk
      refine ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
  rw [← hmap]
  exact (TwoComponentTransport.equiv_iff e _).mpr (TwoThin.isPCompIn_two_iff.mp h).2

theorem pRank_eq_of_mulEquiv' {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : pRank 2 A = pRank 2 B := CFSG.pRank_congr_of_mulEquiv e 2

theorem isIntrinsic_map_conj [Finite G] {t : G} {K : Subgroup G} (h : IsIntrinsic t K) (g : G) :
    IsIntrinsic (g * t * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_, ⟨t, h.2.2, by simp [MulAut.conj_apply]⟩⟩
  · have := isPCompIn_map_conj h.1 g
    rwa [map_centralizer_singleton_conj] at this
  · rw [← h.2.1]
    exact (pRank_eq_of_mulEquiv' (MulEquiv.subgroupMap (MulAut.conj g : G ≃* G) K)).symm

end Conj

section Comp

theorem eq_or_eq_of_isComponent_le_sup {H : Type*} [Group H] [Finite H] {K A B : Subgroup H}
    (hK : IsComponent K) (hA : IsComponent A) (hB : IsComponent B) (hle : K ≤ A ⊔ B) :
    K = A ∨ K = B := by
  by_contra hne
  push Not at hne
  have hcA : ⁅K, A⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hA).resolve_left hne.1
  have hcB : ⁅K, B⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hB).resolve_left hne.2
  have hTc : A ⊔ B ≤ centralizer (K : Set H) :=
    sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcA))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcB))
  exact not_le_centralizer_self_of_isQuasisimple (assembly_isQuasisimple_of_isComponent hK)
    (hle.trans hTc)

end Comp

end CFSG.GH74.GLS.Stage1.Thm2.Recip
