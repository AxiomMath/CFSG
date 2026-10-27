module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.ABGLocalTools Subgroup
open scoped Pointwise

private theorem map_conj_centralizer_singleton_aux {G : Type*} [Group G] (x g : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set G) := by
  ext z
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by group⟩
    calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * z) * g := by rw [hz]
      _ = x * (g⁻¹ * z * g) := by group

private theorem isSylowOf_map_conj_aux {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (h : IsSylowOf p P K) (g : G) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine isSylowOf_of_card (Subgroup.map_mono h.le) ?_
  rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj]
  exact h.card_eq

private theorem exists_mem_conj_of_isSylowOf_aux {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P P' K : Subgroup G} (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, ∀ z : G, z ∈ P' ↔ k⁻¹ * z * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun z => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨w, hw, hwz⟩
    have hwz' : (w : G) = (g : G)⁻¹ * z * g := hwz
    have hz : z = (g : G) * w * (g : G)⁻¹ := by rw [hwz']; group
    have hzK : z ∈ K := by
      rw [hz]
      exact K.mul_mem (K.mul_mem g.2 w.2) (K.inv_mem g.2)
    refine ⟨⟨z, hzK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨z, hzK⟩ * g = w := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hwz'.symm)
    rw [this]
    exact hw

theorem exists_mem_normalizer_conj_eq {G : Type*} [Group G] [Finite G] {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (_hx : x ∈ T)
    (hab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {g : G} (hg : g * x * g⁻¹ ∈ T) :
    ∃ n ∈ normalizer (T : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  have hTy : T ≤ centralizer ({g * x * g⁻¹} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hab t ht _ hg)
  have hC := map_conj_centralizer_singleton_aux x g
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hT1 : IsSylowOf 2 (T.map (MulAut.conj g).toMonoidHom)
      (centralizer ({g * x * g⁻¹} : Set G)) := by
    rw [← hC]
    exact isSylowOf_map_conj_aux hT g
  have hT2 : IsSylowOf 2 T (centralizer ({g * x * g⁻¹} : Set G)) := by
    refine isSylowOf_of_card hTy ?_
    rw [hT.card_eq, ← hC, Subgroup.card_map_of_injective hinj]
  obtain ⟨k, hk, hkT⟩ := exists_mem_conj_of_isSylowOf_aux hT1 hT2
  refine ⟨k * g, ?_, ?_⟩
  · rw [mem_set_normalizer_iff'']
    intro z
    have h1 := hkT z
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h1
    have e : (k * g)⁻¹ * z * (k * g) = g⁻¹ * (k⁻¹ * z * k) * g := by group
    rw [SetLike.mem_coe, SetLike.mem_coe, e]
    exact h1
  · have hky : k * (g * x * g⁻¹) = g * x * g⁻¹ * k := mem_centralizer_singleton_iff.mp hk
    calc k * g * x * (k * g)⁻¹ = k * (g * x * g⁻¹) * k⁻¹ := by group
      _ = g * x * g⁻¹ * k * k⁻¹ := by rw [hky]
      _ = g * x * g⁻¹ := by group

theorem isSylowOf_top_of_isolated {G : Type*} [Group G] [Finite G] {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hx : x ∈ T)
    (hiso : ∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ = x) : IsSylowOf 2 T ⊤ := by
  obtain ⟨S, hTS⟩ := hT.isPGroup.exists_le_sylow
  have hS : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hTeq : T = (S : Subgroup G) := by
    by_contra hne
    have hlt : T < (S : Subgroup G) := lt_of_le_of_ne hTS hne
    have : Group.IsNilpotent (S : Subgroup G) := IsPGroup.isNilpotent hS
    have hne' : T.subgroupOf (S : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact not_le_of_gt hlt
    obtain ⟨s, hsN, hsT⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hne')
    have hxS : x ∈ (S : Subgroup G) := hTS hx
    have hs1 : (s : G) * x * (s : G)⁻¹ ∈ T :=
      Subgroup.mem_subgroupOf.mp
        ((mem_normalizer_iff.mp hsN ⟨x, hxS⟩).mp (Subgroup.mem_subgroupOf.mpr hx))
    have hsC : (s : G) ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hiso _ hs1))
    have hQS : T ⊔ zpowers (s : G) ≤ (S : Subgroup G) := sup_le hTS (zpowers_le.mpr s.2)
    have hQC : T ⊔ zpowers (s : G) ≤ centralizer ({x} : Set G) :=
      sup_le hT.le (zpowers_le.mpr hsC)
    have hQ : T ⊔ zpowers (s : G) = T := hT.eq_of_le le_sup_left hQC (hS.to_le hQS)
    have hsmem : (s : G) ∈ T ⊔ zpowers (s : G) := mem_sup_right (mem_zpowers _)
    rw [hQ] at hsmem
    exact hsT (Subgroup.mem_subgroupOf.mpr hsmem)
  rw [hTeq]
  refine isSylowOf_iff.mpr ⟨le_top, hS, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact S.not_dvd_index

end CFSG.GH74.Generic
