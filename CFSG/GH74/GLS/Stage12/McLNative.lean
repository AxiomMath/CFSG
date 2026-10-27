module

public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.Sporadic.SmallOddCore.McLWordBound
public import CFSG.RankThree.Native.HSMcLSmall

public section

namespace CFSG.GH74.GLS.Stage12.McLRec

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.RankThree.Native

theorem card_centralizer_subtype {G : Type*} [Group G] (P : Subgroup G) (x : P) :
    Nat.card (centralizer ({x} : Set P)) = Nat.card ↥(P ⊓ centralizer ({(x : G)} : Set G)) := by
  have h : (centralizer ({x} : Set P)).map P.subtype = P ⊓ centralizer ({(x : G)} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hgP, hg⟩
      exact ⟨⟨g, hgP⟩, Subtype.ext (by simpa using hg), rfl⟩
  rw [← h]
  exact (Subgroup.card_map_of_injective P.subtype_injective).symm

theorem card_centralizer_equiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) (a : H) :
    Nat.card (centralizer ({e a} : Set K)) = Nat.card (centralizer ({a} : Set H)) := by
  have h : (centralizer ({a} : Set H)).map e.toMonoidHom = centralizer ({e a} : Set K) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  rw [← h]
  exact Subgroup.card_map_of_injective e.injective

theorem mclP_isConj
    {t u : mclP} (ht : orderOf t = 2) (hu : orderOf u = 2) : IsConj t u := by
  obtain ⟨g, hg⟩ := mcl_involution_conj_a ht
  obtain ⟨h, hh⟩ := mcl_involution_conj_a hu
  refine isConj_iff.mpr ⟨h * g⁻¹, ?_⟩
  rw [hg, hh]
  group

theorem mclP_card_centralizer_a0 :
    Nat.card (centralizer ({mcla0} : Set mclP)) = 40320 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := mcl_involution_centralizers
  have hr0 : (mclRows[0]'(by simp [mclRows])) ∈ mclRows := List.getElem_mem _
  obtain ⟨-, h2, h3, -, h5, -⟩ := hrows _ hr0
  have hout : (mclRows[0]'(by simp [mclRows])).outer = false := rfl
  have hcent : (mclRows[0]'(by simp [mclRows])).centOrder = 40320 := rfl
  have hrP : tp 275 (mclRows[0]'(by simp [mclRows])).rep ∈ mclP := by
    by_contra h
    have := h3.mpr h
    rw [hout] at this
    exact absurd this (by decide)
  obtain ⟨g, hg⟩ := mcl_involution_conj_a
    (t := ⟨tp 275 (mclRows[0]'(by simp [mclRows])).rep, hrP⟩)
    (by rw [Subgroup.orderOf_mk]; exact h2)
  have hconj : (⟨tp 275 (mclRows[0]'(by simp [mclRows])).rep, hrP⟩ : mclP) * 1 = g * mcla0 * g⁻¹ := by
    rw [mul_one]; exact hg
  have ha : mcla0 = g⁻¹ * (⟨tp 275 (mclRows[0]'(by simp [mclRows])).rep, hrP⟩ : mclP) * g⁻¹⁻¹ := by
    rw [hg]; group
  rw [ha, card_centralizer_conj, card_centralizer_subtype]
  rw [h5, hcent]

theorem mclP_card_centralizer
    {t : mclP} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set mclP)) = 40320 := by
  obtain ⟨g, hg⟩ := mcl_involution_conj_a ht
  rw [hg, card_centralizer_conj, mclP_card_centralizer_a0]

noncomputable def mclEquivP :
    Blueprint.NativeSporadic.McL ≃* mclP :=
  mcl275Equiv.trans (MulEquiv.subgroupCongr mcl275P_eq)

theorem isConj_of_equiv_mclP
    {K : Type*} [Group K] (e : K ≃* mclP) {u v : K} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : IsConj u v := by
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hv' : orderOf (e v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨c, hc⟩ := isConj_iff.mp (mclP_isConj hu' hv')
  refine isConj_iff.mpr ⟨e.symm c, ?_⟩
  apply e.injective
  simp [hc]

theorem card_centralizer_of_equiv_mclP
    {K : Type*} [Group K] (e : K ≃* mclP) {u : K}
    (hu : orderOf u = 2) : Nat.card (centralizer ({u} : Set K)) = 40320 := by
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have h1 := card_centralizer_equiv e u
  have h2 := mclP_card_centralizer hu'
  exact h1.symm.trans h2

theorem card_of_equiv_mclP
    {K : Type*} [Group K] (e : K ≃* mclP) : Nat.card K = 898128000 := by
  rw [Nat.card_congr e.toEquiv]
  exact card_mclP

end CFSG.GH74.GLS.Stage12.McLRec
