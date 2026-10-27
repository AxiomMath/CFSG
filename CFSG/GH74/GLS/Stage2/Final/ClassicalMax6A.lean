module

public import CFSG.GH74.GLS.Stage2.Final.Basic
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.LieType.CurtisTits.Conclusion
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem map_generalizedFitting_equiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : (generalizedFitting A).map e.toMonoidHom = generalizedFitting B :=
  CFSG.WholeGroup.generalizedFitting_map_mulEquiv e

theorem lieModel_generalizedFitting_of_equiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {p f : ℕ} (h : LieModel ↥(generalizedFitting A) .PSp 2 p f) :
    LieModel ↥(generalizedFitting B) .PSp 2 p f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((e.subgroupMap (generalizedFitting A)).trans
      (MulEquiv.subgroupCongr (map_generalizedFitting_equiv e))) h

section Conj

variable {G : Type} [Group G]

theorem mem_Cen_conj_iff (z g x : G) : x ∈ Cen (g * z * g⁻¹) ↔ g⁻¹ * x * g ∈ Cen z := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : g⁻¹ * (x * (g * z * g⁻¹)) * g = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := h1
      _ = z * (g⁻¹ * x * g) := by group
  · intro h
    have h1 : g * (g⁻¹ * x * g * z) * g⁻¹ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    calc x * (g * z * g⁻¹) = g * (g⁻¹ * x * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := h1
      _ = (g * z * g⁻¹) * x := by group

end Conj

theorem exists_conj_of_central {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hctx : Stage2Ctx G z k S) {z'' : G} (hz'' : IsCentralInvolution z'') :
    ∃ g : G, g * z * g⁻¹ = z'' := by
  obtain ⟨hord, S₂, hzS₂, hzc₂⟩ := hz''
  obtain ⟨P, hP⟩ := sylow_of_sylowTop hctx.sylow_top
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S₂
  have hS₂ : (S₂ : Subgroup G) = S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP]
    rfl
  rw [hS₂] at hzS₂
  obtain ⟨s, hs, hsz⟩ := hzS₂
  have hw : g⁻¹ * z'' * g = s := by
    rw [← hsz]
    show g⁻¹ * (g * s * g⁻¹) * g = s
    group
  have hwc : ∀ t ∈ S, t * s = s * t := by
    intro t ht
    have ht2 : g * t * g⁻¹ ∈ (S₂ : Subgroup G) := by
      rw [hS₂]; exact ⟨t, ht, rfl⟩
    have h1 : (g * t * g⁻¹) * (g * s * g⁻¹) = (g * s * g⁻¹) * (g * t * g⁻¹) := by
      have := hzc₂ _ ht2
      rw [← hsz] at this
      exact this
    have h2 : g⁻¹ * ((g * t * g⁻¹) * (g * s * g⁻¹)) * g = g⁻¹ * ((g * s * g⁻¹) * (g * t * g⁻¹)) * g := by
      rw [h1]
    calc t * s = g⁻¹ * ((g * t * g⁻¹) * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * (g * t * g⁻¹)) * g := h2
      _ = s * t := by group
  have hos : orderOf s = 2 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z''
    rw [MulAut.conj_apply] at h1
    simp only [inv_inv] at h1
    rw [← hw, h1]
    exact hord
  have := hctx.data.base.zcen s hs hwc hos
  refine ⟨g, ?_⟩
  rw [this] at hw
  rw [← hw]
  group

theorem max6A_of_sixA {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind} {p f : ℕ}
    (hctx : Stage2Ctx G z k S)
    (h6 : ∀ M : Subgroup G, IsCoatom M → Cen z < M →
      IsCoatom ((Cen z).subgroupOf M) ∧ LieModel ↥(generalizedFitting ↥M) .PSp 2 p f) :
    Max6A G p f := by
  intro z'' hz'' M hM hlt
  obtain ⟨g, hgz⟩ := exists_conj_of_central hctx hz''
  subst hgz
  let c : G ≃* G := MulAut.conj g⁻¹
  let M₀ : Subgroup G := M.map c.toMonoidHom
  have hM₀ : IsCoatom M₀ := (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup c) M).2 hM
  have hCen : (Cen (g * z * g⁻¹)).map c.toMonoidHom = Cen z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := (mem_Cen_conj_iff z g y).1 hy
      show g⁻¹ * y * g⁻¹⁻¹ ∈ Cen z
      rw [inv_inv]
      exact this
    · intro hx
      have h : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      refine ⟨g * x * g⁻¹, (mem_Cen_conj_iff z g _).2 (by rw [h]; exact hx), ?_⟩
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
  have hlt₀ : Cen z < M₀ := by
    rw [← hCen]
    exact (OrderIso.lt_iff_lt (MulEquiv.mapSubgroup c)).2 hlt
  obtain ⟨hcoat, hlie⟩ := h6 M₀ hM₀ hlt₀
  let φ : ↥M ≃* ↥M₀ := M.equivMapOfInjective c.toMonoidHom c.injective
  refine ⟨?_, lieModel_generalizedFitting_of_equiv φ.symm hlie⟩
  have himg : (MulEquiv.mapSubgroup φ) ((Cen (g * z * g⁻¹)).subgroupOf M) = (Cen z).subgroupOf M₀ := by
    ext y
    rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv]
    show ((φ.symm y : ↥M) : G) ∈ Cen (g * z * g⁻¹) ↔ (y : G) ∈ Cen z
    have hy : ((φ.symm y : ↥M) : G) = g * (y : G) * g⁻¹ := by
      have := congrArg Subtype.val (φ.apply_symm_apply y)
      have h2 : (c ((φ.symm y : ↥M) : G)) = (y : G) := this
      have h3 : g⁻¹ * ((φ.symm y : ↥M) : G) * g⁻¹⁻¹ = (y : G) := h2
      calc ((φ.symm y : ↥M) : G) = g * (g⁻¹ * ((φ.symm y : ↥M) : G) * g⁻¹⁻¹) * g⁻¹ := by group
        _ = g * (y : G) * g⁻¹ := by rw [h3]
    rw [hy, mem_Cen_conj_iff z g]
    have h : g⁻¹ * (g * (y : G) * g⁻¹) * g = (y : G) := by group
    rw [h]
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ) _).1 (by rw [himg]; exact hcoat)

end CFSG.GH74.GLS.Stage2.Final
