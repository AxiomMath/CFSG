module

public import CFSG.GH74.Uniqueness.SU.SU13TB0Orbit
public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.GH74.Uniqueness.SU.SU13TB1Core
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G]

theorem conj_mem_oc_of_mem_normalizer [Finite G] {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) {x : G} (hx : x ∈ oc X) : g * x * g⁻¹ ∈ oc X := by
  have hle : (oc X).map (MulAut.conj g).toMonoidHom ≤ oc X := by
    refine le_oc_of_normal_odd ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have := (mem_normalizer_iff.mp hg y).mp (oc_le X hy)
      simpa using this
    · rintro h hh _ ⟨y, hy, rfl⟩
      have hg' : g⁻¹ ∈ normalizer (X : Set G) := inv_mem hg
      have h1 : g⁻¹ * h * g ∈ X := by
        have := (mem_normalizer_iff.mp hg' h).mp hh
        simpa using this
      have h2 := conj_mem_oc h1 hy
      refine ⟨g⁻¹ * h * g * y * (g⁻¹ * h * g)⁻¹, h2, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact odd_card_oc X
  exact hle ⟨x, hx, by simp⟩

theorem isTwoAlt_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n : ℕ} (e : X ≃* Y)
    (h : K.IsTwoAlt X n) : K.IsTwoAlt Y n := by
  obtain ⟨hq, hfin, hc, ⟨φ⟩⟩ := h
  have := hfin
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, Finite.of_equiv X e.toEquiv, ?_, ?_⟩
  · have hmap : (center X).map (e : X →* Y) = center Y := Subgroup.map_center_eq e
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
    exact hc
  · have hmap : (center Y).map (e.symm : Y →* X) = center X := Subgroup.map_center_eq e.symm
    exact ⟨(QuotientGroup.congr (center Y) (center X) e.symm hmap).trans φ⟩

theorem isTwoAlt_centralizer_conj {z k : G} {n : ℕ} (h : K.IsTwoAlt ↥(centralizer ({z} : Set G)) n) :
    K.IsTwoAlt ↥(centralizer ({k * z * k⁻¹} : Set G)) n := by
  have heq : (centralizer ({z} : Set G)).map (MulAut.conj k).toMonoidHom =
      centralizer ({k * z * k⁻¹} : Set G) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := mem_centralizer_singleton_iff.mp hy
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      calc k * y * k⁻¹ * (k * z * k⁻¹) = k * (y * z) * k⁻¹ := by group
        _ = k * (z * y) * k⁻¹ := by rw [hy']
        _ = k * z * k⁻¹ * (k * y * k⁻¹) := by group
    · intro hx
      refine ⟨k⁻¹ * x * k, mem_centralizer_singleton_iff.mpr ?_,
        by simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]; group⟩
      calc k⁻¹ * x * k * z = k⁻¹ * (x * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * z * k⁻¹) * x) * k := by rw [hx]
        _ = z * (k⁻¹ * x * k) := by group
  exact isTwoAlt_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ _ (MulAut.conj k).injective).trans (MulEquiv.subgroupCongr heq)) h

end CFSG.GH74.Uniqueness.SU.SU13
