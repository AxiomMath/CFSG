module

import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.exists_involution_aut_component (h : GomiU42Data X J D E a) :
    ∃ α : MulAut D, α ^ 2 = 1 ∧ α ≠ 1 ∧
      Nat.card ↥(α.toMonoidHom.eqLocus (MonoidHom.id D)) ∣ 51840 ∧
      ∃ L : Subgroup ↥(α.toMonoidHom.eqLocus (MonoidHom.id D)),
        CFSG.IsComponent L ∧ Nat.card L = 25920 := by
  haveI := h.normal
  haveI := h.isSimpleGroup_J
  have hord := h.fixedRoot_conjNormal.1
  have hJle := h.fixedRoot_conjNormal.2.1
  have hJn := h.fixedRoot_conjNormal.2.2.1
  refine ⟨MulAut.conjNormal a, ?_, ?_, ?_, ?_⟩
  · rw [← hord]
    exact pow_orderOf_eq_one _
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  ·
    have hfix : ∀ x : D, x ∈ (MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus
        (MonoidHom.id D) ↔ (x : X) ∈ centralizer ({a} : Set X) := by
      intro x
      change MulAut.conjNormal a x = x ↔ _
      rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, MulAut.conjNormal_apply]
      constructor
      · intro hx
        calc (x : X) * a = (a * x * a⁻¹) * a := by rw [hx]
          _ = a * x := by group
      · intro hx
        calc a * (x : X) * a⁻¹ = ((x : X) * a) * a⁻¹ := by rw [hx]
          _ = x := by group
    have hle : ((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D)).map
        D.subtype ≤ centralizer ({a} : Set X) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hfix x).1 hx
    have hcard : Nat.card ↥(((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus
        (MonoidHom.id D)).map D.subtype) =
        Nat.card ↥((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D)) :=
      Subgroup.card_map_of_injective D.subtype_injective
    rw [← hcard]
    exact (Subgroup.card_dvd_of_le hle).trans (by rw [h.card_centralizer])
  ·
    refine ⟨(J.subgroupOf D).subgroupOf
      ((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D)), ⟨?_, ?_⟩, ?_⟩
    · have e : ↥((J.subgroupOf D).subgroupOf
          ((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D))) ≃* J :=
        (Subgroup.subgroupOfEquivOfLe hJle).trans (Subgroup.subgroupOfEquivOfLe h.lt.le)
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian_J).1
    · exact hJn.isSubnormal
    · have e : ↥((J.subgroupOf D).subgroupOf
          ((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D))) ≃* J :=
        (Subgroup.subgroupOfEquivOfLe hJle).trans (Subgroup.subgroupOfEquivOfLe h.lt.le)
      rw [Nat.card_congr e.toEquiv]
      exact h.card_J

theorem gomi_exists_component_congr {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (α : MulAut A)
    (L : Subgroup ↥(α.toMonoidHom.eqLocus (MonoidHom.id A))) (hL : CFSG.IsComponent L) :
    ∃ L' : Subgroup ↥((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)),
      CFSG.IsComponent L' ∧ Nat.card L' = Nat.card L := by
  let Ψ : ↥(α.toMonoidHom.eqLocus (MonoidHom.id A)) ≃*
      ↥((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)) :=
    ((α.toMonoidHom.eqLocus (MonoidHom.id A)).equivMapOfInjective φ.toMonoidHom
      φ.injective).trans
      (MulEquiv.subgroupCongr (CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr φ α))
  exact ⟨L.map Ψ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv Ψ hL,
    Subgroup.card_map_of_injective Ψ.injective⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
