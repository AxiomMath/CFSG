module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Chevalley
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L128

open Subgroup CFSG CFSG.Blueprint

abbrev GrpEquiv (F F' : Type*) [Group F] [Group F'] : Type _ := F ≃* F'

theorem map_centralizer_singleton {A B : Type*} [Group A] [Group B] (e : A ≃* B) (w : A) :
    (centralizer ({w} : Set A)).map e.toMonoidHom = centralizer ({e w} : Set B) := by
  ext y
  simp only [Subgroup.mem_map, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    simpa using hy

theorem centralizer_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (w : A) :
    Nonempty (↥(centralizer ({w} : Set A)) ≃* ↥(centralizer ({e w} : Set B))) :=
  ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton e w))⟩

theorem centralizer_equiv_of_all_conj {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (z₀ : Y)
    (K : Subgroup Y) (hK : centralizer ({z₀} : Set Y) = K)
    (hall : ∀ u : Y, orderOf u = 2 → ∃ c : Y, u = c * z₀ * c⁻¹) {w : X} (hw : orderOf w = 2) :
    Nonempty (↥(centralizer ({w} : Set X)) ≃* ↥K) := by
  have hw' : orderOf (e w) = 2 := by rw [MulEquiv.orderOf_eq]; exact hw
  obtain ⟨c, hc⟩ := hall (e w) hw'
  obtain ⟨e1⟩ := centralizer_equiv e w
  obtain ⟨e2⟩ := centralizer_equiv (MulAut.conj c) z₀
  have hcc : (MulAut.conj c) z₀ = e w := by
    rw [hc]
    exact MulAut.conj_apply c z₀
  have e3 : ↥(centralizer ({(MulAut.conj c) z₀} : Set Y)) ≃* ↥(centralizer ({e w} : Set Y)) :=
    MulEquiv.subgroupCongr (by rw [hcc])
  have e4 : ↥(centralizer ({z₀} : Set Y)) ≃* ↥K := MulEquiv.subgroupCongr hK
  exact ⟨e1.trans (e3.symm.trans (e2.symm.trans e4))⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L128
