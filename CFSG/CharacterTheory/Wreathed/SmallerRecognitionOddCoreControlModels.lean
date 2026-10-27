module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenter

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOddCoreControl

open Matrix CFSG.Assembly.LowTwoRank DegreeThreeModelFullCenter
open CFSG.ComponentClassification CatalogueBUnitaryTwo CatalogueBUnitaryIsometry
open OddUnitaryThreeCentralizerCore

theorem oddCore_central_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hc : CFSG.oddCore H ≤ Subgroup.center H) : CFSG.oddCore G ≤ Subgroup.center G := by
  apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  have he : (CFSG.oddCore G).map e.toMonoidHom = CFSG.oddCore H :=
    OddCore.equiv_invariant e
  have hec : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
    Subgroup.map_center_eq e
  rw [he, hec]
  exact hc

theorem stated_linear_three_centralizer_oddCore_central
    (G : Type) [Group G] (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel G .PSL 3 p f) (t : G) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.center (Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨_, F, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  let e := eModel.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
  have hFodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have hq : 3 ≤ Nat.card F := by
    rw [hcard]
    exact (hp.odd_iff.mp hpodd).trans (Nat.le_self_pow (by omega) p)
  let D := Subgroup.center (OddLinearThreeCentralizerCore.SL3 F)
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ :=
    OddLinearThreeCentralizerCore.unique_involution_lift F D le_rfl (e t) ht'
  have hc := OddLinearThreeCentralizerCore.targetQuotientCentralizer_core_structure
    F hFodd hq D le_rfl z hz (e t) hzt
  exact oddCore_central_of_equiv (originalCentralizerEquiv e t) hc.2.1

theorem stated_unitary_three_centralizer_oddCore_central
    (G : Type) [Group G] (p f : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hmodel : StatedClassicalModel G .PSU 3 p f) (t : G) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.center (Subgroup.centralizer ({t} : Set G)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, E, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  let h := originalIdentityForm p f hcard
  let : Finite (isometryGroup h) := isometryGroup_finite h
  let D := scalarCenter h (Module.finrank_fin_fun E)
  let : D.Normal := scalar_subgroup_normal h (Module.finrank_fin_fun E) D le_rfl
  let e := eModel.trans (originalIdentityProjectiveEquiv p f hcard).symm
  have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ :=
    unique_involution_lift h (Module.finrank_fin_fun E) D le_rfl (e t) ht'
  have hc := unitaryTargetQuotientCentralizer_core_structure p f hpodd hcard h
    (originalIdentityForm_isSymm p f hcard) (originalIdentityForm_nondegenerate p f hcard)
    (Module.finrank_fin_fun E) D le_rfl z hz (e t) hzt
  exact oddCore_central_of_equiv (originalCentralizerEquiv e t) hc.2.1

end CFSG.Wreathed.SmallerRecognitionOddCoreControl
