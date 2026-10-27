module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.CentralQuotientComponentLift
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift

variable {p f : ℕ} {E : Type} [Field E] {h : UnitaryFieldData p f E}
  {A : Type*} [AddCommGroup A] [Module E A]

@[expose] noncomputable def unitaryDet (C : A →ₛₗ[h.bar] A →ₗ[E] E) :
    sesqUnitaryGroup C →* Eˣ :=
  (Units.map (LinearMap.det : Module.End E A →* E)).comp
    ((sesqUnitaryGroup C).subtype)

noncomputable abbrev unitarySpecial (C : A →ₛₗ[h.bar] A →ₗ[E] E) : Subgroup (sesqUnitaryGroup C) :=
  (unitaryDet C).ker

theorem mem_unitarySpecial {C : A →ₛₗ[h.bar] A →ₗ[E] E} {g : sesqUnitaryGroup C} :
    g ∈ unitarySpecial C ↔
      LinearMap.det ((g : LinearMap.GeneralLinearGroup E A) : Module.End E A) = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem commutator_le_unitarySpecial (C : A →ₛₗ[h.bar] A →ₗ[E] E) :
    _root_.commutator (sesqUnitaryGroup C) ≤ unitarySpecial C :=
  Abelianization.commutator_subset_ker _

variable [FiniteDimensional E A]

theorem isSolvable_of_small (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hA1 : 1 ≤ finrank E A) {C : A →ₛₗ[h.bar] A →ₗ[E] E} (hC : C.IsSymm)
    (hCl : C.SeparatingLeft) (hs : finrank E A = 1 ∨ (finrank E A, p ^ f) = (2, 3)) :
    Group.IsSolvable (sesqUnitaryGroup C) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨-, h2, -⟩ := CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components p f
    hp h.one_le h.card_eq_sq C hC (CatalogueBUnitaryB.nondegenerate_of_isSymm hC hCl) hA1
  have := (h2 hs).1
  exact Group.isSolvable_of_surjective
    (f := (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h C).symm.toMonoidHom)
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h C).symm.surjective

theorem isQuasisimple_unitarySpecial (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hA1 : 1 ≤ finrank E A) {C : A →ₛₗ[h.bar] A →ₗ[E] E} (hC : C.IsSymm)
    (hCl : C.SeparatingLeft) (hns : ¬ (finrank E A = 1 ∨ (finrank E A, p ^ f) = (2, 3))) :
    CFSG.IsQuasisimple (unitarySpecial C) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨-, -, h3⟩ := CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components p f
    hp h.one_le h.card_eq_sq C hC (CatalogueBUnitaryB.nondegenerate_of_isSymm hC hCl) hA1
  have hq := (h3 ⟨fun h1 => hns (Or.inl h1), fun h1 => hns (Or.inr h1)⟩).1
  set e := CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h C with he
  have hmap : (unitarySpecial C).map e.toMonoidHom =
      CatalogueBUnitaryIsometry.specialIsometry
        (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (CatalogueBUnitaryIsometry.mem_specialIsometry_iff
        (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C
        (e.toMonoidHom g)).mpr (mem_unitarySpecial.mp hg)
    · intro hx
      have h1 := (CatalogueBUnitaryIsometry.mem_specialIsometry_iff
        (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C x).mp hx
      exact ⟨e.symm x, mem_unitarySpecial.mpr h1, e.apply_symm_apply x⟩
  exact (isQuasisimple_congr (((unitarySpecial C).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr hmap))).2 hq

theorem eq_unitarySpecial_of_isComponent (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hA1 : 1 ≤ finrank E A) {C : A →ₛₗ[h.bar] A →ₗ[E] E} (hC : C.IsSymm)
    (hCl : C.SeparatingLeft) {L : Subgroup (sesqUnitaryGroup C)} (hL : CFSG.IsComponent L) :
    2 ≤ finrank E A ∧ (finrank E A, p ^ f) ≠ (2, 3) ∧ L = unitarySpecial C := by
  have : Finite E := h.finite
  by_cases hs : finrank E A = 1 ∨ (finrank E A, p ^ f) = (2, 3)
  · exfalso
    have : Group.IsSolvable (sesqUnitaryGroup C) := isSolvable_of_small h hp hA1 hC hCl hs
    have : Group.IsPerfect L := hL.1.1
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · refine ⟨by omega, fun h23 => hs (Or.inr h23), ?_⟩
    exact eq_of_isComponent_of_quasisimple (isQuasisimple_unitarySpecial h hp hA1 hC hCl hs)
      (commutator_le_unitarySpecial C) hL

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
