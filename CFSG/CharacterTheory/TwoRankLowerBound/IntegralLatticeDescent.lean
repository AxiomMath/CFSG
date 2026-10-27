module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import Mathlib.NumberTheory.Niven
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def integerBasisComplexCoordinate {index : Type*} [Fintype index]
    (basis : Module.Basis index ℤ (index → ℤ)) (coordinate : index) : (index → ℂ) →ₗ[ℂ] ℂ where
  toFun := fun values => ∑ label, (basis.repr ((Pi.basisFun ℤ index) label) coordinate : ℂ) * values label
  map_add' := by
    intro left right
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar values
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro label _
    ring

theorem integerBasisComplexCoordinate_cast {index : Type*} [Fintype index]
    (basis : Module.Basis index ℤ (index → ℤ)) (coordinate : index) (values : index → ℤ) :
    integerBasisComplexCoordinate basis coordinate (fun label => (values label : ℂ)) =
      (basis.repr values coordinate : ℂ) := by
  have hrepr := congrArg (fun vector => basis.repr vector coordinate)
    ((Pi.basisFun ℤ index).sum_repr values)
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Pi.basisFun_repr] at hrepr
  change (∑ label, (basis.repr ((Pi.basisFun ℤ index) label) coordinate : ℂ) * values label) = _
  rw [← hrepr, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [Int.cast_mul]
  ring

theorem smithNormalForm_coordinate {index : Type*} [Fintype index]
    {lattice : Submodule ℤ (index → ℤ)} {size : ℕ}
    (form : Module.Basis.SmithNormalForm lattice index size) (values : lattice) (coordinate : index) :
    form.bM.repr (values : index → ℤ) coordinate =
      ∑ label : Fin size, form.bN.repr values label * form.a label *
        (if form.f label = coordinate then 1 else 0) := by
  have hexpansion := congrArg
    (fun value : lattice => form.bM.repr (value : index → ℤ) coordinate) (form.bN.sum_repr values)
  change form.bM.repr (lattice.subtype (∑ label : Fin size, form.bN.repr values label • form.bN label)) coordinate = _
    at hexpansion
  rw [map_sum] at hexpansion
  simp only [map_smul, map_sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hexpansion
  rw [← hexpansion]
  apply Finset.sum_congr rfl
  intro label _
  change form.bN.repr values label * form.bM.repr (form.bN label : index → ℤ) coordinate = _
  rw [form.snf, map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply]
  ring

theorem integer_inverse_algebraic_unit (integer : ℤ) (scalar : ComplexAlgebraicIntegers)
    (hproduct : (integer : ℂ) * (scalar : ℂ) = 1) : IsUnit integer := by
  have hnonzero : (integer : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hproduct
    exact zero_ne_one hproduct
  have hscalar : (scalar : ℂ) = ((1 / (integer : ℚ) : ℚ) : ℂ) := by
    push_cast
    exact (eq_div_iff hnonzero).mpr (by simpa only [mul_comm] using hproduct)
  obtain ⟨inverse, hinverse⟩ := scalar.property.exists_int_iff_exists_rat.mp ⟨_, hscalar⟩
  have hequal : integer * inverse = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_mul, Int.cast_one, ← hinverse]
    exact hproduct
  exact isUnit_iff_dvd_one.mpr ⟨inverse, hequal.symm⟩

theorem smith_coordinate_span_principal {index : Type*} [Fintype index]
    {lattice : Submodule ℤ (index → ℤ)} {size : ℕ}
    (form : Module.Basis.SmithNormalForm lattice index size) (target : Fin size)
    (values : index → ℂ)
    (hspan : values ∈ Submodule.span ComplexAlgebraicIntegers
      {function : index → ℂ | ∃ integerValues : lattice,
        function = fun coordinate => ((integerValues : index → ℤ) coordinate : ℂ)}) :
    integerBasisComplexCoordinate form.bM (form.f target) values ∈
      Submodule.span ComplexAlgebraicIntegers {(form.a target : ℂ)} := by
  induction hspan using Submodule.span_induction with
  | mem function hmember =>
    obtain ⟨integerValues, rfl⟩ := hmember
    rw [integerBasisComplexCoordinate_cast, smithNormalForm_coordinate]
    have hcoordinate : (∑ label : Fin size, form.bN.repr integerValues label * form.a label *
        (if form.f label = form.f target then 1 else 0)) =
        form.bN.repr integerValues target * form.a target := by
      simp only [form.f.injective.eq_iff, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hcoordinate, Int.cast_mul]
    apply Submodule.mem_span_singleton.mpr
    exact ⟨(form.bN.repr integerValues target : ComplexAlgebraicIntegers), rfl⟩
  | zero => simpa only [map_zero] using (Submodule.span ComplexAlgebraicIntegers {(form.a target : ℂ)}).zero_mem
  | add left right _ _ hleft hright =>
    rw [map_add]
    exact Submodule.add_mem _ hleft hright
  | smul scalar values _ hmember =>
    have hequal : integerBasisComplexCoordinate form.bM (form.f target) (scalar • values) =
        scalar • integerBasisComplexCoordinate form.bM (form.f target) values :=
      ((integerBasisComplexCoordinate form.bM (form.f target)).restrictScalars ComplexAlgebraicIntegers).map_smul _ _
    rw [hequal]
    exact Submodule.smul_mem _ scalar hmember

theorem smith_coordinate_span_zero_outside {index : Type*} [Fintype index]
    {lattice : Submodule ℤ (index → ℤ)} {size : ℕ}
    (form : Module.Basis.SmithNormalForm lattice index size) (coordinate : index)
    (hnot : coordinate ∉ Set.range form.f) (values : index → ℂ)
    (hspan : values ∈ Submodule.span ComplexAlgebraicIntegers
      {function : index → ℂ | ∃ integerValues : lattice,
        function = fun coordinate => ((integerValues : index → ℤ) coordinate : ℂ)}) :
    integerBasisComplexCoordinate form.bM coordinate values = 0 := by
  induction hspan using Submodule.span_induction with
  | mem function hmember =>
    obtain ⟨integerValues, rfl⟩ := hmember
    rw [integerBasisComplexCoordinate_cast, smithNormalForm_coordinate]
    have hne : ∀ label : Fin size, form.f label ≠ coordinate :=
      fun label hequal => hnot ⟨label, hequal⟩
    simp only [hne, ite_false, mul_zero, Finset.sum_const_zero, Int.cast_zero]
  | zero => exact map_zero _
  | add left right _ _ hleft hright => rw [map_add, hleft, hright, add_zero]
  | smul scalar values _ hzero =>
    have hequal : integerBasisComplexCoordinate form.bM coordinate (scalar • values) =
        scalar • integerBasisComplexCoordinate form.bM coordinate values :=
      ((integerBasisComplexCoordinate form.bM coordinate).restrictScalars ComplexAlgebraicIntegers).map_smul _ _
    rw [hequal, hzero, smul_zero]

theorem integer_lattice_eq_top_of_algebraic_span {index : Type*} [Fintype index]
    (lattice : Submodule ℤ (index → ℤ))
    (hspan : ∀ integerValues : index → ℤ,
      (fun coordinate => (integerValues coordinate : ℂ)) ∈ Submodule.span ComplexAlgebraicIntegers
        {function : index → ℂ | ∃ latticeValues : lattice,
          function = fun coordinate => ((latticeValues : index → ℤ) coordinate : ℂ)}) :
    lattice = ⊤ := by
  obtain ⟨size, form⟩ := Submodule.smithNormalForm (Pi.basisFun ℤ index) lattice
  have hsurjective : Function.Surjective form.f := by
    intro coordinate
    by_contra hnot
    have hnotRange : coordinate ∉ Set.range form.f := hnot
    have hzero := smith_coordinate_span_zero_outside form coordinate hnotRange _ (hspan (form.bM coordinate))
    rw [integerBasisComplexCoordinate_cast, Module.Basis.repr_self_apply, ite_eq_left rfl, Int.cast_one] at hzero
    exact one_ne_zero hzero
  have hunit : ∀ target : Fin size, IsUnit (form.a target) := by
    intro target
    have hmember := smith_coordinate_span_principal form target _ (hspan (form.bM (form.f target)))
    rw [integerBasisComplexCoordinate_cast, Module.Basis.repr_self_apply, ite_eq_left rfl, Int.cast_one] at hmember
    obtain ⟨scalar, hproduct⟩ := Submodule.mem_span_singleton.mp hmember
    apply integer_inverse_algebraic_unit (form.a target) scalar
    change (scalar : ℂ) * (form.a target : ℂ) = 1 at hproduct
    exact (mul_comm _ _).trans hproduct
  have hbasis : ∀ coordinate : index, form.bM coordinate ∈ lattice := by
    intro coordinate
    obtain ⟨target, rfl⟩ := hsurjective coordinate
    apply (lattice.smul_mem_iff_of_isUnit (hunit target)).mp
    rw [← form.snf]
    exact (form.bN target).property
  apply Submodule.eq_top_iff'.mpr
  intro values
  rw [← form.bM.sum_repr values]
  apply Submodule.sum_mem
  intro coordinate _
  exact lattice.smul_mem _ (hbasis coordinate)

end CFSG.TwoRankLowerBound.Helpers
