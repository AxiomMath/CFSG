module

public import CFSG.LieType.AlgebraicGroups.PointSurjectivityExtension

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

theorem exceptional_Lang_affine_equations_field_extension {k L : Type} [Field k]
    [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L] {B : Type} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] {J : Type} [Finite J] (A : J → Type) [∀ j, CommRing (A j)]
    [∀ j, Algebra k (A j)] [∀ j, Algebra.FiniteType k (A j)] (φ : ∀ j, B →ₐ[k] A j)
    {I : Type} (eqs : ∀ j, I → A j)
    (hsurj : ∀ y : B →ₐ[k] k, ∃ j, ∃ x : A j →ₐ[k] k,
      x.comp (φ j) = y ∧ ∀ i, x (eqs j i) = 0) :
    ∀ y : B →ₐ[k] L, ∃ j, ∃ x : A j →ₐ[k] L,
      x.comp (φ j) = y ∧ ∀ i, x (eqs j i) = 0 := by
  classical
  let A' : J → Type := fun j => A j ⧸ Ideal.span (Set.range (eqs j))
  let φ' : ∀ j, B →ₐ[k] A' j := fun j =>
    (Ideal.Quotient.mkₐ k (Ideal.span (Set.range (eqs j)))).comp (φ j)
  have hsurj' : ∀ y : B →ₐ[k] k, ∃ j, ∃ x : A' j →ₐ[k] k, x.comp (φ' j) = y := by
    intro y
    obtain ⟨j, x, hx, hx0⟩ := hsurj y
    let Ij : Ideal (A j) := Ideal.span (Set.range (eqs j))
    have hker : Ij ≤ RingHom.ker x := by
      rw [Ideal.span_le]
      rintro a ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (hx0 i)
    refine ⟨j, Ideal.Quotient.liftₐ Ij x fun a ha => RingHom.mem_ker.mp (hker ha), ?_⟩
    change (Ideal.Quotient.liftₐ Ij x _).comp
      ((Ideal.Quotient.mkₐ k Ij).comp (φ j)) = y
    rw [← AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, hx]
  intro y
  obtain ⟨j, x', hx'⟩ := exceptional_Lang_constructible_point_surjectivity_field_extension
    (fun j => A j ⧸ Ideal.span (Set.range (eqs j)))
    (fun j => (Ideal.Quotient.mkₐ k (Ideal.span (Set.range (eqs j)))).comp (φ j)) hsurj' y
  refine ⟨j, x'.comp (Ideal.Quotient.mkₐ k (Ideal.span (Set.range (eqs j)))), ?_, ?_⟩
  · rw [AlgHom.comp_assoc]
    exact hx'
  · intro i
    have hmem : eqs j i ∈ Ideal.span (Set.range (eqs j)) :=
      Ideal.subset_span ⟨i, rfl⟩
    have hzero : Ideal.Quotient.mkₐ k (Ideal.span (Set.range (eqs j))) (eqs j i) = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    change x' (Ideal.Quotient.mkₐ k (Ideal.span (Set.range (eqs j))) (eqs j i)) = 0
    rw [hzero, map_zero]

end CFSG.LieType.AlgebraicGroups
