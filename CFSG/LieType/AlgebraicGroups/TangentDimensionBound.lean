module

public import CFSG.LieType.AlgebraicGroups.TangentDimension
public import CFSG.LieType.AlgebraicGroups.TorusAffineDomain

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

theorem trdeg_fractionRing_eq {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [FaithfulSMul k A] :
    Algebra.trdeg k (FractionRing A) = Algebra.trdeg k A := by
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  rw [← trdeg_add_eq k A (A := FractionRing A), trdeg_eq_zero (R := A) (A := FractionRing A),
    add_zero]

theorem exists_injective_of_forall_exists_comp_eq {k A : Type} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A] {I : Type} [Finite I]
    (D : I → Type) [∀ i, CommRing (D i)] [∀ i, Algebra k (D i)] (φ : ∀ i, A →ₐ[k] D i)
    (hcov : ∀ y : A →ₐ[k] k, ∃ i, ∃ z : D i →ₐ[k] k, z.comp (φ i) = y) :
    ∃ i, Function.Injective (φ i) := by
  have : Fintype I := Fintype.ofFinite I
  by_contra hne
  push Not at hne
  have hker : ∀ i, ∃ c : A, c ≠ 0 ∧ φ i c = 0 := fun i => by
    obtain ⟨c₁, c₂, h, hne⟩ := Function.not_injective_iff.1 (hne i)
    exact ⟨c₁ - c₂, sub_ne_zero.2 hne, by rw [map_sub, h, sub_self]⟩
  choose c hc0 hc using hker
  have hprod : ∏ i, c i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
  refine hprod (eq_zero_of_forall_algHom k A _ fun y => ?_)
  obtain ⟨i, z, rfl⟩ := hcov y
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [AlgHom.comp_apply, hc, map_zero])

theorem trdeg_torusAffine (k : Type) [Field k] (a b : ℕ) :
    Algebra.trdeg k (TorusAffine k a b) = (a + b : ℕ) := by
  have : Algebra.IsAlgebraic (MvPolynomial (Fin a ⊕ Fin b) k) (TorusAffine k a b) :=
    IsLocalization.isAlgebraic (TorusAffine k a b) (Submonoid.powers (torusAffineDet k a b))
  have : FaithfulSMul (MvPolynomial (Fin a ⊕ Fin b) k) (TorusAffine k a b) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (torusAffineDet_ne_zero k a b)))
  rw [← trdeg_add_eq k (MvPolynomial (Fin a ⊕ Fin b) k) (A := TorusAffine k a b),
    trdeg_eq_zero (R := MvPolynomial (Fin a ⊕ Fin b) k) (A := TorusAffine k a b), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_sum, Cardinal.mk_fintype,
    Cardinal.mk_fintype, Fintype.card_fin, Fintype.card_fin, Cardinal.lift_id, Cardinal.lift_id,
    Nat.cast_add]

theorem exceptional_Lang_finite_parameter_tangent_dimension_bound {k : Type} [Field k]
    [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A]
    [Algebra.Smooth k A] {I : Type} [Fintype I] [Nonempty I] (a b : I → ℕ)
    (φ : ∀ i, A →ₐ[k] TorusAffine k (a i) (b i))
    (hcov : ∀ y : A →ₐ[k] k, ∃ i, ∃ z : TorusAffine k (a i) (b i) →ₐ[k] k, z.comp (φ i) = y) :
    ∀ x : A →ₐ[k] k,
      (Module.finrank k (TangentSpace k A x) : Cardinal) = Algebra.trdeg k (FractionRing A) ∧
        Algebra.trdeg k (FractionRing A) ≤ (Finset.univ.sup fun i => a i + b i : ℕ) := by
  intro x
  refine ⟨finrank_tangentSpace_eq_trdeg x, ?_⟩
  obtain ⟨i, hi⟩ := exists_injective_of_forall_exists_comp_eq _ φ hcov
  rw [trdeg_fractionRing_eq]
  calc Algebra.trdeg k A ≤ Algebra.trdeg k (TorusAffine k (a i) (b i)) :=
        trdeg_le_of_injective (φ i) hi
    _ = (a i + b i : ℕ) := trdeg_torusAffine k (a i) (b i)
    _ ≤ (Finset.univ.sup fun i => a i + b i : ℕ) :=
        Nat.cast_le.2 (Finset.le_sup (f := fun i => a i + b i) (Finset.mem_univ i))

end CFSG.LieType.AlgebraicGroups
