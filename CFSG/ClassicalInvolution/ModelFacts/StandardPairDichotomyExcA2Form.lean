module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem

theorem form_eq_iform_tag (τ : Tag) (hA : TauCeti.IsFiniteType τ.cartan) :
    ∃ c : ℚ, 0 < c ∧ ∀ x y : Fin τ.rank → ℤ,
      form hA (toRat x) (toRat y) = c * (iform x y : ℚ) := by
  obtain ⟨c, hc, hd⟩ := exists_symmetrizer_eq τ
  refine ⟨c, hc, fun x y => ?_⟩
  have hxy : form hA (toRat x) (toRat y) =
      ∑ l, (y l : ℚ) * ∑ i, (x i : ℚ) * (symmetrizer hA l * (τ.cartan l i : ℚ)) := by
    rw [form_eq_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [toRat_apply, form_comm, form_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toRat_apply, form_single_left]
    simp [Pi.single_apply]
  rw [hxy]
  simp only [iform, hd]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hB : (τ.symmetrizedCartan i l : ℤ) = τ.symmetrizedCartan l i :=
    symmetrizedCartan_symm τ i l
  rw [symmetrizedCartan_apply, symmetrizedCartan_apply] at hB
  have hB' : ((τ.symmetrizer i i : ℤ) : ℚ) * (τ.cartan i l : ℚ) =
      (τ.symmetrizer l l : ℚ) * (τ.cartan l i : ℚ) := by exact_mod_cast hB
  rw [symmetrizedCartan_apply]
  push_cast
  linear_combination (-(c * (y l : ℚ) * (x i : ℚ))) * hB'

end CFSG.ClassicalInvolution.ModelFacts.Levi
