module

public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

lemma aux_units_zmod3 : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide

private lemma aux_neg_one_not_isSquare_units : ¬ IsSquare (-1 : (ZMod 3)ˣ) := by decide

lemma aux_squareClass_neg_one_ne_zero :
    squareClass (-1 : (ZMod 3)ˣ) ≠ 0 := by
  intro h
  exact aux_neg_one_not_isSquare_units ((squareClass_eq_zero_iff _).mp h)

private lemma aux_squareClassGroup_zmod3 (x : SquareClassGroup (ZMod 3)) :
    x = 0 ∨ x = squareClass (-1 : (ZMod 3)ˣ) := by
  have h := aux_units_zmod3 (Additive.toMul (Quotient.out x))
  rw [← squareClass_toMul_out x]
  rcases h with h | h <;> rw [h]
  · left
    rw [squareClass_eq_zero_iff]
    exact ⟨1, by simp⟩
  · right
    rfl

lemma aux_subgroup_eq_top_of_mem
    {H : Subgroup ((ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3)))}
    (h1 : ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) ∈ H)
    (h2 : ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  rcases aux_units_zmod3 a with rfl | rfl
  · rcases aux_squareClassGroup_zmod3 (Multiplicative.toAdd b) with hb | hb
    · rw [← ofAdd_toAdd b, hb]
      exact H.one_mem
    · rw [← ofAdd_toAdd b, hb]
      have h11 : ((-1 : (ZMod 3)ˣ)) * (-1) = 1 := by decide
      simpa [h11, one_mul] using H.mul_mem h1 h2
  · rcases aux_squareClassGroup_zmod3 (Multiplicative.toAdd b) with hb | hb
    · rw [← ofAdd_toAdd b, hb]
      exact h1
    · rw [← ofAdd_toAdd b, hb]
      exact h2

@[expose] noncomputable def omegaGroup (hQ : Q.Nondegenerate) : Subgroup (OGroup Q) :=
  (detSpinorNorm hQ).ker

instance omegaGroup_normal (hQ : Q.Nondegenerate) : (omegaGroup hQ).Normal :=
  MonoidHom.normal_ker _

theorem mem_omegaGroup_iff (hQ : Q.Nondegenerate) {g : OGroup Q} :
    g ∈ omegaGroup hQ ↔ detSpinorNorm hQ g = 1 :=
  MonoidHom.mem_ker

theorem range_detSpinorNorm_eq_top (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : (detSpinorNorm hQ).range = ⊤ := by
  obtain ⟨v1, hv1⟩ := exists_eq_unit_of_two_le_finrank hQ h2 (1 : (ZMod 3)ˣ)
  obtain ⟨v2, hv2⟩ := exists_eq_unit_of_two_le_finrank hQ h2 (-1 : (ZMod 3)ˣ)
  have hv1' : Q v1 = 1 := by rw [hv1]; rfl
  have hv2' : Q v2 = -1 := by rw [hv2]; rfl
  have hQv1 : Q v1 ≠ 0 := by rw [hv1']; exact one_ne_zero
  have hQv2 : Q v2 ≠ 0 := by rw [hv2']; exact neg_ne_zero.mpr one_ne_zero
  let _ : Invertible (Q v1) := invertibleOfNonzero hQv1
  let _ : Invertible (Q v2) := invertibleOfNonzero hQv2
  have hunit1 : unitOfInvertible (Q v1) = (1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, hv1']; rfl)
  have hunit2 : unitOfInvertible (Q v2) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, hv2']; rfl)
  have hx1 : detSpinorNorm hQ (reflectionOrthogonal Q v1) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
    rw [detSpinorNorm_reflectionOrthogonal, hunit1, map_one]
  have hx2 : detSpinorNorm hQ (reflectionOrthogonal Q v2) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
    rw [detSpinorNorm_reflectionOrthogonal, hunit2, squareClassHom_apply]
  refine aux_subgroup_eq_top_of_mem ?_ ?_
  · exact MonoidHom.mem_range.mpr ⟨reflectionOrthogonal Q v1, hx1⟩
  · exact MonoidHom.mem_range.mpr ⟨reflectionOrthogonal Q v2, hx2⟩

theorem index_omegaGroup (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    (omegaGroup hQ).index = 4 := by
  rw [omegaGroup, Subgroup.index_ker, range_detSpinorNorm_eq_top hQ h2]
  have htop : Nat.card (⊤ : Subgroup
      ((ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3)))) =
      Nat.card ((ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3))) :=
    Nat.card_congr (Subgroup.topEquiv).toEquiv
  rw [htop, Nat.card_prod]
  have h1 : Nat.card ((ZMod 3)ˣ) = 2 := by
    rw [Nat.card_eq_two_iff' 1]
    exact ⟨(-1 : (ZMod 3)ˣ), by decide, fun y hy => (aux_units_zmod3 y).resolve_left hy⟩
  have h2' : Nat.card (SquareClassGroup (ZMod 3)) = 2 := by
    rw [Nat.card_eq_two_iff' 0]
    exact ⟨squareClass (-1 : (ZMod 3)ˣ), aux_squareClass_neg_one_ne_zero,
      fun y hy => (aux_squareClassGroup_zmod3 y).resolve_left hy⟩
  have h3 : Nat.card (Multiplicative (SquareClassGroup (ZMod 3))) = 2 := by
    rw [Nat.card_eq_two_iff' 1]
    refine ⟨Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)), ?_, fun y hy => ?_⟩
    · intro h
      exact aux_squareClass_neg_one_ne_zero (by simpa using congrArg Multiplicative.toAdd h)
    · rcases aux_squareClassGroup_zmod3 (Multiplicative.toAdd y) with h | h
      · exact absurd (by rw [← ofAdd_toAdd y, h]; rfl : y = 1) hy
      · rw [← ofAdd_toAdd y, h]
  rw [h1, h3]

end CFSG.OddStandard.SmallF3.Omega
