module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalEightOuter
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1POddOut

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

theorem card_outer_dvd_of_pOmegaOdd (T : Type) [Group T] {n p f : ℕ}
    (h : StatedClassicalModel T .POmegaOdd n p f) : Nat.card (Outer T) ∣ 2 * f := by
  have h0 := h
  obtain ⟨⟨hp, hf, hn, hp2⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let hF : Field K := hfield
  let hFin : Finite K := hfinite
  set Q := coordinateQuadOdd n K
  have hchar : ringChar K = p := ringChar_eq_of_card_eq hp hf hK
  have h2 : ringChar K ≠ 2 := by
    rw [hchar]
    exact hp2
  have hE : matrixProjectiveImage Q = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n p f
      h0) K hK e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
      (.inl rfl) n p f h0) K hK).2
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived Q)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinateOddWitnessEquiv K e)).toEquiv
  have hneg : (⟨-1, OrthogonalOuter.neg_one_mem_matrixIsometries Q⟩ :
      matrixIsometries Q) ∉ commutator (matrixIsometries Q) := by
    have hscalar : (GeneralLinearGroup.scalar (Fin (2 * n + 1)) (-1 : Kˣ) :
        GL (Fin (2 * n + 1)) K) = -1 := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    intro hmem
    have hmem' : CFSG.ComponentClassification.HarrisLit.T1.negOneIsometry K n ∈
        commutator (matrixIsometries Q) := by
      rw [show CFSG.ComponentClassification.HarrisLit.T1.negOneIsometry K n =
        ⟨-1, OrthogonalOuter.neg_one_mem_matrixIsometries Q⟩ from Subtype.ext hscalar]
      exact hmem
    have h1 : Abelianization.of (CFSG.ComponentClassification.HarrisLit.T1.negOneIsometry K n) =
        1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      exact hmem'
    exact CFSG.ComponentClassification.HarrisLit.T1.of_negOneIsometry_ne_one K n h2 h1
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl) n p f
    h0 K hK (quadOdd n K) (coe_quadOdd n K) e
  rw [hout, card_outer_eq Q]
  set A := (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range with hA
  set B := (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range with hB
  set C := (linearConjugationHom Q).range.relIndex (matrixProjectiveImage Q) with hC
  set D := (matrixProjectiveImage Q).index with hD
  have hbound : 2 * A ≤ 4 :=
    ((two_mul_relIndex_inner_le Q hneg).trans
      (card_abelianization_matrixIsometries_reindex (oddIndexEquiv n) (quadOdd n K)).le).trans
        (hab.2.1 hp2)
  have ha : A ∣ 2 := by
    have hle : A ≤ 2 := by omega
    have hpos : 0 < A := by
      rw [hA]
      exact Nat.pos_of_dvd_of_pos (relIndex_inner_dvd Q) Nat.card_pos
    have hA12 : A = 1 ∨ A = 2 := by omega
    rcases hA12 with h1 | h1
    · simp [h1]
    · simp [h1]
  have hb : B = 1 := by
    rw [hB]
    refine Subgroup.relIndex_eq_one.mpr ?_
    rintro _ ⟨g, rfl⟩
    obtain ⟨A', hA'⟩ := CFSG.ComponentClassification.HarrisLit.T1.exists_isometry_of_linear
      (K := K) (n := n) h2 hn g
    exact ⟨A', hA'⟩
  have hc : C ∣ f := by
    rw [hC]
    exact (relIndex_linearRange_dvd Q).trans
      ((Subgroup.card_subgroup_dvd_card (fieldProjection Q).range).trans
        (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hd : D = 1 := by
    rw [hD, hE, Subgroup.index_top]
  rw [hb, hd, mul_one, mul_one]
  exact Nat.mul_dvd_mul ha hc

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

end
