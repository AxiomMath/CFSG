module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer

public section

namespace CFSG.ComponentClassification.CatFC.OmegaSmall

open Module Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare (orthogonalOperatorCentralizer)

section Abstract

theorem card_fixed_normalCentralQuotient_dvd {X : Type*} [Group X] [Finite X]
    (N Z : Subgroup X) [N.Normal] [Z.Normal] (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z) :
    Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (fixedSubgroup ψ) ∣
      Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) * Nat.card X := by
  have hZ'inv := restricted_central_invariant N Z ψ hN hZ
  set P := fixedProjection (Z.subgroupOf N) (restrictAutomorphism N ψ hN) hZ'inv with hP
  have hker := fixedProjection_kernel (Z.subgroupOf N) (restrictAutomorphism N ψ hN) hZ'inv
  have h1 : Nat.card (N.subgroupOf (fixedSubgroup ψ)) = Nat.card P.range * Nat.card P.ker := by
    rw [← Nat.card_congr (fixedNormalEquiv N ψ hN).toEquiv]
    exact card_eq_card_range_mul_card_ker P
  have h2 : Nat.card P.ker ∣ Nat.card (Z.subgroupOf N) := by
    rw [hP, hker, card_subgroupOf_eq_card_inf]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card P.range ∣
      Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) :=
    Subgroup.card_subgroup_dvd_card _
  have h4 : N.relIndex (fixedSubgroup ψ) ∣ N.index := Subgroup.relIndex_dvd_index_of_normal _ _
  have h5 : Nat.card (fixedSubgroup ψ) =
      Nat.card (N.subgroupOf (fixedSubgroup ψ)) * N.relIndex (fixedSubgroup ψ) :=
    (Subgroup.card_mul_index (N.subgroupOf (fixedSubgroup ψ))).symm
  have h6 : N.index * Nat.card N = Nat.card X := Subgroup.index_mul_card N
  have h7 : Nat.card N = Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (Z.subgroupOf N) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
  calc Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (fixedSubgroup ψ)
      = Nat.card (N ⧸ Z.subgroupOf N) *
          ((Nat.card P.range * Nat.card P.ker) * N.relIndex (fixedSubgroup ψ)) := by
        rw [h5, h1]
    _ ∣ Nat.card (N ⧸ Z.subgroupOf N) *
          ((Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) *
            Nat.card (Z.subgroupOf N)) * N.index) :=
        Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul (Nat.mul_dvd_mul h3 h2) h4)
    _ = Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) *
          (N.index * (Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (Z.subgroupOf N))) := by
        ring
    _ = _ := by rw [← h7, h6]

theorem two_pow_sub_two_dvd_of_two_pow_dvd_four_mul {k m : ℕ} (h : 2 ^ k ∣ 4 * m) :
    2 ^ (k - 2) ∣ m := by
  rcases Nat.le_total k 2 with hk | hk
  · rw [Nat.sub_eq_zero_of_le hk]
    exact one_dvd _
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [Nat.add_sub_cancel]
    rw [pow_add] at h
    have h' : 4 * 2 ^ j ∣ 4 * m := by
      rw [mul_comm 4 (2 ^ j)]
      simpa using h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) h'

end Abstract

section Orthogonal

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem finite_orthogonalGroup_fin_fun (Q : QuadraticForm K (Fin d → K)) :
    Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Finite.of_injective (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
    ((g.val : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) → (Fin d → K)))
    (fun a b h => Subtype.ext (LinearEquiv.coe_injective h))

theorem omega_linear_fixed_card_dvd (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q) (hg : g.val.right = 1) :
    Nat.card (matrixProjectiveDerived Q) *
        Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap) ∣
      Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  haveI := finite_orthogonalGroup_fin_fun Q
  have hex := exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd
  set A := matrixLinearEquiv g.val.left with hA
  set μ := multiplier Q g with hμ
  have hsim := matrix_similarity Q g hg
  have h1 : Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) =
      Nat.card (fixedSubgroup (projectiveConjugation Q A μ hsim)) :=
    Nat.card_congr (linearFixedEquiv Q hex g hg).toEquiv
  have h2 := card_fixed_normalCentralQuotient_dvd (orthogonalDerived Q) (scalarSigns Q)
    (similarityConjugation Q A μ hsim) (orthogonalDerived_invariant Q A μ hsim)
    (scalarSigns_invariant Q A μ hsim)
  have h3 : Nat.card (fixedSubgroup (similarityConjugation Q A μ hsim)) =
      Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) :=
    Nat.card_congr (fixedCentralizerEquiv Q A μ hsim).toEquiv
  have h4 : Nat.card (matrixProjectiveDerived Q) = Nat.card (projectiveDerived Q) :=
    Nat.card_congr (projectiveEquiv Q hex).toEquiv
  rw [h1, h4, ← h3]
  exact h2

theorem card_centralizer_dvd_four_mul_card_fixed (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q) (hg : g.val.right = 1)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      4 * Nat.card (matrixProjectiveDerived Q)) :
    Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap) ∣
      4 * Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) := by
  have h := omega_linear_fixed_card_dvd hd Q hQ g hg
  rw [hcard] at h
  have hpos : 0 < Nat.card (matrixProjectiveDerived Q) := Nat.card_pos
  refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
  calc Nat.card (matrixProjectiveDerived Q) *
        Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap)
      ∣ Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) *
          (4 * Nat.card (matrixProjectiveDerived Q)) := h
    _ = _ := by ring

theorem two_pow_sub_two_dvd_card_fixed_matrixProjectiveConjugation (hd : 0 < d)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q)
    (hg : g.val.right = 1)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      4 * Nat.card (matrixProjectiveDerived Q)) {k : ℕ}
    (hk : 2 ^ k ∣
      Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap)) :
    2 ^ (k - 2) ∣ Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) :=
  two_pow_sub_two_dvd_of_two_pow_dvd_four_mul
    (hk.trans (card_centralizer_dvd_four_mul_card_fixed hd Q hQ g hg hcard))

end Orthogonal

end CFSG.ComponentClassification.CatFC.OmegaSmall
