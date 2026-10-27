module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBModel
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC.PSLSmallGraph3

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial

theorem shape_f {f : ℕ} (hs : A6Shape .PSL 3 f) : f = 2 := by
  simpa [A6Shape] using hs

theorem pureGraph_not_inner {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (A : GL (Fin n) K) :
    pureGraphAction n K A ∉ (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) K →*
      MulAut (ProjectiveSpecialLinearGroup (Fin n) K)).range := by
  rintro ⟨z, hz⟩
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL z)
  have h1 : MulAut.conj z = innerDiagonalAction n K B := by
    rw [innerDiagonalAction_eq_pglAction, hB, pglAction_toPGL]
  have h2 := CatalogueBLinearHigherB.congr_pureGraph (K := K) (n := n) A
  have h3 := CatalogueBLinearHigherB.congr_conjAut (K := K) (n := n) B
  have h4 : LinearFlag.conjAut n K A * LinearFlag.dualAut n K = LinearFlag.conjAut n K B :=
    (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)).injective (by
      rw [h2, h3, ← h1]
      exact hz.symm)
  have h5 := ProjectivePlane.standard_form_unique hn (A := A) (B := B) (σ := 1) (τ := 1)
    (ε := 1) (η := 0) le_rfl (Nat.zero_le _) (by
      simpa only [map_one, mul_one, pow_one, pow_zero] using h4)
  exact absurd h5.2 (by norm_num)

theorem a6_orderOf_ne_eight (g : alternatingGroup (Fin 6)) : orderOf g ≠ 8 := by
  intro h
  have h1 : orderOf (g : Equiv.Perm (Fin 6)) = 8 := by rw [Subgroup.orderOf_coe]; exact h
  have h2 : orderOf (g : Equiv.Perm (Fin 6)) ∣ 60 := by
    rw [← Equiv.Perm.lcm_cycleType]
    refine Multiset.lcm_dvd.mpr fun n hn => ?_
    have h2n := Equiv.Perm.two_le_of_mem_cycleType hn
    have h6 : n ≤ 6 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
      (by simpa using Finset.card_le_univ (g : Equiv.Perm (Fin 6)).support)
    interval_cases n <;> decide
  rw [h1] at h2
  exact absurd h2 (by norm_num)

section Dihedral

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem outer_involution_of_dihedral (h : A6Hyp σ D) {z t : ↥(fixedSubgroup σ)}
    (hz : orderOf z = 8) (ht : orderOf t = 2) (hzt : t * z * t⁻¹ = z⁻¹) :
    ∃ x : ↥(fixedSubgroup σ), orderOf x = 2 ∧ x ∉ D := by
  obtain ⟨-, ⟨eD⟩, -⟩ := h
  have hzD : z ∉ D := by
    intro hzD
    have : orderOf (⟨z, hzD⟩ : ↥D) = 8 := by
      rw [← hz, ← Subgroup.orderOf_coe]
    have h8 := a6_orderOf_ne_eight (eD ⟨z, hzD⟩)
    rw [MulEquiv.orderOf_eq eD] at h8
    exact h8 this
  have ht2 : t * t = 1 := by rw [← pow_two]; exact ht ▸ pow_orderOf_eq_one t
  by_cases htD : t ∈ D
  · refine ⟨t * z, ?_, fun hx => hzD ?_⟩
    · have hsq : (t * z) * (t * z) = 1 := by
        have h1 : t * z * t = z⁻¹ := by
          have := hzt
          rwa [show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2] at this
        calc (t * z) * (t * z) = (t * z * t) * z := by group
          _ = 1 := by rw [h1]; group
      have hne : t * z ≠ 1 := by
        intro h1
        have : z = t⁻¹ := by
          calc z = t⁻¹ * (t * z) := by group
            _ = t⁻¹ := by rw [h1]; group
        have h2 : orderOf z = 2 := by
          rw [this, orderOf_inv]; exact ht
        omega
      exact orderOf_eq_prime (by rw [← pow_two] at hsq; exact hsq) hne
    · have : t⁻¹ * (t * z) ∈ D := by
        exact D.mul_mem (D.inv_mem htD) hx
      simpa using this
  · exact ⟨t, ht, htD⟩

end Dihedral

end CFSG.ComponentClassification.CatFC.PSLSmallGraph3
