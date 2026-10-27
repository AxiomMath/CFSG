module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6CompsAux

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {K0 : Type} [Field K0]

theorem u6_shape_big [Fintype K0] {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (h : UnitaryFieldData 2 3 K0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) {y : X}
    {g : StatedSU 6 (2 ^ 3) K0} (hact : ActsAs K e y g) (hy3 : y ^ 3 = 1)
    (hbig : 4 ≤ maxEig (g : GL (Fin 6) K0))
    (hnotscal : ¬ ∃ c : K0ˣ, (g : GL (Fin 6) K0) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J →
      CFSG.Open.IsQuasisimple ↥J ∧ IsLieQuot ↥J IsU6BigCompIndex) ∧
    (∀ J₁ J₂ J₃ : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₁ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₂ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₃ →
        J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) := by
  obtain ⟨hy, A, ν, hA3, hgA, hε⟩ := U6Comps.exists_model_of_actsAs h e hact hy3
  have hbigA : ∃ c : K0, 4 ≤ eigMult (A : GL (Fin 6) K0) c := by
    unfold maxEig at hbig
    obtain ⟨c, -, hc⟩ := (Finset.le_sup_iff (by norm_num : ⊥ < 4)).1 hbig
    refine ⟨((ν⁻¹ : K0ˣ) : K0) * c, ?_⟩
    rw [hgA, U6Comps.eigMult_scalar_mul] at hc
    exact hc
  have hnsA : ∀ d : K0, eigMult (A : GL (Fin 6) K0) d ≠ 6 :=
    U6Comps.eigMult_ne_six_of_not_scalar _ ν (by rw [← hgA]; exact hnotscal)
  obtain ⟨hty, h3⟩ := U6Comps.fixedComps_big h A hA3 hbigA hnsA
  have hlayer := LieSemisimple.perfectInLayer_primeFormP h (by norm_num) (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) (primeFormConjHom h (idGram K0 6) A)
    (U6Comps.conj_pow_three h A hA3)
  exact U6Comps.shape_of_model hy _ (by rw [hε]; exact hlayer) (by rw [hε]; exact hty)
    (by rw [hε]; exact h3)

theorem u6_shape_three [Fintype K0] {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (h : UnitaryFieldData 2 3 K0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) {y : X}
    {g : StatedSU 6 (2 ^ 3) K0} (hact : ActsAs K e y g) (hy3 : y ^ 3 = 1)
    (hdiv : ∀ c : K0, 3 ∣ eigMult (g : GL (Fin 6) K0) c)
    (hnotscal : ¬ ∃ c : K0ˣ, (g : GL (Fin 6) K0) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J →
      CFSG.Open.IsQuasisimple ↥J ∧ IsLieQuot ↥J KSF4SU3.IsU3EightIndexTwo) ∧
    (∀ J₁ J₂ J₃ : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₁ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₂ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₃ →
        J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) := by
  obtain ⟨hy, A, ν, hA3, hgA, hε⟩ := U6Comps.exists_model_of_actsAs h e hact hy3
  have hdivA : ∀ d : K0, 3 ∣ eigMult (A : GL (Fin 6) K0) d := by
    intro d
    have := hdiv (ν * d)
    rw [hgA, U6Comps.eigMult_scalar_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul] at this
    exact this
  have hnsA : ∀ d : K0, eigMult (A : GL (Fin 6) K0) d ≠ 6 :=
    U6Comps.eigMult_ne_six_of_not_scalar _ ν (by rw [← hgA]; exact hnotscal)
  obtain ⟨hty, h3⟩ := U6Comps.fixedComps_three h A hA3 hdivA hnsA
  have hlayer := LieSemisimple.perfectInLayer_primeFormP h (by norm_num) (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) (primeFormConjHom h (idGram K0 6) A)
    (U6Comps.conj_pow_three h A hA3)
  exact U6Comps.shape_of_model hy _ (by rw [hε]; exact hlayer) (by rw [hε]; exact hty)
    (by rw [hε]; exact h3)

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
