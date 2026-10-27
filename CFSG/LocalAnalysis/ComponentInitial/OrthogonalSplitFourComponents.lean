module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFourNormalizer
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_left_or_right_of_isSubnormal (hK : 4 ≤ Nat.card K)
    {T : Subgroup (DeterminantIsometries K)} (hT : CFSG.IsQuasisimple T)
    (hTs : CFSG.Assembly.IsSubnormal T ⊤) :
    T = determinantLeftFactor K ∨ T = determinantRightFactor K := by
  classical
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  haveI : Finite (DeterminantIsometries K) :=
    Finite.of_injective
      (fun g : DeterminantIsometries K =>
        (g.val : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K))
      fun g h heq => Subtype.ext (LinearEquiv.ext fun X => congrFun heq X)
  have hJnormal : (specialImage K).Normal := by
    rw [← determinant_commutator_eq hK2 hK3]
    infer_instance
  have hcn : ((specialImage K).subgroupOf (⊤ : Subgroup (DeterminantIsometries K))).Normal :=
    (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ => hJnormal.conj_mem x hx k
  have hcomp : ∀ F : Subgroup (DeterminantIsometries K), F ≤ specialImage K →
      (F.subgroupOf (specialImage K)).Normal → CFSG.IsQuasisimple F →
      CFSG.Assembly.IsComponentOf F ⊤ := by
    intro F hFle hFn hFq
    exact ⟨le_top, CFSG.Assembly.IsSubnormal.step hFle hFn
        (CFSG.Assembly.IsSubnormal.step le_top hcn (CFSG.Assembly.IsSubnormal.refl ⊤)),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native F).mpr hFq⟩
  have hTA : CFSG.Assembly.IsComponentOf T ⊤ :=
    ⟨le_top, hTs,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native T).mpr hT⟩
  have hL := hcomp _ determinantLeftFactor_le determinantLeftFactor_normal
    (determinantLeftFactor_quasisimple hK2 hK3)
  have hR := hcomp _ determinantRightFactor_le determinantRightFactor_normal
    (determinantRightFactor_quasisimple hK2 hK3)
  rcases isComponentOf_eq_or_commute hTA hL with h1 | h1
  · exact Or.inl h1
  rcases isComponentOf_eq_or_commute hTA hR with h2 | h2
  · exact Or.inr h2
  exfalso
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
  have h5 : specialImage K ≤ Subgroup.centralizer (T : Set (DeterminantIsometries K)) := by
    rw [← determinantFactors_sup]
    exact sup_le h1 h2
  haveI : Group.IsPerfect T := hT.1
  have hTc : T ≤ specialImage K := by
    calc T = ⁅T, T⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ commutator (DeterminantIsometries K) := Subgroup.commutator_mono le_top le_top
      _ = specialImage K := determinant_commutator_eq hK2 hK3
  exact not_le_centralizer_self_of_isQuasisimple hTA.2.2 (hTc.trans h5)

theorem not_le_normalizer_of_isSubnormal (hK : 4 ≤ Nat.card K)
    {T P : Subgroup (DeterminantIsometries K)} (hT : CFSG.IsQuasisimple T)
    (hTs : CFSG.Assembly.IsSubnormal T ⊤) (hP : ¬ 2 ∣ P.index) :
    ¬ P ≤ normalizer (T : Set (DeterminantIsometries K)) := by
  classical
  have hNT : normalizer (T : Set (DeterminantIsometries K)) ≤ specialImage K := by
    rcases eq_left_or_right_of_isSubnormal hK hT hTs with h | h
    · rw [h]
      exact normalizer_determinantLeftFactor_le
    · rw [h]
      exact normalizer_determinantRightFactor_le
  intro hPT
  have hdvd : (specialImage K).index ∣ P.index := Subgroup.index_dvd_of_le (hPT.trans hNT)
  rw [index_specialImage] at hdvd
  exact hP hdvd

end CFSG.LocalAnalysis.ComponentInitial
