module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieAPI
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensionsTwo

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG

theorem hasCompOrSolv_of_isQuasisimple {G : Type*} [Group G] (h : IsQuasisimple G) :
    HasCompOrSolv G :=
  Or.inr ⟨⊤, LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h,
    Subgroup.Normal.isSubnormal inferInstance⟩

section Alt

open CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem hasCompOrSolv_isometry_alt (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hdim : 1 ≤ Module.finrank K V) (hodd : Odd (Nat.card K)) :
    HasCompOrSolv (isometryGroup B) := by
  have hdim2 : 2 ≤ Module.finrank K V := by
    obtain ⟨m, b, hd, -⟩ := exists_symplectic_basis B hB hnd
    omega
  by_cases hexc : Module.finrank K V = 2 ∧ Nat.card K = 3
  · exact Or.inl (plane_fieldThree_solvable B hB hnd hexc.1 hexc.2)
  · exact hasCompOrSolv_of_isQuasisimple
      (isometry_quasisimple B hB hnd hdim2 hodd (not_and_or.mp hexc))

end Alt

section Unitary

open CFSG.ComponentClassification.CatalogueBUnitaryIsometry

variable {E : Type} [Field E] [Finite E] {W : Type} [AddCommGroup W] [Module E W]
  [FiniteDimensional E W] {sigma : E ≃+* E} (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E)

theorem hasCompOrSolv_isometry_unitary (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hW : 1 ≤ Module.finrank E W)
    (hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2) :
    HasCompOrSolv (isometryGroup h) := by
  by_cases hd1 : Module.finrank E W = 1
  · exact Or.inl (isometry_one_solvable h hd1)
  by_cases hd2 : Module.finrank E W = 2
  · by_cases hq3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) = 3
    · exact Or.inl (isometry_two_three_solvable h hsym hnd hsigma hne hd2 hq3)
    · exact Or.inr ⟨specialIsometry h,
        specialIsometry_two_quasisimple h hsym hnd hsigma hne hd2 hq2 hq3,
        Subgroup.Normal.isSubnormal inferInstance⟩
  · have hd3 : 3 ≤ Module.finrank E W := by omega
    refine Or.inr ⟨specialIsometry h, specialIsometry_quasisimple_of_three_le h hsym hnd hsigma
      hne hd3 ?_, Subgroup.Normal.isSubnormal inferInstance⟩
    intro hh
    exact hq2 (Prod.mk.inj hh).2

end Unitary

end CFSG.ComponentClassification.CatFC.DS81
