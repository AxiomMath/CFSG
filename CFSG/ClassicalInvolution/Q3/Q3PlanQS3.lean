module

public import CFSG.ClassicalInvolution.Q3.SP3
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem solvable_of_centralizer_pCore_le {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    (hΛ : InClass3 Λ)
    (hC : Subgroup.centralizer ((pCore 2 Y : Subgroup Y) : Set Y) ≤ pCore 2 Y) :
    Group.IsSolvable Y := by
  have hUn : (pCore 2 Y).Normal := pCore_normal
  have hU2 : IsPGroup 2 (pCore 2 Y) := pCore_isPGroup
  have hle : (⊤ : Subgroup Y) ≤ CFSG.solvableRadical Y := by
    rw [← hΛ.generated]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal
      (SP3.isSubnormal_of_central hz (SP3.involution_central hU2 hC hΛ hz)) hz.isSolvable
  have hrad : CFSG.solvableRadical Y = ⊤ := top_le_iff.mp hle
  have hsolv : Group.IsSolvable (CFSG.solvableRadical Y) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  rw [hrad] at hsolv
  exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := Y)).toMonoidHom)
    (Subgroup.topEquiv (G := Y)).surjective

@[expose] def QuasisimpleConnected3Comp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ Λ : Set (Subgroup Y), InClass3 Λ → NonCommConnected Λ → ¬ Group.IsSolvable Y →
      ¬ Subgroup.centralizer ((pCore 2 Y : Subgroup Y) : Set Y) ≤ pCore 2 Y →
        CFSG.Open.IsQuasisimple Y

theorem quasisimpleConnected3_of_comp (h : QuasisimpleConnected3Comp) : QuasisimpleConnected3 := by
  intro Y _ _ hBelow hO Λ hΛ hconn hns
  by_cases hC : Subgroup.centralizer ((pCore 2 Y : Subgroup Y) : Set Y) ≤ pCore 2 Y
  · exact absurd (solvable_of_centralizer_pCore_le hΛ hC) hns
  · exact h Y hBelow hO Λ hΛ hconn hns hC

end CFSG.ClassicalInvolution.Q3
