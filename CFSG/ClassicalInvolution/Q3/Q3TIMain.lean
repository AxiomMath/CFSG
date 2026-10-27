module

public import CFSG.ClassicalInvolution.Q3.Q3TIDesc
public import CFSG.ClassicalInvolution.Q3.Q3TIModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores

section Outer


@[expose] def AlmostSimpleOuter3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (Q3B.conjClass L) →
          T.Normal → Subgroup.centralizer (T : Set Y) = ⊥ → IsClassicalMember3 (L ⊓ T) z

end Outer

section Assembly

theorem tightNormalInnerConn_of_residuals (h1 : ModelOddAutRigid) (h2 : AlmostSimpleOuter3) :
    Q3B.TightNormalInnerConn := by
  intro Y _ _ hBelow hO z L hz T hT hTL hgen hconn hTn hTz
  have : T.Normal := hTn
  by_cases hD : Subgroup.centralizer (T : Set Y) = ⊥
  · exact le_sup_of_le_left (le_of_almostSimple_member h1 hBelow hz hT hD
      (h2 Y hBelow hO z L hz T hT hTL hgen hconn hTn hD))
  · exact le_sup_centralizer_of_centralizer_ne_bot hBelow hO hz hT hTL hgen hTz hD

theorem solvableMemberInnerTight_of_residuals (h1 : ModelOddAutRigid)
    (h2 : AlmostSimpleOuter3) : SolvableMemberInnerTight :=
  Q3B.solvableMemberInnerTight_of_conn
    (Q3B.solvableMemberInnerTightConn_of_normalizes_of_normalInner
      tightNormalizesComponentConn_proved (tightNormalInnerConn_of_residuals h1 h2))

theorem quasisimpleConnected3_of_residuals (h1 : ModelOddAutRigid) (h2 : AlmostSimpleOuter3) :
    QuasisimpleConnected3 :=
  quasisimpleConnected3_of_tight m11Facts (solvableMemberInnerTight_of_residuals h1 h2)

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T
