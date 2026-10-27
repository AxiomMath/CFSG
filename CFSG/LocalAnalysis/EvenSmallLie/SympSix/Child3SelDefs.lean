module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup

structure GL3Source {Y : Type} [Group Y] (D : Subgroup Y) (a : Y) (J : Subgroup Y) : Prop where
  normal : D.Normal
  simple : IsSimpleGroup D
  nonab : ∃ x y : D, x * y ≠ y * x
  centralizer_eq : centralizer (D : Set Y) = ⊥
  orderOf_eq : orderOf a = 2
  le : J ≤ D
  le_centralizer : J ≤ centralizer ({a} : Set Y)
  sup_eq : zpowers a ⊔ J = centralizer ({a} : Set Y)
  inf_eq : zpowers a ⊓ J = ⊥
  gl3 : Nonempty (J ≃* GL (Fin 3) (ZMod 2))

@[expose] def SourceExcluded (P : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (D : Subgroup Y) (a : Y) (J : Subgroup Y),
    GL3Source D a J → P D → False

@[expose] def ExcludedSource (T : Type) [Group T] : Prop :=
  SourceExcluded fun (D : Type) [Group D] => Nonempty (D ≃* T)

@[expose] def ExcludedLie (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ) : Prop :=
  SourceExcluded fun (D : Type) [Group D] => CFSG.Blueprint.LieModel D t n p f

structure SporadicExclusions : Prop where
  M22 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .M22)
  M23 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .M23)
  M24 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .M24)
  J2 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .J2)
  HS : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .HS)
  McL : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .McL)
  He : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .He)
  Suz : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .Suz)
  Co3 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .Co3)
  Co2 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .Co2)

structure OrthogonalExclusions : Prop where
  plus4 : ExcludedLie .POmegaPlus 4 2 1
  plus5 : ExcludedLie .POmegaPlus 5 2 1
  plus6 : ExcludedLie .POmegaPlus 6 2 1
  plus7 : ExcludedLie .POmegaPlus 7 2 1
  minus4 : ExcludedLie .POmegaMinus 4 2 1
  minus5 : ExcludedLie .POmegaMinus 5 2 1
  minus6 : ExcludedLie .POmegaMinus 6 2 1

structure ClassicalExclusions : Prop where
  psu35 : ExcludedLie .PSU 3 5 1
  psp47 : ExcludedLie .PSp 2 7 1

structure ExceptionalExclusions : Prop where
  g2four : ExcludedLie .G2 0 2 2
  d4two : ExcludedLie .trialityD4 0 2 1
  f4two : ExcludedLie .F4 0 2 1
  e6two : ExcludedLie .E6 0 2 1
  g2three : ExcludedLie .G2 0 3 1

structure CharThreeExclusions : Prop where
  psu33 : ExcludedLie .PSU 3 3 1
  psu43 : ExcludedLie .PSU 4 3 1
  psl39 : ExcludedLie .PSL 3 3 2

structure ResidualExclusions : Prop where
  sporadic : SporadicExclusions
  orthogonal : OrthogonalExclusions
  classical : ClassicalExclusions
  exceptional : ExceptionalExclusions
  charThree : CharThreeExclusions

structure ResidualExclusionsNine : Prop where
  plus4 : ExcludedLie .POmegaPlus 4 2 1
  minus4 : ExcludedLie .POmegaMinus 4 2 1
  plus5 : ExcludedLie .POmegaPlus 5 2 1
  psu33 : ExcludedLie .PSU 3 3 1
  J2 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .J2)
  He : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .He)

end CFSG.EvenSmallLie.Child3
