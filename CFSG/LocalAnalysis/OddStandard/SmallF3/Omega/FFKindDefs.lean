module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def KM0 (x : ProjSim Q) : Prop := SimHasType x 4 1

@[expose] def KM1 (x : ProjSim Q) : Prop := SimHasType x 2 (-1)

@[expose] def KM2 (x : ProjSim Q) : Prop := ∃ α : ℤˣ, SimHasType x 1 α

@[expose] def KM3 (x : ProjSim Q) : Prop := ∃ α : ℤˣ, SimHasType x 3 α

@[expose] def KM4 (x : ProjSim Q) : Prop := ¬ SimInGStar x

@[expose] noncomputable def ffFix (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (x : ProjSim Q) : Subgroup ↥(omegaProj hQ) :=
  fixSub (ffSimOmegaAct hQ h2 x)

end Model

@[expose] def ffX (B : Type) [Group B] : Subgroup B :=
  twoPrimeRes (twoRes (⊤ : Subgroup B))

@[expose] def XTwoCore (A : Type) [Group A] : Prop :=
  ffX A = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup A))

@[expose] def LayerModel (B : Type) [Group B] (t : CFSG.Open.StatedLieTag) (n k : ℕ) : Prop :=
  ∃ (E : Subgroup B) (_ : E.Normal), LieModel ↥E t n 3 k ∧ IsPGroup 2 (B ⧸ E)

section Invariants

variable {G : Type} [Group G]

@[expose] def DInv (L : Subgroup G) (s : G) : ℕ → Prop
  | 0 => InnerOn L s ∧ s ∉ centralizer (L : Set G) ∧
      Group.IsSolvable ↥(L ⊓ centralizer ({s} : Set G))
  | 1 => InnerOn L s ∧ s ∉ centralizer (L : Set G) ∧ IsL29 (layerCent L s) ∧
      XOut L s = layerCent L s
  | 2 => ¬ InnerOn L s ∧ IsOmega5 (layerCent L s) ∧ XOut L s = layerCent L s
  | 3 => ¬ InnerOn L s ∧ Group.IsSolvable ↥(L ⊓ centralizer ({s} : Set G))
  | _ => ¬ InnerOn L s ∧ (IsL3Eps3 (layerCent L s) ∨ IsL29 (layerCent L s)) ∧
      XOut L s = layerCent L s

end Invariants

end CFSG.OddStandard.SmallF3.Omega
