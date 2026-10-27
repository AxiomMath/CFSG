module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def IVK_4_7e : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p n : ℕ), p.Prime → p ≠ 2 →
    (LieModel K .G2 0 p n ∨ LieModel K .trialityD4 0 p n) → ∀ P : Sylow p K,
      Subgroup.closure {x : K | x ∈ (P : Subgroup K) ∧ x ^ p = 1} = (P : Subgroup K) ∧
      (LieModel K .G2 0 p n → Nat.card ↥(P : Subgroup K) = (p ^ n) ^ 6)

@[expose] def IVK_4_7f : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), LieModel K .G2 0 3 n → ∀ P : Sylow 3 K,
    IsElementaryAbelian 3 ↥(Subgroup.center ↥(P : Subgroup K)) ∧
      Nat.card ↥(Subgroup.center ↥(P : Subgroup K)) = (3 ^ n) ^ 2

@[expose] def IVK_4_7ef : Prop := IVK_4_7e ∧ IVK_4_7f

end CFSG.GH74.GLS.IVK
