module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec128Inv {G : Type} [Group G] (V : Subgroup G) (Y Xt : Subgroup (MulAut ↥V))
    (τ : MulAut ↥V) : Prop where
  xy : Xt ≤ Y
  ty : τ ∈ Y
  sq : τ * τ = 1
  ne : τ ≠ 1
  a5 : Nonempty (↥Xt ≃* ↥(alternatingGroup (Fin 5)))
  tx : τ ∉ Xt
  comm : ∀ x ∈ Xt, τ * x = x * τ
  cases : ∀ y ∈ Y, y * τ = τ * y → y ∈ Xt ∨ ∃ x ∈ Xt, y = τ * x
  cent : Nonempty (↥(Y ⊓ Subgroup.centralizer ({τ} : Set (MulAut ↥V))) ≃*
    (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))))
  fus : ∀ y : MulAut ↥V,
    ((∃ b ∈ Y, y = b * τ * b⁻¹) ∧ y ∈ Subgroup.centralizer ({τ} : Set (MulAut ↥V))) ↔
      ((∃ x ∈ Xt, y = τ * x) ∧ y * y = 1 ∧ y ≠ 1)

end CFSG.OddStandard.SmallF3.Omega
