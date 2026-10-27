module

public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G] [Finite G]

@[expose] def FullCPsp4 (x : G) (q : ℕ) : Prop :=
  IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q)

@[expose] def FullCL4 (x : G) (q : ℕ) : Prop :=
  IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q ^ 2) ∨
    (q = 5 ∧ Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7)))

@[expose] def FullE (x : G) (T : Subgroup G) : Prop :=
  HasNormal2Compl (CxK x (Jx x)) ∧
    (IsCyclic ↥(T ⊓ CxK x (Jx x)) ∨ IsDihedral ↥(T ⊓ CxK x (Jx x)))

structure FullF (z x : G) (T : Subgroup G) : Prop where
  res : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
    pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T
  T₁ : ∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ x ∈ T₁ ∧ z ∈ T₁ ∧
    IsDihedral ↥T₁

@[expose] def FullG (x : G) : Prop :=
  ∀ P : Sylow 2 ↥(O2Of (centralizer ({x} : Set G))), IsDihedral ↥P

end CFSG.GH74.GLS.Stage2.Local.P27
