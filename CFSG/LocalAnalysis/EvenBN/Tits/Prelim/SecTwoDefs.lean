module

public import CFSG.Open.FusionDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open
open scoped MatrixGroups

instance secTwo_standardComponentOddCore_normal (X : Type*) [Group X] :
    (standardComponentOddCore X).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def secTwoR {X : Type*} [Group X] (t u : X) : Subgroup X :=
  closure {t, u}

structure SecTwoHyp (X : Type*) [Group X] (t u : X) : Prop where
  orderOf_t : orderOf t = 2
  orderOf_u : orderOf u = 4
  commute : t * u = u * t
  sq_ne : u ^ 2 ≠ t
  sylow : fusionIsSylowIn 2 (secTwoR t u) (centralizer ({t} : Set X))

@[expose] def WreathS3CaseIn (G : Type*) [Group G] (z : G) : Prop :=
  ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧ Nat.card A = 16 ∧ (∀ a ∈ A, a ^ 4 = 1) ∧
    centralizer (A : Set G) ≤ A ∧ z ∈ A ∧
    (∀ a ∈ A, a ^ 2 = 1 → a ≠ 1 → ∃ g : G, g * z * g⁻¹ = a) ∧ ∀ P : Sylow 2 G, Nat.card P = 32

@[expose] def PGLTwoSquareOuter {G : Type*} [Group G] (J : Subgroup G) (t : G) : Prop :=
  J.Normal ∧ centralizer (J : Set G) = ⊥ ∧
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (q : ℕ), Odd q ∧ Fintype.card F = q ^ 2 ∧
      ∃ (e : J ≃* PSL(2, F)) (g : PGL(2, F)),
        g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
        ∀ x y : J, (y : G) = t * x * t⁻¹ →
          Matrix.ProjectiveSpecialLinearGroup.toPGL (e y) =
            g * Matrix.ProjectiveSpecialLinearGroup.toPGL (e x) * g⁻¹

end CFSG.LocalAnalysis.EvenBN.Tits
