module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt6_2_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (V : Set G) ≤ M

@[expose] def Stmt6_2_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    Nonempty (↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) ∧
    Nat.card (quasithinOmegaOneCenter T) = 2 ∧
    ¬ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M

@[expose] def Stmt6_2_5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    let IsType3 := fun F : Subgroup G =>
      F ≤ V ∧ Nat.card F = 4 ∧ ¬ IsCentralType L V F 1 ∧ ¬ IsFieldType M L V F 1
    ((autOn L V).relIndex (autOn (ch6MV M V) V) = 6 → ∀ F : Subgroup G, ¬ IsType3 F) ∧
    ((autOn L V).relIndex (autOn (ch6MV M V) V) = 2 →
      Nat.card {F : Subgroup G // IsType3 F} = 20 ∧
      ∀ F F' : Subgroup G, IsType3 F → IsType3 F' →
        ∃ m ∈ ch6MV M V, F' = conjSubgroup F m) ∧
    (∀ F F' : Subgroup G,
      ((IsCentralType L V F 1 ∧ IsCentralType L V F' 1) ∨
        (IsFieldType M L V F 1 ∧ IsFieldType M L V F' 1) ∨ (IsType3 F ∧ IsType3 F')) →
      ∃ m ∈ ch6MV M V, F' = conjSubgroup F m) ∧
    (∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, conjSubgroup F g ≤ V →
      ∃ x ∈ ch6MV M V, conjSubgroup F g = conjSubgroup F x) ∧
    (∀ g : G, ch6ZS T L V ≤ conjSubgroup V g → conjSubgroup V g = V) ∧
    (∀ g : G, ¬ IsCyclic ↥(V ⊓ conjSubgroup V g) → ⁅V, conjSubgroup V g⁆ = ⊥) ∧
    ∀ Y : Subgroup G, Y ≤ V → Y.relIndex V = 2 → ∀ g : G, Y ≤ conjSubgroup V g →
      conjSubgroup V g = V

@[expose] def Stmt6_2_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ∀ g : G,
      let A := conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)
      let U := V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)
      A.relIndex (conjSubgroup V g) = 2 → U.relIndex V = 2 →
      ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 2 ∧
          (U ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)).relIndex U = 2 ∧
          IsFieldType M L V (A ⊓ Subgroup.centralizer (V : Set G)) g ∧
          IsFieldType M L V (U ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) 1 ∧
          IsPGroup 2 ↥(V ⊔ conjSubgroup V g)) ∨
      ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 4 ∧
          IsElemAbelianMod A (A ⊓ Subgroup.centralizer (V : Set G)) ∧
          ¬ autOn A V ≤ autOn L V ∧
          (∃ D : Subgroup G, D ≤ V ⊔ conjSubgroup V g ∧
            V ⊔ conjSubgroup V g ≤ Subgroup.normalizer (D : Set G) ∧
            E2.IsExtraspecialPlus 2 D ∧
            ∃ φ : ↥(V ⊔ conjSubgroup V g) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
              φ.ker = D.subgroupOf (V ⊔ conjSubgroup V g)) ∧
          V ⊓ conjSubgroup V g = ⁅A, U⁆ ∧ Nat.card ↥(V ⊓ conjSubgroup V g) = 2 ∧
          pCoreOf 2 (V ⊔ conjSubgroup V g) ≤ oTwoUpper (V ⊔ conjSubgroup V g))

@[expose] def Stmt6_2_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    wClos V 0 T ≤ ch6Q T V ∧ ch6Q T V = pCoreOf 2 (L ⊔ T) ∧
      Subgroup.normalizer (wClos V 0 T : Set G) ≤ M

@[expose] def Stmt6_2_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ¬ V ≤ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))

@[expose] def Stmt6_2_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    let H := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
    let K := conjClosure V H
    H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) ∧
      H ⊓ Subgroup.normalizer (V : Set G) = H ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
      K ⊓ M = K ⊓ Subgroup.normalizer (V : Set G) ∧
      K ⊓ Subgroup.normalizer (V : Set G) = K ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)

@[expose] def Stmt6_2_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    let Z := quasithinOmegaOneCenter T
    let H := Subgroup.centralizer (Z : Set G)
    let U := conjClosure (ch6ZS T L V) H
    (QuasithinUnique.CharTwo H ∧ U ≤ pCoreOf 2 H ∧ ⁅U, pCoreOf 2 H⁆ ≤ Z) ∧
    (centralizerMod Z H U ≤ Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (V : Set G) ≤ M ∧ V ⊓ centralizerMod Z H U ≤ pCoreOf 2 H) ∧
    IsO2Trivial H (centralizerMod Z H U) ∧
    ¬ V ≤ centralizerMod Z H U ∧
    ⁅V, U⁆ ≤ V ⊓ U

@[expose] def Stmt6_2_11_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    let Z := quasithinOmegaOneCenter T
    let H := Subgroup.centralizer (Z : Set G)
    (V ⊓ centralizerMod Z H (conjClosure (ch6ZS T L V) H)).relIndex V = 2

@[expose] def Stmt6_2_12_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    let Z := quasithinOmegaOneCenter T
    let H := Subgroup.centralizer (Z : Set G)
    let U := conjClosure (ch6ZS T L V) H
    (oTwoUpper (H ⊓ M) ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
      M ⊓ Subgroup.centralizer (V : Set G) ≤ centralizerMod (pCoreOf 2 L) M L) ∧
    (oTwoUpper (centralizerMod Z H U) = ⊥ ∧ centralizerMod Z H U = pCoreOf 2 H)

@[expose] def Stmt6_2_13_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ch6ZS T L V =
        V ⊓ conjClosure (ch6ZS T L V)
          (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →
      Nonempty (G ≃* NativeSporadic.M22)

@[expose] def Stmt6_2_19Sec2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    Nonempty (G ≃* NativeSporadic.M22)

@[expose] def Stmt6_2_19Case2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ¬ ch6ZS T L V <
      V ⊓ conjClosure (ch6ZS T L V) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))

end CFSG.Quasithin.H13
