module

public import CFSG.GH74.Uniqueness.SU.SU9L196
public import CFSG.GH74.Uniqueness.SU.SU9L197
public import CFSG.GH74.Uniqueness.SU.SU9End

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU7

theorem sec19_false_of_stmts (h191 : Lemma191Stmt) (h192 : Lemma192Stmt)
    (h194 : Lemma194Stmt) (h195 : Cor195Stmt)
    (h196c : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
      (A B R : Subgroup G), Ctx19 S U M V x z A B R → ∀ a ∈ A, a ∉ U →
        Nonempty (↥(centralizer ({a} : Set G)) ≃*
            alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
          (commutator ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype = U) :
    Sec19FalseStmt :=
  sec19_false h192 h194 (lemma197 h191 h192 h194 (lemma196 h191 h194 h195 h196c))

end CFSG.GH74.Uniqueness.SU.SU9
