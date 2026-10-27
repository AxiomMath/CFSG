module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type*} [Group G]

@[expose] def Rsub (S : Subgroup G) (a b : G) : Subgroup G :=
  Subgroup.closure {c : G | c ∈ S ∧ c * c = a ^ 2 * b ^ 2}

@[expose] def R1sub (a b y : G) : Subgroup G := Subgroup.closure ({a⁻¹ * b, a * b * y} : Set G)

structure Lemma14_3Conc (G : Type*) [Group G] (z : G) (R R₁ : Subgroup G) : Prop where
  R_normal : (R.subgroupOf (centralizer ({z} : Set G))).Normal
  quot_S3 : Nonempty (↥(centralizer ({z} : Set G)) ⧸ R.subgroupOf (centralizer ({z} : Set G))
    ≃* Equiv.Perm (Fin 3))
  cent_X : ∀ X : Sylow 3 ↥(centralizer ({z} : Set G)),
    ∀ r ∈ R.subgroupOf (centralizer ({z} : Set G)), (∀ w ∈ X, w * r = r * w) →
      (r : G) ∈ zpowers z
  R₁_normal : (R₁.subgroupOf (centralizer ({z} : Set G))).Normal

end CFSG.GH74.GLS.Stage1.Thm6.Sec14
