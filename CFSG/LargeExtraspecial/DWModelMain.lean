module

public import CFSG.LargeExtraspecial.DWTransFaith
public import CFSG.LargeExtraspecial.DWTransGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module CFSG.GroupTheory.GLnTwoSplitting
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem nonempty_centralizer_mulEquiv (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G)) (hsurj : Function.Surjective (conjLinear (AN A))) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) :=
  nonempty_centralizer_mulEquiv_of_surjective A hA.card_eq (by omega)
    (hA.centralizer_eq hM).le hsurj hA.z_mem S.z_ne_one hM

theorem nonempty_centralizer_mulEquiv_of_conj (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G))
    (hi : A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d})
    (hii : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) :=
  hA.nonempty_centralizer_mulEquiv h5 hM (hA.conjLinear_surjective_of_conj hi hii)

end MaxEA

end CFSG.LargeExtraspecial.DW
