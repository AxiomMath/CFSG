module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

private lemma add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma eq_of_add_eq_zero_V6 {u c : V6} (h : u + c = 0) : u = c := by
  calc u = u + 0 := (add_zero u).symm
    _ = u + (c + c) := by rw [add_self_eq_zero_V6]
    _ = (u + c) + c := (add_assoc u c c).symm
    _ = 0 + c := by rw [h]
    _ = c := zero_add c

private lemma coordElt_inv (ι : Elem2 6 →* G) (v : V6) : (coordElt ι v)⁻¹ = coordElt ι v := by
  apply inv_eq_of_mul_eq_one_right
  rw [← coordElt_add, add_self_eq_zero_V6, coordElt_zero]

end CFSG.EvenSporadicStandard.HNRecog.Harada
