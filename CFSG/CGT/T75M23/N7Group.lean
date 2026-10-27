module

public import CFSG.CGT.T75M23.M23PresInputs
public import Mathlib.GroupTheory.FreeGroup.Reduce

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable

abbrev N7 : Type := PG 6 rels7

@[expose] def n7 (w : List (Fin 6 × Bool)) : N7 := PresentedGroup.mk _ (FreeGroup.mk w)

theorem n7_nil : n7 [] = 1 := by
  rw [n7]; exact map_one _

theorem n7_append (w w' : List (Fin 6 × Bool)) : n7 (w ++ w') = n7 w * n7 w' := by
  rw [n7, n7, n7, ← map_mul, FreeGroup.mul_mk]

theorem n7_singleton (i : Fin 6) (b : Bool) :
    n7 [(i, b)] = if b then PresentedGroup.of i else (PresentedGroup.of i)⁻¹ := by
  cases b
  · show PresentedGroup.mk _ (FreeGroup.mk [(i, false)]) = _
    rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv]; rfl
  · rfl

theorem n7_invWord (w : List (Fin 6 × Bool)) : n7 (invWord7 w) = (n7 w)⁻¹ := by
  rw [n7, n7, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, invWord7, List.map_reverse]

theorem n7_exists_word (g : N7) : ∃ w : List (Fin 6 × Bool), g = n7 w := by
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective _ g
  exact ⟨x.toWord, by rw [n7, FreeGroup.mk_toWord]⟩

end CFSG.CGT.T75M23
