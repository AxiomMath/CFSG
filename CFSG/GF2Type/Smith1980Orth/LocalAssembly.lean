module

public import CFSG.GF2Type.Smith1980Orth.PathGlue

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G]

@[expose] def OE23 (S : Setting G) : Prop :=
  ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
    x * y ∈ S.QG ∨ (x * y) ^ 2 ∈ S.QG ∨ (x * y) ^ 3 ∈ S.QG ∨ (x * y) ^ 4 ∈ S.QG

@[expose] def OE44 (S : Setting G) : Prop :=
  ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
    (x * y) ^ 2 ∉ S.QG → (x * y) ^ 4 ∈ S.QG →
      orderOf (x * y) = 4 ∧ IsConj S.z ((x * y) ^ 2)

theorem oLocal_of (S : Setting G) (h34a : OE34a S) (h24 : OE24 S) (h25 : OE25 S)
    (h23 : OE23 S) (h44 : OE44 S) : OLocal S := by
  intro x y hx hy hxM hyM hxQ
  have h34b := oe34b_of S h34a
  by_cases hyQ : y ∈ S.QG
  · exact local_of_mem_QG' S h34a h24 hx hy hxM hxQ hyQ
  by_cases h1 : x * y ∈ S.QG
  · exact local_of_mul_mem' S h34a h34b hx hy hxM hyM hxQ hyQ h1
  by_cases h2 : (x * y) ^ 2 ∈ S.QG
  · exact local_of_sq_mem' S h34a h34b h25 hx hy hxM hyM hxQ hyQ h1 h2
  by_cases h3 : (x * y) ^ 3 ∈ S.QG
  · exact local_of_cube_mem' S h34a h34b h25 hx hy hxM hyM hxQ hyQ h1 h3
  rcases h23 x y hx hy hxM hyM hxQ hyQ with h | h | h | h4
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  obtain ⟨hord, hc⟩ := h44 x y hx hy hxM hyM hxQ hyQ h2 h4
  exact ⟨by rw [hord]; simp, fun _ => hc⟩

end CFSG.GF2Type.Smith1980Orth
