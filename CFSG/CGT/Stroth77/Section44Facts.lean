module

public import CFSG.CGT.Stroth77.Section44
public import CFSG.CGT.Stroth77.Section44CoreA

public section

namespace CFSG.CGT.Stroth77

open Stroth44Core

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.IsD.false_of_t201_A {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (hE : ∀ y ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1)))
    (hu : IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)))
    (hzu : IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) : False := by
  have hm := Stroth44.one_le h
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le Subgroup.le_normalizer dD.closure_le_normalizer
  have htS : dD.t ∈ (F.S : Subgroup G) := h.t_eq ▸ F.t_mem_S
  refine h.false_of_t201_noE16 hnc hSD hE hu hzu (t201_h3 dD hm) ?_ ?_ (t201_hl' dD h.le_S)
    (t201_hx2 dD hm) (t201_hxl dD hm) (t201_hxlu' dD hm h.le_S htS) (t201_hx16 dD hm) ?_ ?_
  · rw [hS]; exact t201_hC2 dD hm
  · rw [hS]; exact t201_hC2c dD hm
  · rw [hS]; exact t201_h7 dD hm
  · rw [hS]; exact t201_h9 dD hm

end CFSG.CGT.Stroth77
