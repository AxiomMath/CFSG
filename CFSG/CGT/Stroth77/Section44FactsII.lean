module

public import CFSG.CGT.Stroth77.Section44
public import CFSG.CGT.Stroth77.Section44CoreII

public section

namespace CFSG.CGT.Stroth77

open Stroth44Core

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.IsD.false_of_t201_ii {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (hE : ∀ y ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1)))
    (hu : IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)))
    (hzu : IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1))) :
    ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = dD.c →
      e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1) →
      e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1) → e * e = (dD.c : G)⁻¹ → False := by
  intro e heN hS heuv het heu hec hea heb he2
  have hm := Stroth44.one_le h
  set hEa := dD.t201iAction heuv het heu hec hea heb he2
  have hφe : hEa.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] := rfl
  have hve : hEa.ve = Torus.ofInt _ ![-1, 0, 0] := rfl
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le (sup_le Subgroup.le_normalizer dD.closure_le_normalizer)
      ((Subgroup.zpowers_le).2 heN)
  have htS : dD.t ∈ (F.S : Subgroup G) := h.t_eq ▸ F.t_mem_S
  refine h.false_of_t201_noE16 hnc hSD hE hu hzu (t201_h3 dD hm) ?_ ?_ (t201_hl' dD h.le_S)
    (t201_hx2 dD hm) (t201_hxl dD hm) (t201_hxlu' dD hm h.le_S htS) (t201_hx16 dD hm) ?_ ?_
  · rw [hS]; exact t201_ii_hC2 dD hEa hm hφe
  · rw [hS]; exact t201_e_hC2c dD hEa hm (t201_ii_φe_z dD hEa hm hφe)
  · rw [hS]; exact t201_ii_h7 dD hEa hm hφe hve
  · rw [hS]; exact t201_ii_h9 dD hEa hm hφe

end CFSG.CGT.Stroth77
