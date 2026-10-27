module

public import CFSG.CGT.Stroth77.Section44
public import CFSG.CGT.Stroth77.Section44CoreIII
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.G23Facts

public section

namespace CFSG.CGT.Stroth77

open Stroth44Core

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.IsD.false_of_t201_iii' {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
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
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ → e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ →
      e * e = 1 → False := by
  intro e heN hS heuv het heu hec hea heb he2
  have hm := Stroth44.one_le h
  set hEa := dD.t201iiiAction heuv het heu hec hea heb he2
  have hφe : hEa.φe = torusDiag _ ![-1, -1, -1] := rfl
  have hve : hEa.ve = 0 := rfl
  have hwuv : hEa.wuv = Torus.ofInt _ ![2, 2, 2] := rfl
  have hwt : hEa.wt = Torus.ofInt _ ![0, -2, 0] := rfl
  have htS : dD.t ∈ (F.S : Subgroup G) := h.t_eq ▸ F.t_mem_S
  refine h.false_of_t201_iii hnc heN he2 hec hea heb heu hS hE hu hzu ?_
    (t201_iii_h2 dD hEa hm hφe) (t201_h3 dD hm) ?_ ?_ (t201_hl' dD h.le_S) (t201_hx2 dD hm)
    (t201_hxl dD hm) (t201_hxlu' dD hm h.le_S htS) (t201_hC7 dD hm) ?_ ?_ ?_ ?_
    (t201_hC13 dD hm) (t201_iii_hF dD hEa hm hφe hve hwuv)
  · rw [hS]; exact t201_iii_h1 dD hEa hm hφe
  · rw [hS]; exact t201_iii_hC2 dD hEa hm hφe hve hwuv hwt
  · rw [hS]; exact t201_e_hC2c dD hEa hm (t201_iii_φe_z dD hEa hm hφe)
  · rw [hS]; exact t201_iii_h9 dD hEa hm hφe
  · rw [hS]; exact t201_iii_hC15 dD hEa hm hφe hve
  · rw [hS]; exact t201_iii_hC11 dD hEa hm hφe hve hwuv hwt
  · rw [hS]; exact t201_iii_hue dD hEa hm hφe hve hwuv hwt

end CFSG.CGT.Stroth77
