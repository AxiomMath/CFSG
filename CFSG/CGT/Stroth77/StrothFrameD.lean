module

public import CFSG.CGT.Stroth77.StrothFrame

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

structure StrothFrame.IsD (F : StrothFrame G) (D : Subgroup G) {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) : Prop where
  A_le : F.A ≤ D
  le_S : D ≤ (F.S : Subgroup G)
  uv_eq : dD.uv = F.dA.uv
  t_eq : dD.t = F.dA.t
  u_eq : dD.u = F.dA.u
  ρ_eq : dD.ρ = F.dA.ρ
  cent : (F.S : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) = D

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem L_eq (h : F.IsD D dD) : dD.L = F.dA.L := by
  rw [StrothWeakTypeData.L, StrothWeakTypeData.L, h.uv_eq, h.t_eq, h.u_eq, h.ρ_eq]

theorem inf_E (h : F.IsD D dD) :
    D ⊓ F.E = Subgroup.closure {((F.dA.a : F.A) : G) ^ 2, ((F.dA.b : F.A) : G) ^ 2} :=
  F.inf_E dD.isMulCommutative h.A_le

theorem mem_of_mem_centralizer (h : F.IsD D dD) {x : G} (hxS : x ∈ (F.S : Subgroup G))
    (hx : x ∈ Subgroup.centralizer (D : Set G)) : x ∈ D := by
  rw [← h.cent]
  exact ⟨hxS, hx⟩

end StrothFrame.IsD

end CFSG.CGT.Stroth77
