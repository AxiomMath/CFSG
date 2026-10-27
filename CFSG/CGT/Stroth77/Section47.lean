module

public import CFSG.CGT.Stroth77.L4Sylow.Recognition
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs
public import CFSG.CGT.Stroth77.StrothFrame

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.YamadaG23

variable {G : Type} [Group G] [Finite G]

@[expose] def Stroth47Conclusion (F : StrothFrame G) (D : Subgroup G) {m : ℕ}
    (dD : StrothWeakTypeData D (.t200 m)) : Prop :=
  (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}


@[expose] def L4Sylow.L4Frame.ofStrothWeakTypeData {G : Type*} [Group G] {D : Subgroup G}
    {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) : L4Sylow.L4Frame D m where
  e := dD.e
  uv := dD.uv
  t := dD.t
  u := dD.u
  uv_mem := dD.uv_mem
  t_mem := dD.t_mem
  u_mem := dD.u_mem
  uv_conj := dD.uv_conj
  t_conj := dD.t_conj
  u_conj := dD.u_conj
  uv_sq := dD.uv_sq
  t_sq := dD.t_sq
  u_sq := dD.u_sq
  uv_comm_u := dD.uv_comm_u
  t_u := dD.t_u

theorem strothL4_of_stroth47 {m : ℕ} (hm : 1 ≤ m) (F : StrothFrame G) {D : Subgroup G}
    (dD : StrothWeakTypeData D (.t200 m)) (h47 : Stroth47Conclusion F D dD)
    (hMason : ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
      Nonempty (↥P ≃* L4Sylow.L4Model n) → LitPSLU4S G) :
    LitPSLU4S G := by
  refine hMason (n := m + 2) (by omega) F.S ?_
  have hS : D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} = (F.S : Subgroup G) := h47.symm
  exact L4Sylow.L4Frame.nonempty_mulEquiv_l4Model
    (L4Sylow.L4Frame.ofStrothWeakTypeData dD) hm hS


theorem litStrothType_of_stroth47 {m : ℕ} (hm : 1 ≤ m) (F : StrothFrame G) {D : Subgroup G}
    (dD : StrothWeakTypeData D (.t200 m)) (h47 : Stroth47Conclusion F D dD)
    (hMason : ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
      Nonempty (↥P ≃* L4Sylow.L4Model n) → LitPSLU4S G) :
    LitStrothType G :=
  Or.inr (Or.inl (strothL4_of_stroth47 hm F dD h47 hMason))


end CFSG.CGT.Stroth77
