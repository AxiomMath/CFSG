module

public import CFSG.Quasithin.H13.L32AC40b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}

theorem relIndex_R1_T_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) : (pCoreOf 2 (l1 T L V ⊔ T)).relIndex T = 2 := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  exact hl1eq ▸ S14.index2_eq_F4

theorem card_map_T_F4 {W : Type*} [Group W] (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) (hTH : T ≤ H) (Ψ : ↥H →* W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    Nat.card ↥((T.subgroupOf H).map Ψ) =
      2 * Nat.card ↥(((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf H).map Ψ) := by
  have hRT := Setting147.R1_le_T S
  have hQR := Setting147.O2H_le_R1 S
  rw [card_map_eq_relIndex Ψ hker hTH, card_map_eq_relIndex Ψ hker (hRT.trans hTH),
    ← Subgroup.relIndex_mul_relIndex _ _ _ hQR hRT, relIndex_R1_T_F4 h1222 h1332 h1334 S, mul_comm]

end CFSG.Quasithin.H13.L32A.C
