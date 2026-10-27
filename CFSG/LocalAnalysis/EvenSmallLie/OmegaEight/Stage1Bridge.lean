module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Main
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Final

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage2

variable {G : Type*} [Group G]

structure UGens (ε : Eps) (U Q : Subgroup G) (ψ : V6 → G) (u : Fin 6 → G) : Prop where
  u_mem : ∀ k, u k ∈ U
  u_act : ∀ k v, u k * ψ v * (u k)⁻¹ = ψ (toMat 6 6 (urRows ε k) *ᵥ v)
  U_le : U ≤ closure ((Q : Set G) ∪ Set.range u)

theorem bridgeCore_of_pointConfig {ε : Eps} {t : G} {L U Q P W R : Subgroup G} {a : G}
    {ψ : V6 → G} {p u : Fin 6 → G} (hC : PointConfig t L U Q P W R)
    (hR : RadicalData ε L U Q P a ψ p) (hu : UGens ε U Q ψ u) :
    BridgeCore t Q R W P U ψ (fun i : Fin 6 => genRows ε i) p (fun k : Fin 6 => urRows ε k) u where
  coord :=
    { comm := hC.comm
      sq_eq_one := hC.sq_eq_one
      card_eq := hC.card_eq
      Q_le_W := hC.Q_le_W
      R_le_W := hC.R_le_W
      inf_eq := hC.inf_eq
      sup_eq := hC.sup_eq
      t_mem := hC.t_mem_normalizer
      t_sq := hC.shape.mul_self
      Q_comm := fun _ hq => hC.shape.commute_of_mem (hC.Q_le hq)
      comm_mem := hC.commutator_mem
      comm_eq_one := hC.commutator_eq_one
      ψ_add := hR.ψ_add
      ψ_inj := hR.ψ_inj
      ψ_mem := hR.ψ_mem
      mem_ψ := hR.mem_ψ }
  orderOf_t := hC.shape.orderOf_eq
  P_le_normalizer := hC.P_le_normalizer
  P_le_normalizer_R := hC.P_le_normalizer_R
  P_le_centralizer := hR.P_le_L.trans hC.shape.le_centralizer
  p_mem := hR.p_mem
  p_act := hR.p_act
  P_le := hR.P_le
  U_le_P := hC.U_le
  u_mem := hu.u_mem
  u_act := hu.u_act
  U_le := hu.U_le
  TH_pgroup := hC.shape.isPGroup_sup hR.U_le_L hR.U_pgroup
  TH_max := hC.shape.sylow
  sylow_W := hC.sylow
  centralizer_t := hC.centralizer_t

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}

theorem exists_bridgeCore [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hS : Setup ε t L U Q P a ψ p) (hL9 : L9 t Q) (hu : UGens ε U Q ψ u) :
    ∃ W R : Subgroup G, BridgeCore t Q R W P U ψ (fun i : Fin 6 => genRows ε i) p
      (fun k : Fin 6 => urRows ε k) u := by
  obtain ⟨W, R, hC⟩ := hS.exists_pointConfig hG hnab hL9
  exact ⟨W, R, bridgeCore_of_pointConfig hC hS.rad hu⟩

section Plus


theorem false_of_setup_plus [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hS : Setup .plus t L U Q P a ψ p) (hL9 : L9 t Q) (hu : UGens .plus U Q ψ u) : False := by
  obtain ⟨W, R, hB⟩ := hS.exists_bridgeCore hG hnab hL9 hu
  exact false_of_bridgeCore_plus hG hnab hB

end Plus

section Minus


theorem false_of_setup_minus [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hS : Setup .minus t L U Q P a ψ p) (hL9 : L9 t Q) (hu : UGens .minus U Q ψ u) : False := by
  obtain ⟨W, R, hB⟩ := hS.exists_bridgeCore hG hnab hL9 hu
  exact false_of_bridgeCore_minus hG hnab hB

end Minus

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
