module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1N

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}

theorem Wsub_sq [Finite G] (hS : Setup ε t L U Q P a ψ p) (hZ : ∀ v, v ∈ Zset t Q ψ)
    (hL9 : L9 t Q) : ∀ w ∈ hS.Wsub hZ, w * w = 1 :=
  hL9 _ (hS.Q_le_Wsub hZ) (hS.t_not_mem_Wsub hZ) (hS.card_Wsub hZ)
    (fun _ hx _ hy => hS.Wsub_comm hZ hx hy)
    (fun _ hn w hw => (mem_normalizer_iff.1 (hS.normalizer_E_le_normalizer_Wsub hZ hn) w).1 hw)

theorem exists_pointConfig [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hS : Setup ε t L U Q P a ψ p) (hL9 : L9 t Q) :
    ∃ W R : Subgroup G, PointConfig t L U Q P W R := by
  have hZ : ∀ v, v ∈ Zset t Q ψ := hS.mem_Zset hG hnab
  have hW2 := hS.Wsub_sq hZ hL9
  obtain ⟨X, hX⟩ := hS.exists_X hZ hW2
  exact ⟨hS.Wsub hZ, hS.Rsub hZ hW2 X,
    { shape := hS.shape
      Q_le := hS.rad.Q_le_L
      P_eq := hS.rad.P_eq
      U_le := hS.rad.U_le_P
      comm := fun _ hx _ hy => hS.Wsub_comm hZ hx hy
      sq_eq_one := hW2
      card_eq := hS.card_Wsub hZ
      Q_le_W := hS.Q_le_Wsub hZ
      R_le_W := hS.Rsub_le_Wsub hZ hW2 X
      inf_eq := hS.inf_Rsub hZ hW2 X
      sup_eq := hS.sup_Rsub hZ hW2 X
      t_not_mem := hS.t_not_mem_Wsub hZ
      t_mem_normalizer := hS.t_mem_normalizer_Wsub hZ
      P_le_normalizer := hS.P_le_normalizer_Wsub hZ
      P_le_normalizer_R := hS.P_le_normalizer_Rsub hZ hW2 hX
      commutator_mem := fun _ hr => hS.commutator_mem_Rsub hZ hW2 hr
      commutator_eq_one := fun _ hr h => hS.commutator_eq_one_Rsub hZ hW2 hr h
      sylow := hS.sylow_Wsub hZ hW2
      centralizer_t := fun _ hx hc => hS.mem_sup_of_comm hZ hW2 hx hc }⟩

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
