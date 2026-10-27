module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndLinearCoords
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndLemmaE

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {d : YamadaData G}

@[expose] def Yamada53 (F : Type) [Field F] [Finite F] (d : YamadaData G) : Prop :=
  (∃ _ : (d.D₁.subgroupOf d.N₁).Normal, ∃ ψ : SL(4, F) →* d.N₁ ⧸ d.D₁.subgroupOf d.N₁,
    Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) → LinearCase F d.G₀

namespace YamadaSection4

variable (h : YamadaSection4 F d)
include h

theorem yamadaG0
    (h53 : Yamada53 F d) : YamadaG0 F d.L d.t d.S d.A₁ d.V₁ d.G₀ where
  setting := h.setting
  center_eq := h.center_eq
  lie := h.lie
  card_field := h.card_field
  order_t := h.order_t
  t_mem := h.t_mem
  kernel := h.kernel
  sylow := h.sylow
  card_normalizer := h.card_normalizer
  normalizer_center := h.normalizer_center
  V₁_normal := h.V₁_normal
  V₁_sq := h.V₁_sq
  V₁_fix := h.V₁_fix
  V₁_comm := h.V₁_center.trans (centralizer_le (h.P_H ▸ inf_le_left))
  L_le := h.L_le_G₀
  V₁_le := h.V₁_le_D₂.trans h.D₂_le_G₀
  t_normalizes := h.t_G₀
  normalizer_le := fun x hx => by
    obtain ⟨h1, h2⟩ := h.normalizer_S hx
    rw [h.G₀_eq]
    exact mem_normalizer_sup h1 h2
  odd_centralizer := h.odd_centralizer_G₀
  two_subgroup := ⟨d.P, h.P_le₁.trans (le_sup_left.trans h.G₀_eq.ge), h.isPGroup_P, h.card_P.ge⟩
  cases := by
    rcases h.type₁ with hL | hU
    · exact Or.inl (h53 hL)
    · exact Or.inr (h.unitaryCase hU)

theorem yamada53
    (hL44 : L44Input) : Yamada53 F d := fun hL => h.linearCase hL44 hL

theorem false_of_yamada_endgame
    (hL44 : L44Input) (hA : L64CentralizerInput)
    (hE : L64TransferInput) (hU : U62RankInput) : False :=
  false_of_yamadaG0 (h.yamadaG0 (h.yamada53 hL44)) hA hE hU

end YamadaSection4

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
