module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridge
public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeWt
public import CFSG.LocalAnalysis.OddStandard.Seitz77WData
public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocal

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

structure Sit27 {G : Type} [Group G] [Finite G] (A R X O Sy Wt : Subgroup G) (t : G) : Prop where
  S : IsSetting25 A R t X O
  F : ActionFacts A R
  hSy : IsSylowOf 2 Sy (normalizer ((R ⊔ zpowers t : Subgroup G) : Set G))
  hWt : WtSpec R t X O Wt

section Exists

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ W : Subgroup G}

theorem Hyp.exists_sit27
    (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∃ X O Sy Wt : Subgroup G, Sit27 A W X O Sy Wt d.t ∧
      ∃ w : WData d W, w.S = Sy ∧ w.W = Sy ⊓ Wt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨pl⟩ := h.exists_PlaneData d hR hW
  have S := IsSetting25.ofPlaneData h d hR hW pl
  have hnorm : (pl.O.subgroupOf pl.X).Normal := S.normal_subgroupOf
  obtain ⟨L⟩ := h.exists_leviData d hR hW
  have F : ActionFacts A W := h.actionFacts d hR hW
  obtain ⟨Wb, hidx, helem, hVWb, htWb, hchar, -, hdel⟩ := Config25.exists_W (S.config25 L F)
  have hWt := S.wtSpec_of_wbar Wb hchar helem hidx hVWb htWb hdel
  obtain ⟨Sy, hSy⟩ := exists_isSylowOf 2 (normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G))
  refine ⟨pl.X, pl.O, Sy, preimageX pl.X pl.O Wb, ⟨S, F, hSy, hWt⟩, ?_⟩
  exact ⟨{ S := Sy
           W := Sy ⊓ preimageX pl.X pl.O Wb
           hS := hSy
           hWS := inf_le_left
           hWnormal := IsSetting25.normal_inf_Wt hSy hWt
           hW_elem := S.elem_inf_Wt hSy hWt
           hW_card := S.card_inf_Wt hSy hWt
           hV₁W := S.W_le_inf_Wt hSy hWt
           hV₁_card := S.W_card
           ht_mem := S.E_le_sylow hSy (mem_sup_right (mem_zpowers _))
           ht_not_mem := IsSetting25.t_not_mem_inf_Wt hWt
           hCt := S.inf_Wt_inf_centralizer_t hSy hWt
           hComm := S.commutator_inf_Wt hSy hWt
           hY := S.Sy_inf_centralizer_W hSy hWt
           hR1 := S.relIndex_inf_Wt hSy hWt F
           hR2 := S.card_fix_inf_Wt hSy hWt F }, rfl, rfl⟩

end Exists

end CFSG.OddStandard.Seitz77
