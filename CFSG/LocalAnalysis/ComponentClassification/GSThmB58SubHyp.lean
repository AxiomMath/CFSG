module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubStd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubL9

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

@[expose] noncomputable def subHyp52 (hc : h.SecCond y) (S' : Subgroup ↥(h.secSubImg y))
    (hS'le : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
      normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))
    (hS'syl : ∃ R : Sylow 2 ↥(centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))),
      (R : Subgroup _) = S'.subgroupOf (centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))))
    (hSS' : h.subS y ≤ S')
    (h7 : ∀ E : Subgroup ↥(h.secSubImg y), E ≤ S' ⊓ coreActionKernel (h.subJ y) →
      (Nat.card (h.subB y) < Nat.card E ∨ (Nat.card E = Nat.card (h.subB y) ∧
        Nat.card ↥(S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
          Set ↥(h.secSubImg y))) < Nat.card ↥(S' ⊓ normalizer (E : Set ↥(h.secSubImg y))))) →
      ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L) :
    Hyp52 ↥(h.secSubImg y) where
  a := hc.subA
  J := h.subJ y
  S := S'
  B := h.subB y
  K := h.subK y
  x := hc.subX
  kProper := kProper_subBar
  kGroup_normalizer := hc.kGroup_normalizer_subB
  normalizer_ne_top := hc.normalizer_subB_ne_top
  orderOf_a := hc.orderOf_subA
  J_le := hc.subJ_le
  isPComponent_J := hc.isPComponent_subJ
  smallType := smallType_subJ
  S_le := hS'le
  S_sylow := hS'syl
  B_le := subB_le.trans (inf_le_inf_right _ hSS')
  B_ne_bot := hc.subB_ne_bot
  a_mem_normalizer := hc.subA_mem_normalizer
  isComponent_bar := hc.isComponent_subBar
  isStandard_bar := hc.isStandard_subBar
  conjClosure_eq := hc.conjClosure_subW
  commutator_eq := hc.commutator_subW
  B_le_kernel := hc.subB_le_kernel
  B_sylow_kernel := hc.subB_sylow_kernel
  isoCorr_of_lt := h7
  x_mem := hSS' hc.subX_mem
  inf_conjugate_x := hc.subB_inf_conjugate
  x_sq_mem := inf_le_inf_right _ (inf_le_inf_right _ hSS') hc.subX_sq_mem
  sylow_layer := by
    rw [hc.layerIn_subW]
    obtain ⟨R, hR1, hR2, hR3⟩ := hc.sylow_layer_subBar
    exact ⟨R, hR1.trans (inf_le_inf_right _ hSS'), hR2, hR3⟩
  isPComponent_K := hc.isPComponent_subK
  layer_eq_K := hc.layer_eq_subK
  type_K := hc.type_subK

end Hyp52

end CFSG.ComponentClassification.GSThmB
