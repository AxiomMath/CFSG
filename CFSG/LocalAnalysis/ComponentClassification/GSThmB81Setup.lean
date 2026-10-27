module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81KLoc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Pre
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsB
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step2a

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H]

structure L81Hyp (h : Hyp59 H) : Prop where
  kOrSimple : SectionRank.IsKGroupCat H ∨ IsSimpleGroup H
  case8 : h.Sec8Case
  eight_le : 8 ≤ Nat.card h.P
  NP_eq : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧ ∀ b ∈ h.B, b * h.a = h.a * b
  C_eq : h.P ⊓ centralizer (h.S : Set H) = zpowers h.a
  J_normal : (h.J.subgroupOf (centralizer ({h.a} : Set H))).Normal
  S_sylow_C : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set H)),
    (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set H))
  B_sylow_kernel : h.B ≤ coreActionKernel h.V ∧ ∃ R : Sylow 2 ↥(coreActionKernel h.V),
    (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V)
  center_J : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥

theorem L81Hyp.of_inputs (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center)
    (hCFi : CFProp23IndexReduced) {h : Hyp59 H}
    (hKS : SectionRank.IsKGroupCat H ∨ IsSimpleGroup H) (hc : h.Sec8Case)
    (hP : 8 ≤ Nat.card h.P) : h.L81Hyp where
  kOrSimple := hKS
  case8 := hc
  eight_le := hP
  NP_eq := h.toHyp52.normalizer_P_eq hCFi (h.toHyp52.sec8Case_table517 hc)
  C_eq := h.toHyp52.centralizer_P_eq hB1 hCF23 hCFc
  J_normal := (normal_subgroupOf_iff_le_normalizer h.J_le).mpr
    (h.toHyp52.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc)
  S_sylow_C := (h.toHyp52.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc).2
  B_sylow_kernel := hB6 H h.toHyp52
  center_J := h.toHyp52.center_eq_bot hB1 hB6 hCF23 hCF24

variable {h : Hyp59 H}

namespace L81Hyp

variable (H₁ : L81Hyp h)
include H₁

theorem card_quot_T : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2 := by
  have hT := h.toHyp52.card_T H₁.NP_eq
  have hBT : h.B ≤ h.T := h.toHyp52.B_le_T'
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.B.subgroupOf h.T)
  rw [Six.card_subgroupOf_eq, inf_eq_left.mpr hBT, hT] at h1
  have hpos : 0 < Nat.card h.B := Nat.card_pos
  have h2 : 2 * Nat.card h.B = Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) * Nat.card h.B := h1
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem exists_b : ∃ b : H, h.B = zpowers b ∧ orderOf b = 2 ∧ Nat.card h.T = 4 ∧
    h.T = zpowers h.a ⊔ zpowers b ∧ h.T = h.P ⊓ centralizer ({b} : Set H) :=
  h.index_two_structure embedsTQuotStatement H₁.card_quot_T

theorem kloc : h.toHyp52.KLoc where
  case8 := H₁.case8
  B_eq := by
    obtain ⟨b, hBb, hb, -⟩ := H₁.exists_b
    exact ⟨b, hBb, hb⟩
  C_eq := H₁.C_eq
  J_normal := H₁.J_normal
  B_sylow_kernel := H₁.B_sylow_kernel

theorem x_mem_P : h.x ∈ h.P ⊓ normalizer (h.Q : Set H) := by
  rcases h.x_cond with hx | ⟨hPQ, -⟩
  · exact hx
  · exfalso
    obtain ⟨-, -, -, hT4, -, -⟩ := H₁.exists_b
    have hPT : h.P ≤ h.T := fun y hy => mem_inf.mpr ⟨hPQ hy, hy⟩
    have := card_le_of_le hPT
    have h8 := H₁.eight_le
    omega

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
