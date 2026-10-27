module

public import CFSG.LocalAnalysis.EvenBN.U5.LinModelFixed
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43OutGen
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43OutLayer

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem lin43o_R_inf_L₂ (c : d.CaseBData) {R : Subgroup G}
    (hR : IsSylowOf 2 R (normalizer (d.D : Set G))) (hSR : c.S ≤ R) : R ⊓ d.L₂ = c.S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact c.S_syl.eq_of_le (le_inf hSR c.S_syl.le) inf_le_right hR.isPGroup.to_inf_left

theorem lin43o_R_le_normalizer_S (k : d.Know12) (c : d.CaseBData) {R : Subgroup G}
    (hR : IsSylowOf 2 R (normalizer (d.D : Set G))) (hSR : c.S ≤ R) :
    R ≤ normalizer (c.S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRL₁ : R ≤ normalizer (d.L₁ : Set G) := hR.le.trans d.normalizer_D_le_normalizer_L₁
  have hS₁ : IsSylowOf 2 c.S d.L₁ := (k.s10_2 c.S c.S_syl c.P_le_S).2.2.2.2.2.2.1
  have hSL₁ : R ⊓ d.L₁ = c.S :=
    hS₁.eq_of_le (le_inf hSR hS₁.le) inf_le_right hR.isPGroup.to_inf_left
  exact Lin43Out.le_normalizer_of_inf_eq hRL₁ hSL₁

theorem lin43o_R_le_normalizer_E (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
    {R : Subgroup G} (hR : IsSylowOf 2 R (normalizer (d.D : Set G))) (hSR : c.S ≤ R) :
    R ≤ normalizer (d.E : Set G) := by
  obtain ⟨-, hEchar, -⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  exact fun r hr => Lin43Out.mem_normalizer_of_characteristic (lin_E_le_S hl k c) hEchar
    (lin43o_R_le_normalizer_S k c hR hSR hr)

theorem lin43o_ctx (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData) {R : Subgroup G}
    (hR : IsSylowOf 2 R (normalizer (d.D : Set G))) (hSR : c.S ≤ R) :
    Lin43Out.OutCtx d.L₂ d.E d.lin43oN R where
  EL := d.E_le_L₂
  LE := d.L₂_le_normalizer_E
  EN := Lin43Out.E_le_secCenter d.E_le_L₂ d.L₂_le_normalizer_E
  NL := d.lin43oN_le
  LN := fun g hg =>
    Lin43Out.mem_normalizer_secCenter _ (le_normalizer hg) (d.L₂_le_normalizer_E hg)
  cen := Lin43Out.secCenter_cen _
  perf := s38d_L₂_le_commutator_sup hl.hyp
  odd := k.s8.2.2.1
  RL := (lin43o_R_le_normalizer_E hl k c hR hSR).trans d.normalizer_E_le_normalizer_L₂
  RE := lin43o_R_le_normalizer_E hl k c hR hSR
  RN := fun r hr n hn =>
    Lin43Out.secCenter_conj _
      (((lin43o_R_le_normalizer_E hl k c hR hSR).trans d.normalizer_E_le_normalizer_L₂) hr)
      (lin43o_R_le_normalizer_E hl k c hR hSR hr) hn
  R2 := hR.isPGroup

theorem lin_sec43_out (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData) (R : Subgroup G)
    (hR : IsSylowOf 2 R (normalizer (d.D : Set G))) (hSR : c.S ≤ R) : c.Sec43Out R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : (d.lin43oN.subgroupOf d.L₂).Normal := d.lin43oN_normal
  have hf : 1 ≤ f := by have := hl.hyp.two_le; omega
  have hctx := lin43o_ctx hl k c hR hSR
  have hX := lin43o_lieModel hl k
  have hRS := lin43o_R_inf_L₂ c hR hSR
  refine ⟨fun Y hYR hY => ?_, fun r hr hrS Z hZS hZ hfix => ?_⟩
  · have h1 := Lin43Out.card_le_four_inf hctx LinCase.l3Fixed hf hX hYR hY
    have e : Y ⊓ c.S = Y ⊓ d.L₂ := by
      rw [← hRS, ← inf_assoc, inf_eq_left.2 hYR]
    rw [e]
    exact h1
  · have hrL : r ∉ d.L₂ := by
      intro hrL
      have hmem : r ∈ R ⊓ d.L₂ := ⟨hr, hrL⟩
      rw [hRS] at hmem
      exact hrS hmem
    exact Lin43Out.card_fix_le hctx LinCase.l3Fixed hf hX hr hrL (hZS.trans c.S_syl.le) hZ hfix

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
