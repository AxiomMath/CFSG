module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d7a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d8a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d8d_inf_A_base_le_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13A t tau x₁ x₂ rho ⊓ baseGrp x₁ x₂ ≤ fourGrp x₁ x₂ := by
  intro a ha
  obtain ⟨haA, haB⟩ := Subgroup.mem_inf.mp ha
  have hBcent : baseGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
    rw [← l12_CQ_t h.c11]; exact inf_le_right
  have hcomm : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp (hBcent haB)
  have hinv : t * a * t⁻¹ = a⁻¹ := q13a_t_inv_A h a haA
  have haeq : a = a⁻¹ := by
    have h1 : t * a * t⁻¹ = a := by rw [hcomm.symm]; group
    rw [h1] at hinv; exact hinv
  have hsq : a * a = 1 := by
    nth_rewrite 1 [haeq]
    exact inv_mul_cancel a
  exact q13b_omega1_A h a haA hsq

theorem q13d_Q_le_A_sup (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤ q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂ := by
  have hcardInf : Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ baseGrp x₁ x₂) ≤ 4 := by
    have hle := Subgroup.card_le_of_le (q13d8d_inf_A_base_le_V h)
    rwa [h.c11.wreath.fourGrp_eq_omega.2.2] at hle
  have hprod := q13d_card_mul_le_card_sup_mul_card_inf
    (q13A t tau x₁ x₂ rho) (baseGrp x₁ x₂)
  rw [q13a_card_A h, (h.c11.wreath.baseGrp_eq).2.2] at hprod
  have h256 : 256 ≤ Nat.card ↥(q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂) *
      Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ baseGrp x₁ x₂) := by
    simpa using hprod
  have hle64 : 64 ≤ Nat.card ↥(q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂) := by
    have h4 : Nat.card ↥(q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂) *
        Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ baseGrp x₁ x₂) ≤
        Nat.card ↥(q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂) * 4 :=
      Nat.mul_le_mul_left _ hcardInf
    omega
  have hJQ : q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho :=
    sup_le inf_le_left h.c11.base_le_Q
  have hcardQ : Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 64 := by
    rw [l12_card_Q h.c11]; norm_num
  have heq : q13A t tau x₁ x₂ rho ⊔ baseGrp x₁ x₂ = ctxQ t tau x₁ x₂ rho :=
    Subgroup.eq_of_le_of_card_ge hJQ (by rw [hcardQ]; exact hle64)
  exact le_of_eq heq.symm

theorem q13d_M_le_BK (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxM t tau x₁ x₂ ≤ q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) := by
  have hA_le : q13A t tau x₁ x₂ rho ≤
      q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) :=
    le_trans (le_trans (le_trans le_sup_left (q13d_P_le_E0 h)) (q13d_E0_le_B h)) le_sup_left
  have hB0_le : baseGrp x₁ x₂ ≤
      q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) := by
    refine le_trans (Subgroup.closure_mono ?_) le_sup_right
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hQ_le : ctxQ t tau x₁ x₂ rho ≤
      q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) :=
    le_trans (q13d_Q_le_A_sup h) (sup_le hA_le hB0_le)
  have hCO_le : ctxCO t tau x₁ x₂ rho ≤
      q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) :=
    le_trans (le_trans (by rw [h.CO_eq, q13d_E0_eq_AC h]; exact le_sup_right)
      (q13d_E0_le_B h)) le_sup_left
  have hK_le : closure ({rho, lam} : Set G) ≤
      q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) := by
    refine le_trans (Subgroup.closure_mono ?_) le_sup_right
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  rw [h.c11.M_eq]
  exact sup_le (by rw [q13b_O_eq h]; exact sup_le hQ_le hCO_le) hK_le

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
