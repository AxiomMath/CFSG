module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem card_CO_eq (hc : Ctx4L t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(centralizer ({t * lam} : Set G) ⊓ ctxO t tau x₁ x₂) = 2 ^ 5 := by
  have hOU : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := O_le_U hc
  set A : Subgroup G := ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) with hA
  have hAcard : Nat.card A = 2 ^ 6 := hc.card_CU_tl
  have hAU : A ≤ ctxU t tau x₁ x₂ lam := inf_le_left
  have hrelU : (ctxO t tau x₁ x₂).relIndex (ctxU t tau x₁ x₂ lam) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := ctxO t tau x₁ x₂) (K := ctxU t tau x₁ x₂ lam)
    rw [inf_eq_left.mpr hOU, card_U hc, hc.card_O] at h
    have h9 : (2 : ℕ) ^ 9 = 2 * 2 ^ 8 := by norm_num
    rw [h9] at h
    exact Nat.mul_right_cancel (by norm_num) h
  have hrelA : (ctxO t tau x₁ x₂).relIndex A = 2 := by
    have hle : (ctxO t tau x₁ x₂).relIndex A ≤ 2 := by
      rw [← hrelU]
      exact Subgroup.relIndex_le_of_le_right hAU (by rw [hrelU]; norm_num)
    have hqA : t * lam ∈ A := ⟨q_mem_U hc, Subgroup.mem_centralizer_iff.mpr (by
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh])⟩
    have hne1 : (ctxO t tau x₁ x₂).relIndex A ≠ 1 := by
      intro h1
      exact q_not_mem_O hc ((Subgroup.relIndex_eq_one.mp h1) hqA)
    have hne0 : (ctxO t tau x₁ x₂).relIndex A ≠ 0 := by
      intro h0
      have h := Subgroup.relIndex_mul_card (H := ctxO t tau x₁ x₂) (K := A)
      rw [h0, zero_mul, hAcard] at h
      norm_num at h
    omega
  have hmul := Subgroup.relIndex_mul_card (H := ctxO t tau x₁ x₂) (K := A)
  rw [hrelA, hAcard] at hmul
  have heq : centralizer ({t * lam} : Set G) ⊓ ctxO t tau x₁ x₂ = ctxO t tau x₁ x₂ ⊓ A := by
    rw [hA, ← inf_assoc, inf_eq_left.mpr hOU, inf_comm]
  rw [heq]
  have h6 : (2 : ℕ) ^ 6 = 2 * 2 ^ 5 := by norm_num
  rw [h6] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
