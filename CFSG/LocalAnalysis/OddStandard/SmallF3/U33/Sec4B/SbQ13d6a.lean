module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_card_CM_t (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) = 3 * 2 ^ 7 := by
  have hV4 : (fourGrp x₁ x₂ : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (h.c11.wreath.fourGrp_eq_omega).2.2
  have hA : (t • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    rw [Set.ncard_smul_set, hV4]
  have hB : ((t * tau) • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    rw [Set.ncard_smul_set, hV4]
  have hdisj : Disjoint (t • (fourGrp x₁ x₂ : Set G))
      ((t * tau) • (fourGrp x₁ x₂ : Set G)) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rw [Set.mem_smul_set] at hxA hxB
    obtain ⟨v, hv, hvx⟩ := hxA
    obtain ⟨w, hw, hwx⟩ := hxB
    have hvx' : t * v = x := hvx
    have hwx' : (t * tau) * w = x := hwx
    have h1 : t * v = (t * tau) * w := by rw [hvx', hwx']
    have h2 : v = tau * w := by
      calc v = t⁻¹ * (t * v) := by group
        _ = t⁻¹ * ((t * tau) * w) := by rw [h1]
        _ = tau * w := by group
    have htau : tau = v * w⁻¹ := by
      rw [h2]; group
    exact l12_tau_not_mem_V h.c11.toCtx10.toCtx4 (by
      rw [htau]
      exact (fourGrp x₁ x₂).mul_mem hv ((fourGrp x₁ x₂).inv_mem hw))
  have hUnion : (conjIn (ctxM t tau x₁ x₂) t).ncard = 8 := by
    rw [h.c11.tM]
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hA, hB]
  have hmain := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) t
  rw [h.c11.card_M, hUnion] at hmain
  rw [show (3 : ℕ) * 2 ^ 10 = 8 * (3 * 2 ^ 7) by norm_num] at hmain
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) hmain).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
