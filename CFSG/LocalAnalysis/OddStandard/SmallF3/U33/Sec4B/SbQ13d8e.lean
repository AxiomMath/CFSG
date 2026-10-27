module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d8b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d8c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d8d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_L_eq_BM (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    q13L t tau x₁ x₂ rho om = q13B t tau x₁ x₂ rho om ⊔ ctxM t tau x₁ x₂ := by
  have hMleL : ctxM t tau x₁ x₂ ≤ q13L t tau x₁ x₂ rho om := q13d_M_le_L h hB
  have hle : q13B t tau x₁ x₂ rho om ⊔ ctxM t tau x₁ x₂ ≤ q13L t tau x₁ x₂ rho om :=
    sup_le inf_le_left hMleL
  have hinf_eq : q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂ =
      ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      have hx1 := hx.1
      simp only [q13B, Subgroup.mem_inf] at hx1
      rw [Subgroup.mem_inf]
      exact ⟨hx.2, hx1.2⟩
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      rw [Subgroup.mem_inf]
      exact ⟨⟨hMleL hx.1, hx.2⟩, hx.1⟩
  have hcard_inf : Nat.card ↥(q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂) ≤ 2 ^ 7 := by
    rw [hinf_eq]
    exact q13d_card_CM_N_le h hB hII
  have hprod := q13d_card_mul_le_card_sup_mul_card_inf
    (q13B t tau x₁ x₂ rho om) (ctxM t tau x₁ x₂)
  rw [h.c11.card_M] at hprod
  have hstep : Nat.card ↥(q13B t tau x₁ x₂ rho om) * (3 * 2 ^ 10) ≤
      Nat.card ↥(q13B t tau x₁ x₂ rho om ⊔ ctxM t tau x₁ x₂) * 2 ^ 7 :=
    hprod.trans (Nat.mul_le_mul_left _ hcard_inf)
  have h24 : 24 * Nat.card ↥(q13B t tau x₁ x₂ rho om) ≤
      Nat.card ↥(q13B t tau x₁ x₂ rho om ⊔ ctxM t tau x₁ x₂) := by
    have hkey : 24 * Nat.card ↥(q13B t tau x₁ x₂ rho om) * 2 ^ 7 =
        Nat.card ↥(q13B t tau x₁ x₂ rho om) * (3 * 2 ^ 10) := by ring
    rw [← hkey] at hstep
    exact Nat.le_of_mul_le_mul_right hstep (by norm_num)
  have hcard_ge : Nat.card ↥(q13L t tau x₁ x₂ rho om) ≤
      Nat.card ↥(q13B t tau x₁ x₂ rho om ⊔ ctxM t tau x₁ x₂) :=
    (q13d_card_L_le h hB hII).trans h24
  exact (Subgroup.eq_of_le_of_card_ge hle hcard_ge).symm

theorem q13d_L_eq (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    q13L t tau x₁ x₂ rho om = q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) := by
  rw [q13d_L_eq_BM h hB hII]
  have hMbase : baseGrp x₁ x₂ ≤ ctxM t tau x₁ x₂ :=
    h.c11.base_le_Q.trans
      ((l12_Q_le_R h.c11).trans (h.c11.R_le_O.trans (p0_O_le_M t tau x₁ x₂)))
  have hKleM : closure ({x₁, x₂, rho, lam} : Set G) ≤ ctxM t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      exact hMbase (Subgroup.subset_closure (by simp))
    · rw [hx]
      exact hMbase (Subgroup.subset_closure (by simp))
    · rw [hx]
      exact (q13a_mem_M h).2.2.1
    · rw [hx]
      exact (q13a_mem_M h).2.2.2.1
  apply le_antisymm
  · exact sup_le le_sup_left (q13d_M_le_BK h)
  · exact sup_le le_sup_left (hKleM.trans le_sup_right)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
