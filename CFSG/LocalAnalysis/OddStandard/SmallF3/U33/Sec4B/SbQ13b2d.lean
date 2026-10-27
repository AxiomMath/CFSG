module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_V_eq_N (h : Q13Om t L S x₁ x₂ lam rho tau om) {V : Subgroup G}
    (hV : NormalIn V (ctxU t tau x₁ x₂ lam)) (hVe : CFSG.Open.IsElemAbelian 2 V)
    (hVc : Nat.card V = 8) (hV0 : fourGrp x₁ x₂ ≤ V) : V = ctxN tau x₁ x₂ := by
  have hV0card : Nat.card (fourGrp x₁ x₂) = 4 := h.c11.wreath.fourGrp_eq_omega.2.2
  have htU : t ∈ ctxU t tau x₁ x₂ lam := q13b_O_le_U h (q13b_t_mem_O h)
  have homU : om ∈ ctxU t tau x₁ x₂ lam := q13b_O_le_U h (q13b_om_mem_O h)
  have hcard : Nat.card V = 2 * Nat.card (fourGrp x₁ x₂) := by rw [hVc, hV0card]
  have hVnorm := q13b_V_normal_U h
  have hVle : V ≤ ctxN tau x₁ x₂ := by
    intro v hv
    have hvU : v ∈ ctxU t tau x₁ x₂ lam := hV.1 hv
    have hcent : ∀ w ∈ fourGrp x₁ x₂, v * w = w * v :=
      fun w hw => CFSG.Open.IsElemAbelian.comm hVe hv (hV0 hw)
    have hvO : v ∈ ctxO t tau x₁ x₂ := q13b_cent_V_le_O h hvU hcent
    have hv2 : v * v = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hVe hv
    have ha : t * v * t⁻¹ * v⁻¹ ∈ fourGrp x₁ x₂ :=
      q13b_comm_mem_of_index_two (F := V) (F₀ := fourGrp x₁ x₂) hV0 hcard
        (fun x hx => hV.2 t htU x hx)
        (fun x hx => hVnorm.2 t htU x hx)
        (fun x hx => by
          simpa using hVnorm.2 t⁻¹ ((ctxU t tau x₁ x₂ lam).inv_mem htU) x hx)
        v hv
    have hb : om * v * om⁻¹ * v⁻¹ ∈ fourGrp x₁ x₂ :=
      q13b_comm_mem_of_index_two (F := V) (F₀ := fourGrp x₁ x₂) hV0 hcard
        (fun x hx => hV.2 om homU x hx)
        (fun x hx => hVnorm.2 om homU x hx)
        (fun x hx => by
          simpa using hVnorm.2 om⁻¹ ((ctxU t tau x₁ x₂ lam).inv_mem homU) x hx)
        v hv
    exact q13b_core h hvO hv2 ha hb
  exact Subgroup.eq_of_le_of_card_ge hVle (by rw [q13b_card_N h, hVc])

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
