module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_E0_order_four_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    {y : ↥(q13E0 t tau x₁ x₂ rho om)} (hy : orderOf y = 4) :
    (y : G) ∈ q13P t tau x₁ x₂ rho om := by
  by_contra hyP
  rcases (q13d_mem_E0 h hII).mp y.2 with hP | ⟨p, hp, hpy⟩
  · exact hyP hP
  · have hsq : (y : G) * (y : G) = 1 := by
      rw [hpy]
      exact q13d_E0_out_sq h hII p hp
    have hdvd : orderOf (y : G) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rw [show orderOf (y : G) = 4 from by rw [Subgroup.orderOf_coe, hy]] at hdvd
    norm_num at hdvd

private theorem q13d_E0_eq_mul_order_four (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    {y : ↥(q13E0 t tau x₁ x₂ rho om)}
    (hyP : (y : G) ∈ q13P t tau x₁ x₂ rho om) (hord : orderOf y ≠ 4) :
    ∃ a b : ↥(q13E0 t tau x₁ x₂ rho om), orderOf a = 4 ∧ orderOf b = 4 ∧ y = a * b := by
  have hy4G : (y : G) ^ 4 = 1 := q13d_P_pow_four h hII (y : G) hyP
  have hy4 : y ^ 4 = 1 := by
    apply Subtype.ext
    simpa using hy4G
  have hy2 : y ^ 2 = 1 := by
    have hdvd : orderOf y ∣ 4 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_iff_pow_eq_one.mpr hy4G
    have h4 : orderOf y ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    have hk1 : k ≤ 1 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · omega
      · have hk2 : k = 2 := by omega
        exact absurd (by rw [hk', hk2]; norm_num) hord
    have hdvd2 : orderOf y ∣ 2 := by
      rw [hk']
      simpa using pow_dvd_pow 2 hk1
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd2
  let g : ↥(q13E0 t tau x₁ x₂ rho om) := ⟨t * om, q13d_gam_mem_E0 h⟩
  have hgval : (g : G) = t * om := rfl
  have hgP : (g : G) ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
  have hgord : orderOf g = 4 := by
    rw [← Subgroup.orderOf_coe, hgval]
    exact q13d_orderOf_gam h
  have hg4 : g ^ 4 = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hgord] at h
  have hg2val : (g : G) ^ 2 = tau := by
    rw [hgval]
    exact q13d_gam_sq h
  have hg2ne : g ^ 2 ≠ 1 := by
    intro hgg
    have hcoeeq : (g : G) ^ 2 = 1 := by
      have hh := congrArg (fun z : ↥(q13E0 t tau x₁ x₂ rho om) => (z : G)) hgg
      simpa using hh
    rw [hg2val] at hcoeeq
    exact q13b_tau_ne_one h hcoeeq
  have hcomm : Commute y g := by
    rw [commute_iff_eq]
    apply Subtype.ext
    exact q13d_P_comm h hII (y : G) hyP (g : G) hgP
  have hyg2eq : (y * g) ^ 2 = g ^ 2 := by
    rw [hcomm.mul_pow 2, hy2, one_mul]
  have hyg2ne : (y * g) ^ 2 ≠ 1 := by
    rw [hyg2eq]
    exact hg2ne
  have hyg4 : (y * g) ^ 4 = 1 := by
    rw [hcomm.mul_pow 4, hy4, hg4, one_mul]
  have hordyg : orderOf (y * g) = 4 := by
    have hnot : ¬ (y * g) ^ 2 ^ 1 = 1 := by simpa using hyg2ne
    have hfin : (y * g) ^ 2 ^ (1 + 1) = 1 := by simpa using hyg4
    have hh := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y * g) hnot hfin
    simpa using hh
  have hginvord : orderOf g⁻¹ = 4 := by rw [orderOf_inv, hgord]
  refine ⟨y * g, g⁻¹, hordyg, hginvord, ?_⟩
  group

theorem q13d_P_char_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    CharIn (q13P t tau x₁ x₂ rho om) (q13E0 t tau x₁ x₂ rho om) := by
  refine ⟨q13d_P_le_E0 h, ?_⟩
  rw [Subgroup.characteristic_iff_map_le]
  intro φ z hz
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  change ((φ y : ↥(q13E0 t tau x₁ x₂ rho om)) : G) ∈ q13P t tau x₁ x₂ rho om
  by_cases hord : orderOf y = 4
  · exact q13d_E0_order_four_mem_P h hII (y := φ y) (by rw [MulEquiv.orderOf_eq, hord])
  · obtain ⟨a, b, ha, hb, hyab⟩ := q13d_E0_eq_mul_order_four h hII hy hord
    have haP : ((φ a : ↥(q13E0 t tau x₁ x₂ rho om)) : G) ∈ q13P t tau x₁ x₂ rho om :=
      q13d_E0_order_four_mem_P h hII (by rw [MulEquiv.orderOf_eq, ha])
    have hbP : ((φ b : ↥(q13E0 t tau x₁ x₂ rho om)) : G) ∈ q13P t tau x₁ x₂ rho om :=
      q13d_E0_order_four_mem_P h hII (by rw [MulEquiv.orderOf_eq, hb])
    have hdecomp : ((φ y : ↥(q13E0 t tau x₁ x₂ rho om)) : G) =
        ((φ a : ↥(q13E0 t tau x₁ x₂ rho om)) : G) *
          ((φ b : ↥(q13E0 t tau x₁ x₂ rho om)) : G) := by
      rw [hyab, map_mul]
      rfl
    rw [hdecomp]
    exact (q13P t tau x₁ x₂ rho om).mul_mem haP hbP

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
