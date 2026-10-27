module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_gam_inv (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * (t * om) * t⁻¹ = (t * om)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (q13a_t_mul_self h),
    inv_eq_of_mul_eq_one_right h.om_sq, ← mul_assoc, q13a_t_mul_self h, one_mul]

private theorem q13d_gam_zpow_inv (h : Q13Om t L S x₁ x₂ lam rho tau om) (k : ℤ) :
    t * (t * om) ^ k * t⁻¹ = ((t * om) ^ k)⁻¹ := by
  rw [← conj_zpow (a := t) (b := t * om) (i := k), q13d_gam_inv h, inv_zpow]

private theorem q13d_gam_comm (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    (a : G) (ha : a ∈ q13A t tau x₁ x₂ rho) : Commute (t * om) a :=
  q13d_gam_cent_A h hII a ha

private theorem q13d_gam_zpow_cent (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    (k : ℤ) {a : G} (ha : a ∈ q13A t tau x₁ x₂ rho) :
    (t * om) ^ k * a = a * (t * om) ^ k :=
  (q13d_gam_comm h hII a ha).zpow_left k

private theorem q13d_gam_comm_zpow_inv (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    (k : ℤ) {a : G} (ha : a ∈ q13A t tau x₁ x₂ rho) :
    Commute a⁻¹ (((t * om) ^ k)⁻¹) :=
  ((q13d_gam_comm h hII a ha).symm.zpow_right k).inv_left.inv_right

theorem q13d_P_comm (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, ∀ q ∈ q13P t tau x₁ x₂ rho om, p * q = q * p := by
  intro p hp q hq
  obtain ⟨a, ha, i, rfl⟩ := (q13d_mem_P h hII).mp hp
  obtain ⟨b, hb, j, rfl⟩ := (q13d_mem_P h hII).mp hq
  have h1 : Commute a (t * om) := (q13d_gam_comm h hII a ha).symm
  exact (Commute.mul_left
    (Commute.mul_right (q13a_A_comm h a ha b hb) (h1.zpow_right j))
    (Commute.mul_right ((q13d_gam_comm h hII b hb).zpow_left i)
      (Commute.zpow_zpow_self (t * om) i j))).eq

theorem q13d_card_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    Nat.card ↥(q13P t tau x₁ x₂ rho om) = 2 ^ 6 := by
  rw [q13P]
  have hK : ∀ k ∈ zpowers (t * om), ∀ a ∈ q13A t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ q13A t tau x₁ x₂ rho := by
    intro k hk a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rwa [show (t * om) ^ m * a * ((t * om) ^ m)⁻¹ = a by
      rw [q13d_gam_zpow_cent h hII m ha]; group]
  have hHK : q13A t tau x₁ x₂ rho ⊓ zpowers (t * om) = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    rw [Subgroup.mem_bot]
    exact q13d_A_inf_gam h g (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hg).2
  have hcard := card_sup_eq_mul (H := q13A t tau x₁ x₂ rho) (K := zpowers (t * om)) hK hHK
  rw [q13a_card_A h, Nat.card_zpowers, q13d_orderOf_gam h] at hcard
  rw [hcard]
  norm_num

theorem q13d_t_not_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    t ∉ q13P t tau x₁ x₂ rho om := by
  intro ht
  have hE : q13E0 t tau x₁ x₂ rho om = q13P t tau x₁ x₂ rho om := by
    rw [q13E0, sup_eq_left]
    exact Subgroup.zpowers_le.mpr ht
  have hcard := q13d_card_E0 h
  rw [hE, q13d_card_P h hII] at hcard
  norm_num at hcard

theorem q13d_t_inv_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, t * p * t⁻¹ = p⁻¹ := by
  intro p hp
  obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hII).mp hp
  calc t * (a * (t * om) ^ k) * t⁻¹
      = (t * a * t⁻¹) * (t * (t * om) ^ k * t⁻¹) := by group
    _ = a⁻¹ * ((t * om) ^ k)⁻¹ := by
        rw [q13a_t_inv_A h a ha, q13d_gam_zpow_inv h k]
    _ = (a * (t * om) ^ k)⁻¹ := by
        rw [mul_inv_rev]
        exact (q13d_gam_comm_zpow_inv h hII k ha).eq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
