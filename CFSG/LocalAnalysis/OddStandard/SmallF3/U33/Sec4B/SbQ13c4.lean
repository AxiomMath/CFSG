module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13c_wreathGrp_le_L (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    wreathGrp x₁ x₂ lam ≤ L := by
  obtain ⟨hx₁, hx₂, hlam⟩ := S4A.generators_mem_L h.c11.toCtx0
  rw [wreathGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact hx₁
  · exact hx₂
  · exact hlam

private lemma q13c_zpowers_t (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ x ∈ twoCore t, x = 1 ∨ x = t := by
  intro x hx
  rw [h.c11.l43] at hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : (orderOf t : ℤ) = 2 := by
    rw [h.c11.hyp.ord_t]; norm_num
  have hkm : t ^ (k % 2) = x := by
    have hh := zpow_mod_orderOf t k
    rw [h2] at hh
    exact hh.trans hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hkm
    exact hkm.symm
  · right
    rw [h1, zpow_one] at hkm
    exact hkm.symm

private lemma q13c_lam_conj_baseGrp (h : Q13Om t L S x₁ x₂ lam rho tau om) {b : G}
    (hb : b ∈ baseGrp x₁ x₂) : lam * b * lam⁻¹ ∈ baseGrp x₁ x₂ :=
  S4A.conj_mem_baseGrp_of_gens (a := x₁) (b := x₂) (g := lam)
    (by rw [h.c11.wreath.conj_x₁]; exact Subgroup.subset_closure (by simp))
    (by rw [S4A.wr_lam_conj_x₂ h.c11.wreath]; exact Subgroup.subset_closure (by simp))
    b hb

theorem q13c_mem_wreath (h : Q13Om t L S x₁ x₂ lam rho tau om) {u : G}
    (hu : u ∈ wreathGrp x₁ x₂ lam) :
    u ∈ baseGrp x₁ x₂ ∨ ∃ b ∈ baseGrp x₁ x₂, u = b * lam := by
  rw [wreathGrp_eq_sup] at hu
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ baseGrp x₁ x₂,
      k * h * k⁻¹ ∈ baseGrp x₁ x₂ := by
    intro k hk b hb
    rcases q13c_zpowers_lam h k hk with hk1 | hkl
    · rw [hk1]; simpa using hb
    · rw [hkl]; exact q13c_lam_conj_baseGrp h hb
  obtain ⟨b, hb, k, hk, hbk⟩ :=
    (mem_sup_iff_of_normalizes (H := baseGrp x₁ x₂) (K := zpowers lam) hnorm).mp hu
  rcases q13c_zpowers_lam h k hk with hk1 | hkl
  · left
    rw [hbk, hk1, mul_one]
    exact hb
  · right
    exact ⟨b, hb, by rw [hbk, hkl]⟩

private lemma q13c_mem_V_of_mem_T (h : Q13Om t L S x₁ x₂ lam rho tau om) {u : G}
    (hu : u ∈ wreathGrp x₁ x₂ lam) (hu2 : u * u = 1)
    (huy : u * x₁ ^ 2 = x₁ ^ 2 * u) : u ∈ fourGrp x₁ x₂ := by
  rcases q13c_mem_wreath h hu with huA | ⟨b, hbA, rfl⟩
  · rw [(h.c11.wreath.fourGrp_eq_omega).1]
    exact Subgroup.subset_closure ⟨huA, by rwa [pow_two]⟩
  · exfalso
    have hyA : x₁ ^ 2 ∈ baseGrp x₁ x₂ :=
      Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
    have hzA : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ :=
      Subgroup.pow_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 2
    have hyzA : x₁ ^ 2 * (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := Subgroup.mul_mem _ hyA hzA
    have hbcomm : b * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * b :=
      S4A.baseGrp_comm h.c11.wreath hbA hyzA
    have hconj : (b * lam) * x₁ ^ 2 * (b * lam)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
      calc (b * lam) * x₁ ^ 2 * (b * lam)⁻¹
          = b * (lam * x₁ ^ 2 * lam⁻¹) * b⁻¹ := by group
        _ = b * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * b⁻¹ := by rw [q13c_lam_y h]
        _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by rw [hbcomm]; group
    have hy_eq : (b * lam) * x₁ ^ 2 * (b * lam)⁻¹ = x₁ ^ 2 := by
      rw [huy]; group
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have h : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 * 1 := by
        rw [mul_one, ← hconj, hy_eq]
      exact mul_left_cancel h
    exact (q13b_z_facts h).1 hz1

theorem q13c_inv_PT (h : Q13Om t L S x₁ x₂ lam rho tau om) {w : G} (hwS : w ∈ S)
    (hwPL : w ∈ twoCore t ⊔ L) (hw2 : w * w = 1) (hwy : w * x₁ ^ 2 = x₁ ^ 2 * w) :
    w ∈ fourGrp x₁ x₂ ∨ t * w ∈ fourGrp x₁ x₂ := by
  have hw_sup : w ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
    have hwmem : w ∈ S ⊓ (twoCore t ⊔ L) := ⟨hwS, hwPL⟩
    rwa [h.c11.inf_PL] at hwmem
  have hnorm : ∀ k ∈ wreathGrp x₁ x₂ lam, ∀ a ∈ twoCore t,
      k * a * k⁻¹ ∈ twoCore t := by
    intro k hk a ha
    rcases q13c_zpowers_t h a ha with ha1 | hat
    · rw [ha1]; simpa using Subgroup.one_mem (twoCore t)
    · rw [hat]
      have hkH : k ∈ invCent t :=
        S4A.L_le_invCent h.c11.hyp (q13c_wreathGrp_le_L h hk)
      have hcomm : k * t = t * k := S4A.mem_invCent_iff.mp hkH
      rw [show k * t * k⁻¹ = t by rw [hcomm]; group]
      exact h.c11.hyp.mem_twoCore
  obtain ⟨p, hp2, u, huT, hwup⟩ :=
    (mem_sup_iff_of_normalizes (H := twoCore t) (K := wreathGrp x₁ x₂ lam) hnorm).mp hw_sup
  have huH : u ∈ invCent t := S4A.L_le_invCent h.c11.hyp (q13c_wreathGrp_le_L h huT)
  have hcomm_ut : u * t = t * u := S4A.mem_invCent_iff.mp huH
  have hyT : x₁ ^ 2 ∈ wreathGrp x₁ x₂ lam :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hyH : x₁ ^ 2 ∈ invCent t := S4A.L_le_invCent h.c11.hyp (q13c_wreathGrp_le_L h hyT)
  have hty : t * x₁ ^ 2 = x₁ ^ 2 * t := (S4A.mem_invCent_iff.mp hyH).symm
  rcases q13c_zpowers_t h p hp2 with hp1 | hpt
  · left
    have hw : w = u := by rw [hwup, hp1, one_mul]
    rw [hw]
    exact q13c_mem_V_of_mem_T h huT (by rw [← hw, hw2]) (by rw [← hw, hwy])
  · right
    have ht2 : t * t = 1 := q13a_t_mul_self h
    have hu2 : u * u = 1 := by
      have h : w * w = u * u := by
        rw [hwup, hpt]
        calc (t * u) * (t * u) = t * (u * t) * u := by group
          _ = t * (t * u) * u := by rw [hcomm_ut]
          _ = (t * t) * (u * u) := by group
          _ = u * u := by rw [ht2, one_mul]
      rw [← h, hw2]
    have huy : u * x₁ ^ 2 = x₁ ^ 2 * u := by
      have h1 : w * x₁ ^ 2 = t * (u * x₁ ^ 2) := by
        rw [hwup, hpt]; group
      have h2 : x₁ ^ 2 * w = t * (x₁ ^ 2 * u) := by
        rw [hwup, hpt]
        calc x₁ ^ 2 * (t * u) = (x₁ ^ 2 * t) * u := by group
          _ = (t * x₁ ^ 2) * u := by rw [hty]
          _ = t * (x₁ ^ 2 * u) := by group
      have h3 := hwy
      rw [h1, h2] at h3
      exact mul_left_cancel h3
    have huV : u ∈ fourGrp x₁ x₂ := q13c_mem_V_of_mem_T h huT hu2 huy
    have htw : t * w = u := by
      rw [hwup, hpt]
      calc t * (t * u) = (t * t) * u := by group
        _ = u := by rw [ht2, one_mul]
    rw [htw]
    exact huV

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
