module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_t_mul_t (hc : Ctx4C t L S x₁ x₂ lam rho tau) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [hc.hyp.ord_t] at h
  simpa [pow_two] using h

theorem w4q_tau_mul_tau (hc : Ctx4C t L S x₁ x₂ lam rho tau) : tau * tau = 1 := by
  simpa [pow_two] using hc.l44.1

theorem w4q_V_le_A (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, Subgroup.closure_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have h₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have h₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  rcases hw with rfl | rfl
  · exact pow_mem h₁ 2
  · exact pow_mem (mul_mem h₁ h₂) 2

theorem w4q_V_le_E (t x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
  rw [fourGrp, Subgroup.closure_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl <;> exact Subgroup.subset_closure (by simp)

theorem w4q_t_mem_E (t x₁ x₂ : G) : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)

theorem w4q_E_le_X (t tau x₁ x₂ : G) : ctxE t x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxE, Subgroup.closure_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)

theorem w4q_A_comm (hc : Ctx4C t L S x₁ x₂ lam rho tau) {a b : G} (ha : a ∈ baseGrp x₁ x₂)
    (hb : b ∈ baseGrp x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative ↥(ctxW t x₁ x₂) := hc.abelian_W
  exact congrArg Subtype.val (mul_comm' (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(ctxW t x₁ x₂))
    ⟨b, Subgroup.mem_sup_right hb⟩)

theorem w4q_X_cases
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {x : G}
    (hx : x ∈ ctxX t tau x₁ x₂) : x ∈ ctxE t x₁ x₂ ∨ tau * x ∈ ctxE t x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have ht2 := w4q_t_mul_t hc
  have htτ : t * tau = tau * t := w4_t_comm_tau hc4
  have htE := w4q_t_mem_E t x₁ x₂
  have hVE := w4q_V_le_E t x₁ x₂
  rcases l12_X_cases hc4 hx with hxN | htxN
  · rcases l12_N_cases hc4 hxN with hV | hV
    · exact Or.inl (hVE hV)
    · exact Or.inr (hVE hV)
  · rcases l12_N_cases hc4 htxN with hV | hV
    · left
      have h1 : t * (t * x) = x := by rw [← mul_assoc, ht2, one_mul]
      have h2 : t * (t * x) ∈ ctxE t x₁ x₂ := mul_mem htE (hVE hV)
      rwa [h1] at h2
    · right
      have h1 : t * (tau * (t * x)) = tau * x := by
        calc t * (tau * (t * x)) = (t * tau) * t * x := by group
          _ = (tau * t) * t * x := by rw [htτ]
          _ = tau * (t * t) * x := by group
          _ = tau * x := by rw [ht2, mul_one]
      have h2 : t * (tau * (t * x)) ∈ ctxE t x₁ x₂ := mul_mem htE (hVE hV)
      rwa [h1] at h2

theorem w4q_tau_not_mem_E (hc : Ctx4C t L S x₁ x₂ lam rho tau) : tau ∉ ctxE t x₁ x₂ := by
  intro h
  apply hc.tau_not_mem
  have hVL : fourGrp x₁ x₂ ≤ L := (w4q_V_le_A x₁ x₂).trans (w4_baseGrp_le_L hc.toCtx0)
  have hE : ctxE t x₁ x₂ ≤ twoCore t ⊔ L := by
    rw [ctxE, Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left hc.hyp.mem_twoCore
    · exact Subgroup.mem_sup_right (hVL (Subgroup.subset_closure (by simp)))
    · exact Subgroup.mem_sup_right (hVL (Subgroup.subset_closure (by simp)))
  exact hE h

theorem w4q_E_cases
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {e : G}
    (he : e ∈ ctxE t x₁ x₂) : e ∈ fourGrp x₁ x₂ ∨ t * e ∈ fourGrp x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hVE := w4q_V_le_E t x₁ x₂
  have hτE := w4q_tau_not_mem_E hc
  have htE := w4q_t_mem_E t x₁ x₂
  have hX : e ∈ ctxX t tau x₁ x₂ := w4q_E_le_X t tau x₁ x₂ he
  rcases l12_X_cases hc4 hX with hxN | htxN
  · rcases l12_N_cases hc4 hxN with hV | hV
    · exact Or.inl hV
    · exfalso
      apply hτE
      have h1 : tau = (tau * e) * e⁻¹ := by group
      rw [h1]
      exact mul_mem (hVE hV) (inv_mem he)
  · rcases l12_N_cases hc4 htxN with hV | hV
    · exact Or.inr hV
    · exfalso
      apply hτE
      have h1 : tau = (tau * (t * e)) * (t * e)⁻¹ := by group
      rw [h1]
      exact mul_mem (hVE hV) (inv_mem (mul_mem htE he))

theorem w4q_not_sq_tV (hc : Ctx4C t L S x₁ x₂ lam rho tau) (g : G) {v : G}
    (hv : v ∈ fourGrp x₁ x₂) : g * g ≠ t * v := by
  intro h
  have hmem : t * v ∈ conjIn (ctxM t tau x₁ x₂) t := by
    rw [hc.tM]
    exact ⟨v, hv, rfl⟩
  obtain ⟨m, -, hm⟩ := hmem
  apply hc.l44.2 (m⁻¹ * g * m)
  have h1 : (m⁻¹ * g * m) * (m⁻¹ * g * m) = t := by
    calc (m⁻¹ * g * m) * (m⁻¹ * g * m) = m⁻¹ * (g * g) * m := by group
      _ = m⁻¹ * (t * v) * m := by rw [h]
      _ = m⁻¹ * (m * t * m⁻¹) * m := by rw [hm]
      _ = t := by group
  rw [pow_two]
  exact h1

theorem w4q_A_cent_E (hc : Ctx4C t L S x₁ x₂ lam rho tau) {a e : G} (ha : a ∈ baseGrp x₁ x₂)
    (he : e ∈ ctxE t x₁ x₂) : e * a = a * e := by
  have hA : baseGrp x₁ x₂ ≤ closure ({t, tau, x₁, x₂} : Set G) := by
    rw [baseGrp, Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  have h : a ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
    rw [hc.cent_E]
    exact hA ha
  exact (Subgroup.mem_centralizer_iff.mp h.2) e he

theorem w4q_X_norm_A
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {k h : G}
    (hk : k ∈ ctxX t tau x₁ x₂) (hh : h ∈ baseGrp x₁ x₂) : k * h * k⁻¹ ∈ baseGrp x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hcentr : ∀ {w : G}, w ∈ baseGrp x₁ x₂ → ∀ a ∈ baseGrp x₁ x₂,
      w * a * w⁻¹ ∈ baseGrp x₁ x₂ := by
    intro w hw a ha
    rw [w4q_A_comm hc hw ha, mul_inv_cancel_right]
    exact ha
  have hmem : ctxX t tau x₁ x₂ ≤ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [ctxX, Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    apply Subgroup.mem_normalizer_fintype
    intro a ha
    rcases hw with rfl | rfl | rfl | rfl
    · rw [w4q_A_cent_E hc ha (w4q_t_mem_E w x₁ x₂), mul_inv_cancel_right]
      exact ha
    · rw [w4_tau_conj_baseGrp hc4 ha]
      exact inv_mem ha
    · exact hcentr (pow_mem hx₁ 2) a ha
    · exact hcentr (pow_mem (mul_mem hx₁ hx₂) 2) a ha
  exact ((Subgroup.mem_normalizer_iff.mp (hmem hk)) h).mp hh

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
