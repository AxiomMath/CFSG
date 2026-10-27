module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Stmt

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}

theorem fzl59b_mem_invCent {g : G} : g ∈ invCent t ↔ g * t = t * g := by
  rw [invCent]
  exact Subgroup.mem_centralizer_singleton_iff

theorem fzl59b_conj_fix {k : G} (hk : k ∈ invCent t) : k * t * k⁻¹ = t := by
  have h1 : k * t = t * k := fzl59b_mem_invCent.mp hk
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

theorem fzl59b_conj_mul {k w : G} (hk : k ∈ invCent t) :
    k * (t * w) * k⁻¹ = t * (k * w * k⁻¹) := by
  calc k * (t * w) * k⁻¹ = (k * t * k⁻¹) * (k * w * k⁻¹) := by group
    _ = t * (k * w * k⁻¹) := by rw [fzl59b_conj_fix hk]

theorem fzl59b_isConj_conj {a w : G} (k : G) : IsConj a (k * w * k⁻¹) ↔ IsConj a w :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨k, rfl⟩).symm, fun h => h.trans (isConj_iff.mpr ⟨k, rfl⟩)⟩

theorem fzl59b_conj_pair {k w v : G} (hk : k ∈ invCent t) (hv : k * w * k⁻¹ = v) :
    (IsConj t w ↔ IsConj t v) ∧ (IsConj t (t * w) ↔ IsConj t (t * v)) := by
  refine ⟨?_, ?_⟩
  · rw [← hv]
    exact (fzl59b_isConj_conj k).symm
  · rw [← hv, ← fzl59b_conj_mul hk]
    exact (fzl59b_isConj_conj k).symm

theorem fzl59b_t_mul_self (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [h.ctx.hyp.ord_t] at h1
  rwa [pow_two] at h2

theorem fzl59b_t_ne_one (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) : t ≠ 1 := by
  intro h1
  have h2 := h.ctx.hyp.ord_t
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem fzl59b_twoCore_eq (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) {p : G}
    (hp : p ∈ twoCore t) : p = 1 ∨ p = t := by
  have hp2 : p ^ 2 = 1 := by
    have h1 : (⟨p, hp⟩ : twoCore t) ^ Nat.card (twoCore t) = 1 := pow_card_eq_one'
    rw [h.card_two] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  exact h.ctx.hyp.eq_one_or_eq p hp hp2

theorem fzl59b_b_mem (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) (i : Fin 3)
    (j : Fin 2) : b i j ∈ T₃ := by
  have h1 : b i j ∈ fzR t x₁ x₂ := by
    rw [h.hR]
    exact Subgroup.subset_closure ⟨(i, j), rfl⟩
  have h2 : b i j ∈ T₂ := by
    rw [h.hT₂]
    exact Subgroup.mem_sup_left h1
  rw [h.hT₃]
  exact Subgroup.mem_sup_left h2

theorem fzl59b_t_mem (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) : t ∈ T₃ := by
  rw [h.grid.t_eq]
  exact T₃.mul_mem (T₃.mul_mem (fzl59b_b_mem h 0 0) (fzl59b_b_mem h 1 0)) (fzl59b_b_mem h 2 0)

theorem fzl59b_isConj_ts (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) :
    IsConj t (t * s) := by
  rcases h.u_cases with hu | hu
  · exact isConj_iff.mpr ⟨u, hu.t_conj⟩
  · exact isConj_iff.mpr ⟨u, hu.t_conj⟩

theorem fzl59b_isConj_tz (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) :
    IsConj t (t * (x₁ * x₂) ^ 2) := by
  have hq0 : b 2 1 * b 0 0 = b 0 0 * b 2 1 := (h.grid.comm 2 0 (by decide) 1 0).eq
  have hq1 : b 2 1 * b 1 0 = b 1 0 * b 2 1 := (h.grid.comm 2 1 (by decide) 1 0).eq
  have hqp : b 2 1 * b 2 0 * (b 2 1)⁻¹ = (b 2 0)⁻¹ := (h.grid.quat 2).2.2.1
  have hA : b 2 1 * (b 0 0 * b 1 0) = (b 0 0 * b 1 0) * b 2 1 := by
    rw [← mul_assoc, hq0, mul_assoc, hq1, ← mul_assoc]
  refine isConj_iff.mpr ⟨b 2 1, ?_⟩
  rw [← h.z3]
  calc b 2 1 * t * (b 2 1)⁻¹
      = b 2 1 * (b 0 0 * b 1 0 * b 2 0) * (b 2 1)⁻¹ := by rw [← h.grid.t_eq]
    _ = ((b 2 1 * (b 0 0 * b 1 0)) * b 2 0) * (b 2 1)⁻¹ := by group
    _ = (((b 0 0 * b 1 0) * b 2 1) * b 2 0) * (b 2 1)⁻¹ := by rw [hA]
    _ = (b 0 0 * b 1 0) * (b 2 1 * b 2 0 * (b 2 1)⁻¹) := by group
    _ = (b 0 0 * b 1 0) * (b 2 0)⁻¹ := by rw [hqp]
    _ = (b 0 0 * b 1 0) * (b 2 0 * b 2 0 ^ 2) := by rw [(h.grid.quat 2).inv_eq]
    _ = t * b 2 0 ^ 2 := by rw [h.grid.t_eq]; group

end CFSG.OddStandard.SmallF3.FritzII
