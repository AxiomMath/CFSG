module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatPerm

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG.OddStandard.Solomon75.AhatData

theorem apply_comm {σ p : Perm (Fin 11)} (h : σ * p = p * σ) (x : Fin 11) :
    σ (p x) = p (σ x) := by
  have := congrArg (fun f : Perm (Fin 11) => f x) h
  simpa only [Perm.mul_apply] using this

theorem eq_u0_of_comm {σ : Perm (Fin 11)} (hs : sign σ = 1) (h1 : σ ≠ 1)
    (hc : ∀ p ∈ P0 11, σ * p = p * σ) : σ = u0 := by
  have c : ∀ p ∈ P0 11, ∀ x, σ (p x) = p (σ x) := fun p hp x => apply_comm (hc p hp) x
  have h10 : σ 10 = 10 := by
    have a1 := c g1 g1_mem 10
    have a2 := c g2 g2_mem 10
    have a3 := c g3 g3_mem 10
    rw [show g1 10 = 10 by decide] at a1
    rw [show g2 10 = 10 by decide] at a2
    rw [show g3 10 = 10 by decide] at a3
    exact (by decide : ∀ y : Fin 11, g1 y = y → g2 y = y → g3 y = y → y = 10) _
      a1.symm a2.symm a3.symm
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := by
    have a1 := c g1 g1_mem 0
    have a2 := c g2 g2_mem 0
    have a3 := c h23 h23_mem 0
    rw [show g1 0 = 0 by decide] at a1
    rw [show g2 0 = 0 by decide] at a2
    rw [show h23 0 = 0 by decide] at a3
    rcases (by decide : ∀ y : Fin 11, g1 y = y → g2 y = y → h23 y = y →
        y = 0 ∨ y = 1 ∨ y = 10) _ a1.symm a2.symm a3.symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (σ.injective (h.trans h10.symm)) (by decide)
  have h8 : σ 8 = 8 ∨ σ 8 = 9 := by
    have a2 := c g2 g2_mem 8
    have a3 := c g3 g3_mem 8
    rw [show g2 8 = 8 by decide] at a2
    rw [show g3 8 = 8 by decide] at a3
    rcases (by decide : ∀ y : Fin 11, g2 y = y → g3 y = y → y = 8 ∨ y = 9 ∨ y = 10)
        _ a2.symm a3.symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (σ.injective (h.trans h10.symm)) (by decide)
  have hform : ∀ x : Fin 11, σ x = if h : x.val < 8 then xo ⟨x.val, h⟩ (σ 0)
      else if x = 8 then σ 8 else if x = 9 then g1 (σ 8) else x := by
    intro x
    split_ifs with hx hx8 hx9
    · have := c (xo ⟨x.val, hx⟩) (xo_mem _) 0
      rwa [xo_zero, show (Fin.castLE (by norm_num) ⟨x.val, hx⟩ : Fin 11) = x from rfl] at this
    · rw [hx8]
    · have := c g1 g1_mem 8
      rwa [show g1 8 = 9 by decide, ← hx9] at this
    · have hx10 := (by decide : ∀ y : Fin 11, ¬ y.val < 8 → y ≠ 8 → y ≠ 9 → y = 10) x hx hx8 hx9
      rw [hx10, h10]
  rcases h0 with h0 | h0 <;> rcases h8 with h8 | h8
  · exact absurd (Equiv.ext fun x => by rw [hform x, h0, h8]; revert x; decide) h1
  · have e : σ = swap 8 9 := Equiv.ext fun x => by rw [hform x, h0, h8]; revert x; decide
    rw [e, sign_swap (by decide)] at hs
    exact absurd hs (by decide)
  · exact Equiv.ext fun x => by rw [hform x, h0, h8]; revert x; decide
  · have e : σ = u0 * swap 8 9 := Equiv.ext fun x => by rw [hform x, h0, h8]; revert x; decide
    rw [e, Perm.sign_mul, sign_u0, sign_swap (by decide)] at hs
    exact absurd hs (by decide)

theorem mem_zpowers_t3 {σ : Perm (Fin 11)} (hs : sign σ = 1)
    (hf : ∀ x : Fin 11, x.val < 8 → σ x = x) : σ ∈ zpowers t3 := by
  have hout : ∀ y : Fin 11, 8 ≤ y.val → σ y = 8 ∨ σ y = 9 ∨ σ y = 10 := by
    intro y hy
    refine (by decide : ∀ w : Fin 11, 8 ≤ w.val → w = 8 ∨ w = 9 ∨ w = 10) _ ?_
    by_contra h
    have h' : (σ y).val < 8 := by omega
    have e := σ.injective (hf (σ y) h')
    rw [e] at h'
    omega
  have hform : ∀ x : Fin 11, σ x =
      if x.val < 8 then x else if x = 8 then σ 8 else if x = 9 then σ 9 else σ 10 := by
    intro x
    split_ifs with hx hx8 hx9
    · exact hf x hx
    · rw [hx8]
    · rw [hx9]
    · rw [(by decide : ∀ y : Fin 11, ¬ y.val < 8 → y ≠ 8 → y ≠ 9 → y = 10) x hx hx8 hx9]
  have h8 := hout 8 (by decide)
  have h9 := hout 9 (by decide)
  have h10 := hout 10 (by decide)
  rcases h8 with h8 | h8 | h8 <;> rcases h9 with h9 | h9 | h9 <;>
    rcases h10 with h10 | h10 | h10
  all_goals first
    | exact absurd (σ.injective (h8.trans h9.symm)) (by decide)
    | exact absurd (σ.injective (h8.trans h10.symm)) (by decide)
    | exact absurd (σ.injective (h9.trans h10.symm)) (by decide)
    | skip
  · have e : σ = 1 := Equiv.ext fun x => by rw [hform x, h8, h9, h10]; revert x; decide
    rw [e]
    exact one_mem _
  · have e : σ = swap 9 10 := Equiv.ext fun x => by rw [hform x, h8, h9, h10]; revert x; decide
    rw [e, sign_swap (by decide)] at hs
    exact absurd hs (by decide)
  · have e : σ = swap 8 9 := Equiv.ext fun x => by rw [hform x, h8, h9, h10]; revert x; decide
    rw [e, sign_swap (by decide)] at hs
    exact absurd hs (by decide)
  · have e : σ = t3 := Equiv.ext fun x => by rw [hform x, h8, h9, h10]; revert x; decide
    rw [e]
    exact mem_zpowers t3
  · have e : σ = t3⁻¹ := Equiv.ext fun x => by rw [hform x, h8, h9, h10]; revert x; decide
    rw [e]
    exact inv_mem (mem_zpowers t3)
  · have e : σ = swap 8 10 := Equiv.ext fun x => by rw [hform x, h8, h9, h10]; revert x; decide
    rw [e, sign_swap (by decide)] at hs
    exact absurd hs (by decide)

theorem conj_t3_of_comm_u0 {σ : Perm (Fin 11)} (h : σ * u0 = u0 * σ) :
    σ * t3 * σ⁻¹ = t3 ∨ σ * t3 * σ⁻¹ = t3⁻¹ := by
  have hfix : ∀ y : Fin 11, 8 ≤ y.val → σ y = 8 ∨ σ y = 9 ∨ σ y = 10 := by
    intro y hy
    apply fix_u0
    rw [← apply_comm h y, (by decide : ∀ w : Fin 11, 8 ≤ w.val → u0 w = w) y hy]
  have e : σ * t3 * σ⁻¹ = swap (σ 8) (σ 9) * swap (σ 9) (σ 10) := by
    rw [swap_apply_apply, swap_apply_apply, t3]
    group
  rw [e]
  have h8 := hfix 8 (by decide)
  have h9 := hfix 9 (by decide)
  have h10 := hfix 10 (by decide)
  rcases h8 with h8 | h8 | h8 <;> rcases h9 with h9 | h9 | h9 <;>
    rcases h10 with h10 | h10 | h10
  all_goals first
    | exact absurd (σ.injective (h8.trans h9.symm)) (by decide)
    | exact absurd (σ.injective (h8.trans h10.symm)) (by decide)
    | exact absurd (σ.injective (h9.trans h10.symm)) (by decide)
    | (rw [h8, h9, h10]; decide)

theorem lt_of_comm_u0 {q : Perm (Fin 11)} (h : q * u0 = u0 * q) {x : Fin 11} (hx : x.val < 8) :
    (q x).val < 8 := by
  apply lt_of_u0_ne
  intro h'
  have e := apply_comm h x
  rw [h'] at e
  exact u0_ne_of_lt x hx (q.injective e)

end CFSG.OddStandard.GH71.AhatB
