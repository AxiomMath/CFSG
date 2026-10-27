module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModFox

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix
open Certificates.A5GL42 (Mat4)

private theorem two (a : Mat4) : a + a = 0 := by
  ext i j
  exact (by decide : ∀ x : ZMod 2, x + x = 0) (a i j)

private theorem eq_of_add_eq_zero {a b : Mat4} (h : a + b = 0) : a = b :=
  add_right_cancel (h.trans (two b).symm)

private theorem twoVec (v : Fin 4 → ZMod 2) : v + v = 0 := by
  ext i
  exact (by decide : ∀ x : ZMod 2, x + x = 0) (v i)

private theorem eq_of_add_eq_zero_vec {a b : Fin 4 → ZMod 2} (h : a + b = 0) : a = b :=
  add_right_cancel (h.trans (twoVec b).symm)

private theorem add_add_add_cancel (A B C : Mat4) : (A + B) + (B + C) = A + C := by
  rw [add_assoc, ← add_assoc B B C, two B, zero_add]

theorem blk_mulVec (a U : Mat4) (x y : Fin 4 → ZMod 2) :
    blk a U *ᵥ Sum.elim x y = Sum.elim (a *ᵥ x + U *ᵥ y) (a *ᵥ y) := by
  have h1 : (Sum.elim x y) ∘ Sum.inl = x := by ext i; simp
  have h2 : (Sum.elim x y) ∘ Sum.inr = y := by ext i; simp
  rw [blk, Matrix.fromBlocks_mulVec, h1, h2]
  simp

theorem blk_commute_u (a U : Mat4) : blk a U * blk 1 1 = blk 1 1 * blk a U := by
  rw [blk_mul, blk_mul]
  simp only [mul_one, one_mul]
  rw [add_comm]

theorem blk_u_mul_self : blk 1 1 * blk 1 1 = 1 := by
  rw [blk_mul, mul_one, two, blk_one]

theorem eq_blk_of_comm {M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)}
    (h : M * blk 1 1 = blk 1 1 * M) : ∃ a U : Mat4, M = blk a U := by
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, ?_⟩
  have h' : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ * blk 1 1
      = blk 1 1 * Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ := by
    rw [Matrix.fromBlocks_toBlocks]
    exact h
  rw [blk] at h'
  simp only [Matrix.fromBlocks_multiply, mul_one, mul_zero, add_zero, one_mul, zero_mul,
    zero_add] at h'
  obtain ⟨h11, h12, -, -⟩ := (Matrix.fromBlocks_inj).mp h'
  have h210 : M.toBlocks₂₁ = 0 := by
    have hh : M.toBlocks₁₁ + M.toBlocks₂₁ = M.toBlocks₁₁ + 0 := by
      rw [add_zero]
      exact h11.symm
    exact add_left_cancel hh
  have h220 : M.toBlocks₂₂ = M.toBlocks₁₁ := by
    have hh : M.toBlocks₁₁ + M.toBlocks₁₂ = M.toBlocks₂₂ + M.toBlocks₁₂ := by
      rw [h12, add_comm]
    exact (add_right_cancel hh).symm
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  simp only [blk, h210, h220]

@[expose] def Dm (m X : Mat4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  blk X (X * m + m * X)

theorem Dm_mul (m X Y : Mat4) : Dm m X * Dm m Y = Dm m (X * Y) := by
  have h2 : X * (Y * m + m * Y) + (X * m + m * X) * Y = (X * Y) * m + m * (X * Y) := by
    have hX : X * (Y * m + m * Y) = (X * Y) * m + (X * m) * Y := by
      rw [mul_add, ← mul_assoc X Y m, ← mul_assoc X m Y]
    have hY : (X * m + m * X) * Y = (X * m) * Y + (m * X) * Y := by
      rw [add_mul]
    rw [hX, hY, ← mul_assoc m X Y]
    exact add_add_add_cancel ((X * Y) * m) ((X * m) * Y) ((m * X) * Y)
  rw [Dm, Dm, Dm, blk_mul, h2]

theorem Dm_one (m : Mat4) : Dm m 1 = 1 := by
  rw [Dm, one_mul, mul_one, two, blk_one]

theorem Dm_mul_u (m X : Mat4) : Dm m X * blk 1 1 = blk X (X * m + m * X + X) := by
  rw [Dm, blk_mul]
  congr 1
  · rw [mul_one]
  · rw [mul_one, mul_one, add_comm]

theorem normalizer_core {m X W α α' : Mat4} (h : blk X W * Dm m α = Dm m α' * blk X W) :
    X * α = α' * X ∧ (W + X * m + m * X) * α = α' * (W + X * m + m * X) := by
  have key : blk (X * α) (X * (α * m + m * α) + W * α)
      = blk (α' * X) (α' * W + (α' * m + m * α') * X) := by
    have h' := h
    rw [Dm, Dm, blk_mul, blk_mul] at h'
    exact h'
  have h1 : X * α = α' * X := (blk_inj key).1
  have h2 : X * (α * m + m * α) + W * α = α' * W + (α' * m + m * α') * X :=
    (blk_inj key).2
  have h2' : X * α * m + X * m * α + W * α
      = α' * W + α' * m * X + m * α' * X := by
    have hh := h2
    rw [mul_add, add_mul] at hh
    rw [← mul_assoc X α m, ← mul_assoc X m α] at hh
    rw [← add_assoc] at hh
    exact hh
  have h1m : m * X * α = m * α' * X := by
    rw [mul_assoc m X α, h1, ← mul_assoc m α' X]
  have h2'' : α' * X * m + X * m * α + W * α
      = α' * W + α' * m * X + m * X * α := by
    have hh := h2'
    rw [h1] at hh
    rw [← h1m] at hh
    exact hh
  have hgoal : (W + X * m + m * X) * α = α' * (W + X * m + m * X) := by
    rw [add_mul, add_mul, mul_add, mul_add, ← mul_assoc α' X m, ← mul_assoc α' m X]
    have hCD :
        (α' * X * m + X * m * α + W * α) + (α' * W + α' * m * X + m * X * α) = 0 := by
      rw [h2'']
      exact two _
    refine eq_of_add_eq_zero ?_
    have hperm : (W * α + X * m * α + m * X * α) + (α' * W + α' * X * m + α' * m * X)
        = (α' * X * m + X * m * α + W * α) + (α' * W + α' * m * X + m * X * α) := by
      abel
    rw [hperm, hCD]
  exact ⟨h1, hgoal⟩

theorem Dm_form {m X W : Mat4} (hW : W + X * m + m * X = 0 ∨ W + X * m + m * X = X) :
    blk X W = Dm m X ∨ blk X W = Dm m X * blk 1 1 := by
  rcases hW with h0 | hX
  · left
    have h0' : W + (X * m + m * X) = 0 := by rw [← add_assoc]; exact h0
    have hWX : W = X * m + m * X := eq_of_add_eq_zero h0'
    rw [hWX, Dm]
  · right
    have h0' : W + (X * m + m * X) = X := by rw [← add_assoc]; exact hX
    have hWX : W = X + (X * m + m * X) := by
      have hh : W + (X + (X * m + m * X)) = 0 := by
        have e : W + (X + (X * m + m * X)) = (W + (X * m + m * X)) + X := by abel
        rw [e, h0', two]
      exact eq_of_add_eq_zero hh
    rw [Dm_mul_u, hWX, add_comm]

private theorem Dm_mulVec (m X : Mat4) (x y : Fin 4 → ZMod 2) :
    Dm m X *ᵥ Sum.elim x y
      = Sum.elim (X *ᵥ x + (X * m + m * X) *ᵥ y) (X *ᵥ y) := by
  rw [Dm, blk_mulVec]

private theorem Dm_fix_iff (m X : Mat4) (x y : Fin 4 → ZMod 2) :
    (Dm m X *ᵥ Sum.elim x y = Sum.elim x y) ↔
      X *ᵥ (x + m *ᵥ y) = x + m *ᵥ y ∧ X *ᵥ y = y := by
  constructor
  · intro hv
    rw [Dm_mulVec] at hv
    have hy : X *ᵥ y = y := by
      have hh := congrArg (fun w => w ∘ Sum.inr) hv
      simpa using hh
    have hx0 : X *ᵥ x + (X * m + m * X) *ᵥ y = x := by
      have hh := congrArg (fun w => w ∘ Sum.inl) hv
      simpa using hh
    have e1 : (X * m + m * X) *ᵥ y = X *ᵥ (m *ᵥ y) + m *ᵥ y := by
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec y X m, ← Matrix.mulVec_mulVec y m X, hy]
    refine ⟨?_, hy⟩
    rw [Matrix.mulVec_add]
    apply eq_of_add_eq_zero_vec
    have hx' : (X *ᵥ x + X *ᵥ (m *ᵥ y)) + m *ᵥ y = x := by
      rw [e1] at hx0
      simpa only [add_assoc] using hx0
    calc (X *ᵥ x + X *ᵥ (m *ᵥ y)) + (x + m *ᵥ y)
        = ((X *ᵥ x + X *ᵥ (m *ᵥ y)) + m *ᵥ y) + x := by abel
      _ = x + x := by rw [hx']
      _ = 0 := twoVec x
  · rintro ⟨hu, hy⟩
    rw [Dm_mulVec]
    have e1 : (X * m + m * X) *ᵥ y = X *ᵥ (m *ᵥ y) + m *ᵥ y := by
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec y X m, ← Matrix.mulVec_mulVec y m X, hy]
    have hx : X *ᵥ x + (X * m + m * X) *ᵥ y = x := by
      rw [e1]
      have hu' : X *ᵥ x + X *ᵥ (m *ᵥ y) = x + m *ᵥ y := by
        simpa only [Matrix.mulVec_add] using hu
      rw [← add_assoc, hu', add_assoc, twoVec, add_zero]
    rw [hx, hy]

private def phi (m : Mat4) :
    (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) where
  toFun v := (v ∘ Sum.inl + m *ᵥ (v ∘ Sum.inr), v ∘ Sum.inr)
  invFun p := Sum.elim (p.1 + m *ᵥ p.2) p.2
  left_inv v := by
    have h1 : (v ∘ Sum.inl + m *ᵥ (v ∘ Sum.inr)) + m *ᵥ (v ∘ Sum.inr) = v ∘ Sum.inl := by
      rw [add_assoc, twoVec, add_zero]
    change Sum.elim ((v ∘ Sum.inl + m *ᵥ (v ∘ Sum.inr)) + m *ᵥ (v ∘ Sum.inr)) (v ∘ Sum.inr) = v
    rw [h1]
    ext s
    cases s <;> rfl
  right_inv p := by
    have h1 : p.1 + m *ᵥ p.2 + m *ᵥ p.2 = p.1 := by
      rw [add_assoc, twoVec, add_zero]
    have hc : Sum.elim (p.1 + m *ᵥ p.2) p.2 ∘ Sum.inl = p.1 + m *ᵥ p.2 := by
      ext i; simp
    have hd : Sum.elim (p.1 + m *ᵥ p.2) p.2 ∘ Sum.inr = p.2 := by
      ext i; simp
    apply Prod.ext
    · change (Sum.elim (p.1 + m *ᵥ p.2) p.2 ∘ Sum.inl)
          + m *ᵥ (Sum.elim (p.1 + m *ᵥ p.2) p.2 ∘ Sum.inr) = p.1
      rw [hc, hd, h1]
    · change Sum.elim (p.1 + m *ᵥ p.2) p.2 ∘ Sum.inr = p.2
      exact hd

private theorem phi_fst (m : Mat4) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    (phi m v).1 = v ∘ Sum.inl + m *ᵥ (v ∘ Sum.inr) := rfl

private theorem phi_snd (m : Mat4) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    (phi m v).2 = v ∘ Sum.inr := rfl

private theorem Dm_fix_iff' (m X : Mat4) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    (Dm m X *ᵥ v = v) ↔
      X *ᵥ (v ∘ Sum.inl + m *ᵥ (v ∘ Sum.inr)) = (v ∘ Sum.inl + m *ᵥ (v ∘ Sum.inr)) ∧
        X *ᵥ (v ∘ Sum.inr) = v ∘ Sum.inr := by
  have hsum : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
    ext s; cases s <;> rfl
  have hh := Dm_fix_iff m X (v ∘ Sum.inl) (v ∘ Sum.inr)
  rw [hsum] at hh
  exact hh

theorem card_fix_Dm (m X : Mat4) :
    (Finset.univ.filter fun v : Fin 4 ⊕ Fin 4 → ZMod 2 => Dm m X *ᵥ v = v).card =
      (Finset.univ.filter fun x : Fin 4 → ZMod 2 => X *ᵥ x = x).card ^ 2 := by
  classical
  rw [← Fintype.card_subtype (fun v : Fin 4 ⊕ Fin 4 → ZMod 2 => Dm m X *ᵥ v = v),
      ← Fintype.card_subtype (fun x : Fin 4 → ZMod 2 => X *ᵥ x = x)]
  rw [pow_two, ← Fintype.card_prod]
  refine Fintype.card_congr ?_
  refine (Equiv.subtypeEquiv (phi m) ?_).trans Equiv.subtypeProdEquivProd
  intro v
  rw [phi_fst, phi_snd]
  exact Dm_fix_iff' m X v

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
