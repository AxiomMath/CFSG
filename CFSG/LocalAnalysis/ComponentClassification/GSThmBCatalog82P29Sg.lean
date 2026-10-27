module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sd

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

namespace Model

variable {P : Type*} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

@[expose] def Q : Subgroup P where
  carrier := {x | x ∈ M.T ∨ M.t₀⁻¹ * x ∈ M.T}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · right
      have : M.t₀⁻¹ * (x * y) = (M.t₀⁻¹ * x * M.t₀) * (M.t₀⁻¹ * y) := by group
      rw [this]
      exact mul_mem (M.conj_t₀_mem_T hx) hy
    · right
      rw [← mul_assoc]
      exact mul_mem hx hy
    · left
      have : x * y = (M.t₀ * M.t₀) * (M.t₀⁻¹ * (M.t₀⁻¹ * x) * M.t₀) * (M.t₀⁻¹ * y) := by group
      rw [this]
      exact mul_mem (mul_mem M.t₀_sq_mem_T (M.conj_t₀_mem_T hx)) hy
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · right
      have : M.t₀⁻¹ * x⁻¹ = (M.t₀⁻¹ * (M.t₀⁻¹ * x)⁻¹ * M.t₀) * (M.t₀ * M.t₀)⁻¹ := by group
      rw [this]
      exact mul_mem (M.conj_t₀_mem_T (inv_mem hx)) (inv_mem M.t₀_sq_mem_T)

theorem T_le_Q : M.T ≤ M.Q := fun _ hx => Or.inl hx

theorem t₀_mem_Q : M.t₀ ∈ M.Q := Or.inr (by rw [inv_mul_cancel]; exact one_mem _)

theorem t₀_not_mem_T : M.t₀ ∉ M.T := by
  intro h
  have h1 := mem_centralizer_singleton_iff.mp (M.T_le h).1
  have h2 := M.t₀_conj_iota
  rw [mul_assoc, ← h1, inv_mul_cancel_left] at h2
  have h3 : M.z₁ ∈ M.D₁ ⊓ M.D₂ := ⟨M.z₁_mem_D₁, h2 ▸ M.iota_mem_D₂⟩
  rw [M.inf_D_eq_bot, mem_bot] at h3
  exact M.z₁_ne h3

theorem Q_le_L : M.Q ≤ L := by
  rintro x (hx | hx)
  · exact (M.T_le hx).2
  · have : x = M.t₀ * (M.t₀⁻¹ * x) := by group
    rw [this]
    exact mul_mem M.t₀_mem (M.T_le hx).2

theorem sq_mem_T {x : P} (hx : x ∈ M.Q) : x * x ∈ M.T := by
  rcases hx with hx | hx
  · exact mul_mem hx hx
  · have : x * x = (M.t₀ * M.t₀) * (M.t₀⁻¹ * (M.t₀⁻¹ * x) * M.t₀) * (M.t₀⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mul_mem M.t₀_sq_mem_T (M.conj_t₀_mem_T hx)) hx

theorem isPGroup_Q [Finite P] : IsPGroup 2 M.Q := by
  intro x
  refine ⟨2 * m + 3, ?_⟩
  apply Subtype.ext
  have hT : ∀ y ∈ M.T, y ^ 2 ^ (2 * m + 2) = 1 := by
    intro y hy
    have := pow_card_eq_one' (G := M.T) (x := ⟨y, hy⟩)
    rw [M.card_T] at this
    exact congrArg Subtype.val this
  rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_succ', pow_mul, _root_.sq]
  exact hT _ (M.sq_mem_T x.2)

theorem card_Q [Finite P] : Nat.card M.Q = 2 ^ (2 * m + 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := M.isPGroup_Q.exists_card_eq
  have h1 : 2 ^ (2 * m + 2) ∣ 2 ^ k := by
    rw [← M.card_T, ← hk]; exact Subgroup.card_dvd_of_le M.T_le_Q
  have h2 : 2 ^ k ∣ Nat.card L := by rw [← hk]; exact Subgroup.card_dvd_of_le M.Q_le_L
  have h3 : M.T ≠ M.Q := fun h => M.t₀_not_mem_T (h ▸ M.t₀_mem_Q)
  have h4 : 2 * m + 2 < k := by
    rcases Nat.lt_or_ge (2 * m + 2) k with h | h
    · exact h
    · exfalso
      apply h3
      apply Subgroup.eq_of_le_of_card_ge M.T_le_Q
      rw [hk, M.card_T]
      exact Nat.pow_le_pow_right (by norm_num) h
  have h5 : k ≤ 2 * m + 3 := by
    rcases Nat.lt_or_ge k (2 * m + 4) with h | h
    · omega
    · exact absurd ((pow_dvd_pow 2 h).trans h2) M.not_dvd_L
  rw [hk]
  congr 1
  omega

theorem center_Q {x : P} (hx : x ∈ M.Q) (hc : ∀ y ∈ M.Q, x * y = y * x) :
    x = 1 ∨ x = M.z₁ * ι := by
  have hxT : x ∈ M.T := by
    rcases hx with hx | hx
    · exact hx
    · exfalso
      set u := M.t₀⁻¹ * x with hu
      have hxe : x = M.t₀ * u := by rw [hu]; group
      obtain ⟨⟨b, c⟩, hbc⟩ := hx
      have key : ∀ a : DihedralGroup (2 ^ m), M.ρ₂ a ∈ M.D₁ := by
        intro a
        have h1 := hc (M.ρ a) (M.T_le_Q (M.D₁_le_T ⟨a, rfl⟩))
        have h2 : M.ρ₂ a = u * M.ρ a * u⁻¹ := by
          rw [M.ρ₂_apply]
          have : M.t₀⁻¹ * M.ρ a * M.t₀ = M.t₀⁻¹ * (x * M.ρ a * x⁻¹) * M.t₀ := by
            rw [h1, mul_inv_cancel_right]
          rw [this, hxe]
          group
        rw [h2, ← hbc, ρ₁₂_apply]
        have h3 := M.comm₁₂ a c
        have e : M.ρ b * M.ρ₂ c * M.ρ a * (M.ρ b * M.ρ₂ c)⁻¹ = M.ρ (b * a * b⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          calc M.ρ b * M.ρ₂ c * M.ρ a * (M.ρ b * M.ρ₂ c)⁻¹ =
              M.ρ b * (M.ρ₂ c * M.ρ a) * (M.ρ₂ c)⁻¹ * (M.ρ b)⁻¹ := by group
            _ = M.ρ b * (M.ρ a * M.ρ₂ c) * (M.ρ₂ c)⁻¹ * (M.ρ b)⁻¹ := by rw [h3]
            _ = M.ρ b * M.ρ a * (M.ρ b)⁻¹ := by group
        rw [e]
        exact ⟨_, rfl⟩
      have h1 : M.ρ₂ (r 1) ∈ M.D₁ ⊓ M.D₂ := ⟨key (r 1), ⟨r 1, rfl⟩⟩
      rw [M.inf_D_eq_bot, mem_bot] at h1
      have h2 : (r 1 : DihedralGroup (2 ^ m)) = 1 := M.ρ₂_injective (by rw [h1, map_one])
      have h3 := congrArg orderOf h2
      rw [orderOf_one, DihedralGroup.orderOf_r_one] at h3
      exact absurd h3 (by
        have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) M.two_le
        omega)
  rcases M.mem_T_of_comm hxT (fun y hy => hc y (M.T_le_Q hy)) with h | h | h | h
  · exact Or.inl h
  · exfalso
    have h1 := hc M.t₀ M.t₀_mem_Q
    have h2 : M.t₀⁻¹ * x * M.t₀ = x := by rw [mul_assoc, h1, inv_mul_cancel_left]
    rw [h, show M.z₁ = M.ρ (r (cc m)) from rfl, ← M.iota] at h2
    have h4 : M.z₁ ∈ M.D₁ ⊓ M.D₂ := ⟨M.z₁_mem_D₁, by
      rw [show M.z₁ = M.ρ (r (cc m)) from rfl, ← h2]; exact M.iota_mem_D₂⟩
    rw [M.inf_D_eq_bot, mem_bot] at h4
    exact M.z₁_ne h4
  · exfalso
    have h1 := hc M.t₀ M.t₀_mem_Q
    have h2 : M.t₀⁻¹ * x * M.t₀ = x := by rw [mul_assoc, h1, inv_mul_cancel_left]
    rw [h, M.t₀_conj_iota] at h2
    have h4 : M.z₁ ∈ M.D₁ ⊓ M.D₂ := ⟨M.z₁_mem_D₁, by rw [h2]; exact M.iota_mem_D₂⟩
    rw [M.inf_D_eq_bot, mem_bot] at h4
    exact M.z₁_ne h4
  · exact Or.inr h

end Model

end CFSG.ComponentClassification.GSThmB.P29
