module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33A

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {n : ℕ}

theorem le_fixAlt_of_odd_normal_centralizer {τ : Perm (Fin n)} (hτ : τ * τ = 1)
    {N : Subgroup (alternatingGroup (Fin n))} (hodd : Odd (Nat.card N))
    (hc : ∀ g ∈ N, (g : Perm (Fin n)) * τ = τ * g)
    (hn : ∀ b : alternatingGroup (Fin n), (b : Perm (Fin n)) * τ = τ * b →
      ∀ g ∈ N, b * g * b⁻¹ ∈ N) : N ≤ fixAlt τ := by
  classical
  have hpair : ∀ g ∈ N, ∀ x z : Fin n, τ x ≠ x → τ z ≠ z → z ≠ x → z ≠ τ x →
      (g : Perm (Fin n)) * (swap x (τ x) * swap z (τ z)) =
        (swap x (τ x) * swap z (τ z)) * g := by
    intro g hg x z hx hz hzx hzτx
    set b₀ : Perm (Fin n) := swap x (τ x) * swap z (τ z) with hb₀
    have hb₀A : b₀ ∈ alternatingGroup (Fin n) := by
      rw [Perm.mem_alternatingGroup, hb₀, Perm.sign_mul, Perm.sign_swap (Ne.symm hx),
        Perm.sign_swap (Ne.symm hz)]
      rfl
    have hb₀τ : b₀ * τ = τ * b₀ := by
      rw [hb₀, mul_assoc, swap_mul_comm_of_involution hτ z, ← mul_assoc,
        swap_mul_comm_of_involution hτ x, mul_assoc]
    set b : alternatingGroup (Fin n) := ⟨b₀, hb₀A⟩ with hbdef
    have hgτ := hc g hg
    have hgτ' : ∀ v, (g : Perm (Fin n)) (τ v) = τ ((g : Perm (Fin n)) v) := fun v => by
      rw [← Perm.mul_apply, hgτ, Perm.mul_apply]
    have hconj : (g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ =
        swap ((g : Perm (Fin n)) x) (τ ((g : Perm (Fin n)) x)) *
          swap ((g : Perm (Fin n)) z) (τ ((g : Perm (Fin n)) z)) := by
      rw [← hgτ', ← hgτ', swap_apply_apply, swap_apply_apply, hb₀]
      group
    have hcomm : ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) * b₀ =
        b₀ * ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) := by
      rw [hconj, hb₀]
      set s₁ := swap ((g : Perm (Fin n)) x) (τ ((g : Perm (Fin n)) x))
      set s₂ := swap ((g : Perm (Fin n)) z) (τ ((g : Perm (Fin n)) z))
      set s₃ := swap x (τ x)
      set s₄ := swap z (τ z)
      have h13 : s₁ * s₃ = s₃ * s₁ := pairSwap_commute hτ _ _
      have h14 : s₁ * s₄ = s₄ * s₁ := pairSwap_commute hτ _ _
      have h23 : s₂ * s₃ = s₃ * s₂ := pairSwap_commute hτ _ _
      have h24 : s₂ * s₄ = s₄ * s₂ := pairSwap_commute hτ _ _
      calc s₁ * s₂ * (s₃ * s₄) = s₁ * (s₂ * s₃) * s₄ := by group
        _ = s₁ * (s₃ * s₂) * s₄ := by rw [h23]
        _ = (s₁ * s₃) * (s₂ * s₄) := by group
        _ = (s₃ * s₁) * (s₄ * s₂) := by rw [h13, h24]
        _ = s₃ * (s₁ * s₄) * s₂ := by group
        _ = s₃ * (s₄ * s₁) * s₂ := by rw [h14]
        _ = s₃ * s₄ * (s₁ * s₂) := by group
    have hb2 : b₀ * b₀ = 1 := by
      rw [hb₀]
      calc swap x (τ x) * swap z (τ z) * (swap x (τ x) * swap z (τ z)) =
          swap x (τ x) * (swap z (τ z) * swap x (τ x)) * swap z (τ z) := by group
        _ = swap x (τ x) * (swap x (τ x) * swap z (τ z)) * swap z (τ z) := by
            rw [pairSwap_commute hτ z x]
        _ = 1 := by simp [← mul_assoc]
    have hk : g * b * g⁻¹ * b⁻¹ ∈ N := by
      have h1 : b * g⁻¹ * b⁻¹ ∈ N := hn b hb₀τ g⁻¹ (inv_mem hg)
      have h2 : g * (b * g⁻¹ * b⁻¹) ∈ N := mul_mem hg h1
      simpa [mul_assoc] using h2
    have hk2 : (g * b * g⁻¹ * b⁻¹) * (g * b * g⁻¹ * b⁻¹) = 1 := by
      apply Subtype.ext
      have hbinv : (b⁻¹ : alternatingGroup (Fin n)) = b := by
        apply inv_eq_of_mul_eq_one_right
        exact Subtype.ext hb2
      rw [hbinv]
      change ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) *
        ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) = 1
      have hgb2 : ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
          ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) = 1 := by
        calc ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) =
            (g : Perm (Fin n)) * (b₀ * b₀) * (g : Perm (Fin n))⁻¹ := by group
          _ = 1 := by rw [hb2]; group
      calc ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) *
          ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) =
          ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            (b₀ * ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹)) * b₀ := by group
        _ = ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            (((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) * b₀) * b₀ := by rw [hcomm]
        _ = (((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹)) * (b₀ * b₀) := by group
        _ = 1 := by rw [hgb2, hb2, one_mul]
    have hk1 : g * b * g⁻¹ * b⁻¹ = 1 := by
      have h1 : orderOf (⟨_, hk⟩ : N) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq]; exact Subtype.ext hk2)
      have h2 : orderOf (⟨_, hk⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      have h3 : orderOf (⟨_, hk⟩ : N) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · rw [h] at h2
          exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
      have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
      exact this
    have h6 := congrArg Subtype.val hk1
    change (g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * (b⁻¹ : alternatingGroup _) = 1 at h6
    have hbinv : ((b⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) = b₀⁻¹ := rfl
    rw [hbinv] at h6
    calc (g : Perm (Fin n)) * b₀ = ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀⁻¹) *
        (b₀ * g) := by group
      _ = b₀ * g := by rw [h6, one_mul]
  intro g hg
  have hog : Odd (orderOf (g : Perm (Fin n))) := by
    rw [Subgroup.orderOf_coe]
    have h1 : orderOf g ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _
    exact hodd.of_dvd_nat h1
  rw [mem_fixAlt]
  intro z hz
  rw [Finset.mem_compl]
  intro hzτ
  exact (Perm.mem_support.mp hz)
    (apply_eq_of_odd_commute_pairs hτ (hc g hg) hog (hpair g hg) hzτ)

end CFSG.ComponentClassification.SolMax
