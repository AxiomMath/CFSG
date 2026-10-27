module

public import CFSG.CGT.M24S.NSOrbit3

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond

variable {G : Type} [Group G]

theorem mul_sq_three {a b d z : G} (hzd : d * z = z * d) (hz : z * z = 1)
    (ha : a * a = 1) (hb : b * b = 1) (hd : d * d = 1) (hba : b * a = a * b * z)
    (hda : d * a = a * d * z) (hdb : d * b = b * d * z) : a * b * d * (a * b * d) = z := by
  have h1 : a * b * a = b * z := by
    rw [mul_assoc, hba, ← mul_assoc, ← mul_assoc, ha, one_mul]
  have h2 : a * d * a = d * z := by
    rw [mul_assoc, hda, ← mul_assoc, ← mul_assoc, ha, one_mul]
  have h3 : b * d * b = d * z := by
    rw [mul_assoc, hdb, ← mul_assoc, ← mul_assoc, hb, one_mul]
  have h4 : a * b * d * a = b * d := by
    calc a * b * d * a = (a * b * a) * (a * d * a) := by
          rw [show (a * b * a) * (a * d * a) = a * b * (a * a) * d * a by group, ha, mul_one]
      _ = b * (z * d) * z := by rw [h1, h2]; group
      _ = b * d := by rw [← hzd, mul_assoc, mul_assoc, hz, mul_one]
  calc a * b * d * (a * b * d) = (a * b * d * a) * b * d := by group
    _ = b * d * b * d := by rw [h4]
    _ = d * z * d := by rw [h3]
    _ = z := by rw [mul_assoc, ← hzd, ← mul_assoc, hd, one_mul]

theorem commute_conj_iff {k x y : G} :
    (k * x * k⁻¹) * (k * y * k⁻¹) = (k * y * k⁻¹) * (k * x * k⁻¹) ↔ x * y = y * x := by
  constructor
  · intro h
    have h1 := congrArg (fun g => k⁻¹ * g * k) h
    simpa [mul_assoc] using h1
  · intro h
    rw [show (k * x * k⁻¹) * (k * y * k⁻¹) = k * (x * y) * k⁻¹ by group, h]
    group

theorem commute_mul_left_iff {x y z : G} (hzy : y * z = z * y) :
    (x * z) * y = y * (x * z) ↔ x * y = y * x := by
  constructor
  · intro h
    have h1 : x * y * z = y * x * z := by
      calc x * y * z = x * (y * z) := mul_assoc _ _ _
        _ = x * z * y := by rw [hzy, ← mul_assoc]
        _ = y * (x * z) := h
        _ = y * x * z := (mul_assoc _ _ _).symm
    exact mul_right_cancel h1
  · intro h
    rw [mul_assoc, ← hzy, ← mul_assoc, h, mul_assoc]

variable {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem mul_eq_of_not_commute {x y : G} (hx : x ∈ c.E) (hy : y ∈ c.E) (h : ¬ x * y = y * x) :
    y * x = x * y * t := by
  rcases conj_mem_E_eq c hy hx with h1 | h1
  · exact absurd (by rw [← h1, inv_mul_cancel_right] : y * x = (y * x * y⁻¹) * y) (fun h2 =>
      h (by rw [h2, h1]))
  · calc y * x = y * x * y⁻¹ * y := by group
      _ = x * t * y := by rw [h1]
      _ = x * y * t := by rw [mul_assoc, ← commute_t (c.E_le hy), ← mul_assoc]

theorem top_conj_inv {k e : G} (hk : k ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (he : e ∈ c.E) :
    top (c.mat (k⁻¹ * e * k⁻¹⁻¹)) = vecMul (top (c.mat e)) (blk (c.mat k)) := by
  rw [top_conj c (inv_mem hk) he, inv_inv]

theorem wset_comm (hF : Fixes c v₀) {e₁ e₂ : G} (h₁ : Wset c e₁) (h₂ : Wset c e₂) :
    e₁ * e₂ = e₂ * e₁ := by
  have central : ∀ {x : G}, x ∈ c.E → x * t = t * x := fun hx => commute_t (c.E_le hx)
  have hTt : ∀ {e : G}, Wset c e → top (c.mat e) = 0 → e = 1 ∨ e = t := fun he h0 =>
    wset_T c (mem_T_of_top_eq_zero c he.1 h0) he
  by_cases hv₁ : top (c.mat e₁) = 0
  · rcases hTt h₁ hv₁ with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (central h₂.1).symm
  by_cases hv₂ : top (c.mat e₂) = 0
  · rcases hTt h₂ hv₂ with rfl | rfl
    · rw [one_mul, mul_one]
    · exact central h₁.1
  by_cases hv : top (c.mat e₂) = top (c.mat e₁)
  · rcases wset_unique c h₁ h₂ hv hv₁ with rfl | rfl
    · rfl
    · rw [mul_assoc, ← central h₁.1]
  obtain ⟨e₃, h₃, hv₃⟩ := exists_wset c hF (top (c.mat e₁) + top (c.mat e₂))
  have hv₃0 : top (c.mat e₃) ≠ 0 := by rw [hv₃]; exact add_ne_zero_of_ne _ _ (Ne.symm hv)
  obtain ⟨B, hB1, hB21, hB32⟩ := exists_cycle hv₁ hv₂ (Ne.symm hv)
  have hB13 : vecMul (top (c.mat e₁)) B = top (c.mat e₁) + top (c.mat e₂) := by
    have h := hB32
    rw [add_vecMul, hB21] at h
    calc vecMul (top (c.mat e₁)) B = (vecMul (top (c.mat e₁)) B + top (c.mat e₁)) +
          top (c.mat e₁) := by rw [add_assoc, vec_add_self, add_zero]
      _ = top (c.mat e₁) + top (c.mat e₂) := by rw [h, add_comm]
  obtain ⟨k, hk, hkB⟩ := c.exists_mem_cent B hB1
  have hk' : k⁻¹ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := inv_mem hk
  have hf₁ := wset_unique c h₃ (wset_conj c hk' h₁)
    (by rw [top_conj_inv c hk h₁.1, hkB, hB13, hv₃]) hv₃0
  have hf₂ := wset_unique c h₁ (wset_conj c hk' h₂) (by rw [top_conj_inv c hk h₂.1, hkB, hB21])
    hv₁
  have hf₃ := wset_unique c h₂ (wset_conj c hk' h₃)
    (by rw [top_conj_inv c hk h₃.1, hkB, hv₃, hB32]) hv₂
  have hc : ∀ {x y x' y' : G}, x ∈ c.E → y ∈ c.E → (x' = x ∨ x' = x * t) →
      (y' = y ∨ y' = y * t) → (x' * y' = y' * x' ↔ x * y = y * x) := by
    intro x y x' y' hx hy hx' hy'
    have step : ∀ {a b : G}, a ∈ c.E → b ∈ c.E → (a * t * b = b * (a * t) ↔ a * b = b * a) :=
      fun ha hb => commute_mul_left_iff (central hb)
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact Iff.rfl
    · rw [eq_comm, step hy hx, eq_comm]
    · exact step hx hy
    · rw [step hx (c.E.mul_mem hy (c.T_le_E c.mem)), eq_comm, step hy hx, eq_comm]
  have hE₁ := h₁.1
  have hE₂ := h₂.1
  have hE₃ := h₃.1
  have i12 : e₁ * e₂ = e₂ * e₁ ↔ e₃ * e₁ = e₁ * e₃ :=
    (commute_conj_iff (k := k⁻¹)).symm.trans (hc hE₃ hE₁ hf₁ hf₂)
  have i23 : e₂ * e₃ = e₃ * e₂ ↔ e₁ * e₂ = e₂ * e₁ :=
    (commute_conj_iff (k := k⁻¹)).symm.trans (hc hE₁ hE₂ hf₂ hf₃)
  by_contra h12
  have h31 : ¬ e₃ * e₁ = e₁ * e₃ := fun h => h12 (i12.2 h)
  have h23 : ¬ e₂ * e₃ = e₃ * e₂ := fun h => h12 (i23.1 h)
  have hsq := mul_sq_three (central hE₃) (by rw [← pow_two]; exact c.z_sq)
    (by rw [← pow_two]; exact h₁.2.1) (by rw [← pow_two]; exact h₂.2.1)
    (by rw [← pow_two]; exact h₃.2.1) (mul_eq_of_not_commute c hE₁ hE₂ h12)
    (mul_eq_of_not_commute c hE₁ hE₃ (fun h => h31 h.symm))
    (mul_eq_of_not_commute c hE₂ hE₃ h23)
  have hT : e₁ * e₂ * e₃ ∈ T := by
    apply mem_T_of_top_eq_zero c (c.E.mul_mem (c.E.mul_mem hE₁ hE₂) hE₃)
    rw [top_mul_of_mem_E c (c.E.mul_mem hE₁ hE₂) hE₃, top_mul_of_mem_E c hE₁ hE₂, hv₃,
      vec_add_self]
  rw [mul_self_of_mem_T c hT] at hsq
  exact c.z_ne_one hsq.symm

end CFSG.CGT.M24S.NSB
