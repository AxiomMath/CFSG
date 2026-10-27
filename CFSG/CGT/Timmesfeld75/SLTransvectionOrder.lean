module

public import CFSG.CGT.Timmesfeld75.SLTransvectionComm

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def sact (g : SL(n, F)) (x : Fin n → F) : Fin n → F :=
  (g : Matrix (Fin n) (Fin n) F) *ᵥ x

theorem sact_mul (g h : SL(n, F)) (x : Fin n → F) : sact (g * h) x = sact g (sact h x) := by
  simp only [sact, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem sact_one (x : Fin n → F) : sact (1 : SL(n, F)) x = x := by
  simp [sact]

theorem sact_add (g : SL(n, F)) (x y : Fin n → F) : sact g (x + y) = sact g x + sact g y :=
  Matrix.mulVec_add _ _ _

theorem sact_smul (g : SL(n, F)) (r : F) (x : Fin n → F) : sact g (r • x) = r • sact g x :=
  Matrix.mulVec_smul _ _ _

theorem eq_of_sact {g h : SL(n, F)} (hgh : ∀ x, sact g x = sact h x) : g = h := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simpa [Matrix.toLin'_apply, sact] using hgh x

theorem sact_pow_succ (g : SL(n, F)) (k : ℕ) (x : Fin n → F) :
    sact (g ^ (k + 1)) x = sact g (sact (g ^ k) x) := by
  rw [pow_succ', sact_mul]

theorem vec_add_self [CharP F 2] (v : Fin n → F) : v + v = 0 := by
  ext i
  simp [CharTwo.add_self_eq_zero]

section Data

variable {u₁ u₂ : SL(n, F)} {f₁ f₂ : Module.Dual F (Fin n → F)} {v₁ v₂ : Fin n → F}

theorem sact_mul_transvection (hu₁ : ∀ x, sact u₁ x = x + f₁ x • v₁)
    (hu₂ : ∀ x, sact u₂ x = x + f₂ x • v₂) (x : Fin n → F) :
    sact (u₁ * u₂) x = x + (f₂ x • v₂ + (f₁ x + f₁ v₂ * f₂ x) • v₁) := by
  rw [sact_mul, hu₂ x, hu₁, map_add, map_smul, smul_eq_mul]
  simp only [add_smul, mul_comm (f₂ x) (f₁ v₂)]
  abel

theorem mul_pow_four_eq_one [CharP F 2] (hfv₁ : f₁ v₁ = 0) (hfv₂ : f₂ v₂ = 0)
    (hu₁ : ∀ x, sact u₁ x = x + f₁ x • v₁) (hu₂ : ∀ x, sact u₂ x = x + f₂ x • v₂)
    (hc : f₁ v₂ * f₂ v₁ = 0) : (u₁ * u₂) ^ 4 = 1 := by
  set a := f₁ v₂ with ha
  set b := f₂ v₁ with hb
  let N : (Fin n → F) → (Fin n → F) := fun x => f₂ x • v₂ + (f₁ x + a * f₂ x) • v₁
  have hw : ∀ x, sact (u₁ * u₂) x = x + N x := fun x => sact_mul_transvection hu₁ hu₂ x
  have hNadd : ∀ x y, N (x + y) = N x + N y := by
    intro x y
    simp only [N, map_add, add_smul, mul_add]
    abel
  have hN0 : N 0 = 0 := by simp [N]
  have hf₂N : ∀ x, f₂ (N x) = b * (f₁ x + a * f₂ x) := by
    intro x
    simp only [N, map_add, map_smul, smul_eq_mul, hfv₂]
    rw [← hb]
    ring
  have hf₁N : ∀ x, f₁ (N x) = a * f₂ x := by
    intro x
    simp only [N, map_add, map_smul, smul_eq_mul, hfv₁]
    rw [← ha]
    ring
  have hN3 : ∀ x, N (N (N x)) = 0 := by
    intro x
    have h2 : f₂ (N (N x)) = 0 := by
      rw [hf₂N, hf₁N, hf₂N]
      linear_combination (f₂ x + b * (f₁ x + a * f₂ x)) * hc
    have h1 : f₁ (N (N x)) = 0 := by
      rw [hf₁N, hf₂N]
      linear_combination (f₁ x + a * f₂ x) * hc
    show f₂ (N (N x)) • v₂ + (f₁ (N (N x)) + a * f₂ (N (N x))) • v₁ = 0
    rw [h2, h1]
    simp
  have hsq : ∀ y, sact ((u₁ * u₂) * (u₁ * u₂)) y = y + N (N y) := by
    intro y
    have h := vec_add_self (N y)
    rw [sact_mul, hw y, hw (y + N y), hNadd y (N y)]
    calc y + N y + (N y + N (N y)) = y + (N y + N y) + N (N y) := by abel
      _ = y + N (N y) := by rw [h, add_zero]
  have e : (u₁ * u₂) ^ 4 = ((u₁ * u₂) * (u₁ * u₂)) * ((u₁ * u₂) * (u₁ * u₂)) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  apply eq_of_sact
  intro y
  rw [e, sact_mul, hsq y, hsq (y + N (N y)), sact_one, hNadd y (N (N y)),
    hNadd (N y) (N (N (N y))), hN3 y, hN0, add_zero]
  have h := vec_add_self (N (N y))
  calc y + N (N y) + N (N y) = y + (N (N y) + N (N y)) := by abel
    _ = y := by rw [h, add_zero]

theorem mul_self_eq_one_of_transvection [CharP F 2] {u : SL(n, F)} {f : Module.Dual F (Fin n → F)}
    {v : Fin n → F} (hfv : f v = 0) (hu : ∀ x, sact u x = x + f x • v) : u * u = 1 := by
  apply eq_of_sact
  intro x
  rw [sact_mul, hu x, hu (x + f x • v), sact_one]
  simp only [map_add, map_smul, hfv, add_zero, smul_eq_mul, mul_zero]
  calc x + f x • v + f x • v = x + (f x • v + f x • v) := by abel
    _ = x := by rw [vec_add_self, add_zero]

theorem fix_of_commute_transvection [CharP F 2] {ζ u : SL(n, F)}
    {f : Module.Dual F (Fin n → F)} {v : Fin n → F} (hu : ∀ x, sact u x = x + f x • v)
    (hv : v ≠ 0) {x₀ : Fin n → F} (hx₀ : f x₀ = 1) (hcomm : ζ * u = u * ζ) (hζ : ζ * ζ = 1) :
    sact ζ v = v ∧ ∀ x, f (sact ζ x) = f x := by
  have hc : ∀ x, f x • sact ζ v = f (sact ζ x) • v := by
    intro x
    have h := congrArg (fun g => sact g x) hcomm
    simp only [sact_mul] at h
    rw [hu x, hu (sact ζ x), sact_add, sact_smul] at h
    exact add_left_cancel h
  set l : F := f (sact ζ x₀) with hl
  have hζv : sact ζ v = l • v := by
    have := hc x₀
    rwa [hx₀, one_smul] at this
  have hfx : ∀ x, f (sact ζ x) = f x * l := by
    intro x
    have := hc x
    rw [hζv, smul_smul] at this
    exact (smul_left_injective F hv this).symm
  have hl2 : l * l = 1 := by
    have h1 : sact (ζ * ζ) v = v := by rw [hζ, sact_one]
    rw [sact_mul, hζv, sact_smul, hζv, smul_smul] at h1
    exact smul_left_injective F hv (show (l * l) • v = (1 : F) • v by rw [h1, one_smul])
  have hl1 : l = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h3 : (l + 1) * (l + 1) = 0 := by linear_combination hl2 + (l + 1) * h2
    have h4 := mul_self_eq_zero.1 h3
    linear_combination h4 - h2
  exact ⟨by rw [hζv, hl1, one_smul], fun x => by rw [hfx x, hl1, mul_one]⟩

theorem not_two_dvd_orderOf_mul [CharP F 2] [Finite F] (hfv₁ : f₁ v₁ = 0) (hfv₂ : f₂ v₂ = 0)
    (hu₁ : ∀ x, sact u₁ x = x + f₁ x • v₁) (hu₂ : ∀ x, sact u₂ x = x + f₂ x • v₂)
    (hc : f₁ v₂ * f₂ v₁ ≠ 0) : ¬ 2 ∣ orderOf (u₁ * u₂) := by
  have ha : f₁ v₂ ≠ 0 := left_ne_zero_of_mul hc
  have hb : f₂ v₁ ≠ 0 := right_ne_zero_of_mul hc
  have hv₁ : v₁ ≠ 0 := fun h => hb (by rw [h, map_zero])
  have hv₂ : v₂ ≠ 0 := fun h => ha (by rw [h, map_zero])
  have hx₁ : f₁ ((f₁ v₂)⁻¹ • v₂) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ ha]
  have hx₂ : f₂ ((f₂ v₁)⁻¹ • v₁) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hb]
  have hu₁2 : u₁ * u₁ = 1 := mul_self_eq_one_of_transvection hfv₁ hu₁
  have hu₂2 : u₂ * u₂ = 1 := mul_self_eq_one_of_transvection hfv₂ hu₂
  by_contra h2
  have ho0 : 0 < orderOf (u₁ * u₂) := orderOf_pos _
  obtain ⟨j, hj⟩ := h2
  have hζ2 : (u₁ * u₂) ^ j * (u₁ * u₂) ^ j = 1 := by
    rw [← pow_add, ← two_mul, ← hj]
    exact pow_orderOf_eq_one _
  have hζ1 : (u₁ * u₂) ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hζinv : ((u₁ * u₂) ^ j)⁻¹ = (u₁ * u₂) ^ j := inv_eq_of_mul_eq_one_right hζ2
  have hu₁i : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁2
  have hc₁ : (u₁ * u₂) ^ j * u₁ = u₁ * (u₁ * u₂) ^ j := by
    have h1 : u₁ * (u₁ * u₂) * u₁⁻¹ = (u₁ * u₂)⁻¹ := by
      rw [hu₁i, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hu₂2, hu₁i]
      calc u₁ * (u₁ * u₂) * u₁ = (u₁ * u₁) * u₂ * u₁ := by group
        _ = u₂ * u₁ := by rw [hu₁2, one_mul]
    have h2 : u₁ * (u₁ * u₂) ^ j * u₁⁻¹ = (u₁ * u₂) ^ j := by
      rw [← conj_pow, h1, inv_pow, hζinv]
    rw [hu₁i] at h2
    calc (u₁ * u₂) ^ j * u₁ = (u₁ * (u₁ * u₂) ^ j * u₁) * u₁ := by rw [h2]
      _ = u₁ * (u₁ * u₂) ^ j := by
          calc u₁ * (u₁ * u₂) ^ j * u₁ * u₁ = u₁ * (u₁ * u₂) ^ j * (u₁ * u₁) := by group
            _ = u₁ * (u₁ * u₂) ^ j := by rw [hu₁2, mul_one]
  have hc₂ : (u₁ * u₂) ^ j * u₂ = u₂ * (u₁ * u₂) ^ j := by
    have e : u₂ = u₁ * (u₁ * u₂) := by
      calc u₂ = (u₁ * u₁) * u₂ := by rw [hu₁2, one_mul]
        _ = u₁ * (u₁ * u₂) := by group
    have hcomm : Commute ((u₁ * u₂) ^ j) (u₁ * u₂) := (Commute.refl _).pow_left j
    calc (u₁ * u₂) ^ j * u₂ = (u₁ * u₂) ^ j * (u₁ * (u₁ * u₂)) := by rw [← e]
      _ = ((u₁ * u₂) ^ j * u₁) * (u₁ * u₂) := by group
      _ = u₁ * (u₁ * u₂) ^ j * (u₁ * u₂) := by rw [hc₁]
      _ = u₁ * ((u₁ * u₂) ^ j * (u₁ * u₂)) := by group
      _ = u₁ * ((u₁ * u₂) * (u₁ * u₂) ^ j) := by rw [hcomm.eq]
      _ = u₂ * (u₁ * u₂) ^ j := by rw [← mul_assoc, ← e]
  obtain ⟨hζv₁, hζf₁⟩ := fix_of_commute_transvection hu₁ hv₁ hx₁ hc₁ hζ2
  obtain ⟨hζv₂, hζf₂⟩ := fix_of_commute_transvection hu₂ hv₂ hx₂ hc₂ hζ2
  have hspan : ∀ k : ℕ, ∀ x : Fin n → F, ∃ s t : F,
      sact ((u₁ * u₂) ^ k) x = x + s • v₁ + t • v₂ := by
    intro k
    induction k with
    | zero => exact fun x => ⟨0, 0, by simp [sact_one]⟩
    | succ k ih =>
      intro x
      obtain ⟨s, t, hst⟩ := ih x
      refine ⟨s + (f₁ (x + s • v₁ + t • v₂) + f₁ v₂ * f₂ (x + s • v₁ + t • v₂)),
        t + f₂ (x + s • v₁ + t • v₂), ?_⟩
      rw [sact_pow_succ, hst, sact_mul_transvection hu₁ hu₂]
      simp only [add_smul]
      abel
  apply hζ1
  apply eq_of_sact
  intro x
  obtain ⟨s, t, hst⟩ := hspan j x
  have e₁ := hζf₁ x
  have e₂ := hζf₂ x
  rw [hst] at e₁ e₂
  simp only [map_add, map_smul, smul_eq_mul, hfv₁, hfv₂, mul_zero, add_zero] at e₁ e₂
  have ht : t = 0 := by
    have : t * f₁ v₂ = 0 := by linear_combination e₁
    exact (mul_eq_zero.1 this).resolve_right ha
  have hs : s = 0 := by
    have : s * f₂ v₁ = 0 := by linear_combination e₂
    exact (mul_eq_zero.1 this).resolve_right hb
  rw [hst, ht, hs, sact_one]
  simp

end Data

theorem IsTransvection.orderOf_mul_cases [CharP F 2] [Finite F] {u₁ u₂ : SL(n, F)}
    (h₁ : IsTransvection u₁) (h₂ : IsTransvection u₂) :
    orderOf (u₁ * u₂) ∣ 4 ∨ Odd (orderOf (u₁ * u₂)) := by
  obtain ⟨f₁, v₁, hfv₁, -, hu₁⟩ := h₁.exists_data
  obtain ⟨f₂, v₂, hfv₂, -, hu₂⟩ := h₂.exists_data
  by_cases hc : f₁ v₂ * f₂ v₁ = 0
  · left
    exact orderOf_dvd_of_pow_eq_one (mul_pow_four_eq_one hfv₁ hfv₂ hu₁ hu₂ hc)
  · right
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (not_two_dvd_orderOf_mul hfv₁ hfv₂ hu₁ hu₂ hc))

end CFSG.CGT.Timmesfeld75
