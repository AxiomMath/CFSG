module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Frame

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm Classical

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

theorem exists_not_mem_finset {N : ℕ} (T : Finset (Fin N)) (hT : T.card < N) : ∃ x, x ∉ T := by
  by_contra h
  push Not at h
  have : (Finset.univ : Finset (Fin N)) ⊆ T := fun x _ => h x
  have := Finset.card_le_card this
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

namespace E0Frame

variable (E : E0Frame θ ρ U π L S P ω Δ₀ Y)
include E

theorem exists_three_pts :
    ∃ x₁ x₂ x₃ r : Fin N, x₁ ∉ Δ₀ ∧ x₂ ∉ Δ₀ ∧ x₃ ∉ Δ₀ ∧ r ∉ Δ₀ ∧ x₂ ≠ x₁ ∧ x₂ ≠ ω x₁ ∧
      x₃ ≠ x₁ ∧ x₃ ≠ ω x₁ ∧ x₃ ≠ x₂ ∧ x₃ ≠ ω x₂ ∧ r ≠ x₁ ∧ r ≠ x₂ ∧ r ≠ x₃ := by
  have hN := E.hN
  have h4 := E.shape.card
  obtain ⟨x₁, hx₁⟩ := exists_not_mem_finset Δ₀ (by omega)
  obtain ⟨x₂, hx₂⟩ := exists_not_mem_finset (Δ₀ ∪ {x₁, ω x₁}) (by
    have := Finset.card_union_le Δ₀ ({x₁, ω x₁} : Finset (Fin N))
    have h2 : ({x₁, ω x₁} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
    omega)
  obtain ⟨x₃, hx₃⟩ := exists_not_mem_finset (Δ₀ ∪ {x₁, ω x₁, x₂, ω x₂}) (by
    have := Finset.card_union_le Δ₀ ({x₁, ω x₁, x₂, ω x₂} : Finset (Fin N))
    have h2 : ({x₁, ω x₁, x₂, ω x₂} : Finset (Fin N)).card ≤ 4 := Finset.card_le_four
    omega)
  obtain ⟨r, hr⟩ := exists_not_mem_finset (Δ₀ ∪ {x₁, x₂, x₃}) (by
    have := Finset.card_union_le Δ₀ ({x₁, x₂, x₃} : Finset (Fin N))
    have h2 : ({x₁, x₂, x₃} : Finset (Fin N)).card ≤ 3 := Finset.card_le_three
    omega)
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hx₂ hx₃ hr
  exact ⟨x₁, x₂, x₃, r, hx₁, hx₂.1, hx₃.1, hr.1, hx₂.2.1, hx₂.2.2, hx₃.2.1, hx₃.2.2.1,
    hx₃.2.2.2.1, hx₃.2.2.2.2, hr.2.1, hr.2.2.1, hr.2.2.2⟩

theorem three_cycle_not_normalize {x₁ x₂ x₃ : Fin N} (h1 : x₁ ∉ Δ₀)
    (h3 : x₃ ∉ Δ₀) (h12' : x₂ ≠ ω x₁) (h13 : x₃ ≠ x₁) (h13' : x₃ ≠ ω x₁)
    (h23 : x₃ ≠ x₂) {g : M} (hθg : θ g = swap x₁ x₂ * swap x₁ x₃) :
    ∃ s ∈ S, g * s * g⁻¹ ∉ S := by
  have hω1 : ω x₁ ∉ Δ₀ := E.shape.ω_not_mem h1
  have hne1 : ω x₁ ≠ x₁ := fun e => E.shape.ωfree x₁ h1 e
  obtain ⟨t, ht, hθt⟩ := (E.img (swap x₁ (ω x₁))).2 (E0Shape.swap_mem_E0grp h1)
  refine ⟨t, ht, fun hmem => ?_⟩
  have hE := (E.img _).1 ⟨_, hmem, rfl⟩
  have hconj : θ (g * t * g⁻¹) = swap x₃ (ω x₁) := by
    rw [map_mul, map_mul, map_inv, hθg, hθt]
    have e : (swap x₁ x₂ * swap x₁ x₃) * swap x₁ (ω x₁) * (swap x₁ x₂ * swap x₁ x₃)⁻¹ =
        swap ((swap x₁ x₂ * swap x₁ x₃) x₁) ((swap x₁ x₂ * swap x₁ x₃) (ω x₁)) :=
      (swap_apply_apply _ _ _).symm
    rw [e]
    have a1 : (swap x₁ x₂ * swap x₁ x₃) x₁ = x₃ := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h13 h23]
    have a2 : (swap x₁ x₂ * swap x₁ x₃) (ω x₁) = ω x₁ := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hne1 (fun e => h13' e.symm),
        swap_apply_of_ne_of_ne hne1 (fun e => h12' e.symm)]
    rw [a1, a2]
  rw [hconj] at hE
  obtain ⟨-, hpair⟩ := E0Shape.mem_E0grp_prop E.shape hE
  rcases hpair x₃ h3 with h | h
  · rw [swap_apply_left] at h
    exact h13' h.symm
  · rw [swap_apply_left] at h
    exact h13 (ω.injective h).symm

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
