module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35a
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private theorem exists_iso {X : Type} [Finite X] (hX : Nat.card X = 4) (x₀ : X) :
    ∃ φ : Equiv.Perm X ≃* Equiv.Perm (Fin 4), ∃ e : X ≃ Fin 4, e x₀ = 0 ∧
      ∀ (p : Equiv.Perm X) (y : X), φ p (e y) = e (p y) := by
  let e0 : X ≃ Fin 4 := Finite.equivFinOfCardEq hX
  let e : X ≃ Fin 4 := e0.trans (Equiv.swap (e0 x₀) 0)
  exact ⟨e.permCongrHom, e, by simp [e], fun p y => by simp [Equiv.permCongrHom]⟩

private theorem fin4_trans :
    ∀ a : Equiv.Perm (Fin 4), a 0 = 0 → a ^ 3 = 1 → a ≠ 1 → ∀ y₁ : Fin 4, y₁ ≠ 0 →
      ∀ y : Fin 4, y ≠ 0 → ∃ k : ℕ, k < 3 ∧ (a ^ k) y₁ = y := by
  decide +kernel

private theorem fin4_faithful :
    ∀ a b : Equiv.Perm (Fin 4), a 0 = 0 → b 0 = 0 → a ^ 3 = 1 → a ≠ 1 → b ^ 2 = 1 →
      b * a * b⁻¹ = a⁻¹ → ∀ i : Fin 3, ∀ j : Fin 2, a ^ (i : ℕ) * b ^ (j : ℕ) = 1 →
        (i : ℕ) = 0 ∧ (j : ℕ) = 0 := by
  decide +kernel

theorem fz410_perm_top {X : Type} [Finite X] (hX : Nat.card X = 4)
    (H : Subgroup (Equiv.Perm X)) (x₀ : X) (htrans : ∀ y : X, ∃ h ∈ H, h x₀ = y)
    {a b : Equiv.Perm X} (ha : a ∈ H) (hb : b ∈ H) (ha0 : a x₀ = x₀) (hb0 : b x₀ = x₀)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb2 : b ^ 2 = 1) (hba : b * a * b⁻¹ = a⁻¹) :
    H = ⊤ := by
  obtain ⟨φ, e, he, hφ⟩ := exists_iso hX x₀
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply ha1
    have h1 : a = a⁻¹ := by simpa using hba
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel a
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [ha3, h2]; simp
  have htop : H.map φ.toMonoidHom = ⊤ := by
    apply fzl_perm4_eq_top (H.map φ.toMonoidHom)
    · intro i
      obtain ⟨h, hh, hh0⟩ := htrans (e.symm i)
      refine ⟨φ h, ⟨h, hh, rfl⟩, ?_⟩
      have := hφ h x₀
      rw [he] at this
      rw [this, hh0]
      simp
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · have := hφ a x₀
      rw [he, ha0, he] at this
      exact this
    · have := hφ b x₀
      rw [he, hb0, he] at this
      exact this
    · rw [← map_pow, ha3, map_one]
    · intro h
      apply ha1
      exact φ.injective (by rw [map_one]; exact h)
    · rw [← map_pow, hb2, map_one]
    · intro h
      apply hb1
      exact φ.injective (by rw [map_one]; exact h)
    · rw [← map_mul, ← map_inv, ← map_mul, hba, map_inv]
  rw [eq_top_iff]
  intro g _
  have hg : φ g ∈ H.map φ.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨g', hg', hgg⟩ := hg
  have : g' = g := φ.injective hgg
  rwa [this] at hg'

theorem fz410_perm_faithful {X : Type} [Finite X] (hX : Nat.card X = 4) (x₀ : X)
    {a b : Equiv.Perm X} (ha0 : a x₀ = x₀) (hb0 : b x₀ = x₀) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb2 : b ^ 2 = 1) (hba : b * a * b⁻¹ = a⁻¹) (i j : ℕ) (hi : i < 3) (hj : j < 2)
    (h : a ^ i * b ^ j = 1) : i = 0 ∧ j = 0 := by
  obtain ⟨φ, e, he, hφ⟩ := exists_iso hX x₀
  refine fin4_faithful (φ a) (φ b) ?_ ?_ ?_ ?_ ?_ ?_ ⟨i, hi⟩ ⟨j, hj⟩ ?_
  · have := hφ a x₀
    rw [he, ha0, he] at this
    exact this
  · have := hφ b x₀
    rw [he, hb0, he] at this
    exact this
  · rw [← map_pow, ha3, map_one]
  · intro h1
    apply ha1
    exact φ.injective (by rw [map_one]; exact h1)
  · rw [← map_pow, hb2, map_one]
  · rw [← map_mul, ← map_inv, ← map_mul, hba, map_inv]
  · rw [← map_pow, ← map_pow, ← map_mul, h, map_one]

theorem fz410_perm_trans {X : Type} [Finite X] (hX : Nat.card X = 4) (x₀ : X)
    {a σ : Equiv.Perm X} (ha0 : a x₀ = x₀) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hσ : σ x₀ ≠ x₀)
    (y : X) (hy : y ≠ x₀) : ∃ k : ℕ, k < 3 ∧ (a ^ k * σ) x₀ = y := by
  obtain ⟨φ, e, he, hφ⟩ := exists_iso hX x₀
  have h0 : (φ a) 0 = 0 := by
    have := hφ a x₀
    rw [he, ha0, he] at this
    exact this
  have h3 : (φ a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have h1 : φ a ≠ 1 := fun h => ha1 (φ.injective (by rw [map_one]; exact h))
  have hy1 : e (σ x₀) ≠ 0 := by
    intro h
    apply hσ
    apply e.injective
    rw [h, he]
  have hy2 : e y ≠ 0 := by
    intro h
    apply hy
    apply e.injective
    rw [h, he]
  obtain ⟨k, hk, hky⟩ := fin4_trans (φ a) h0 h3 h1 (e (σ x₀)) hy1 (e y) hy2
  refine ⟨k, hk, ?_⟩
  apply e.injective
  have h5 : ∀ n : ℕ, (φ a ^ n) (e (σ x₀)) = e ((a ^ n) (σ x₀)) := by
    intro n
    rw [← map_pow]
    exact hφ _ _
  rw [Equiv.Perm.mul_apply, ← h5, hky]

end CFSG.OddStandard.SmallF3.FritzII
