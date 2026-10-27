module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

variable {V : Type} [CommGroup V] {G : Type} [Group G]

section Exponent

theorem mul_self_eq_one' (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v * v = 1 := by
  rw [← pow_two]
  exact hV v

end Exponent

section Eps

variable (ρ : G →* MulAut V)

theorem rho_rho (y z : G) (w : V) : ρ y (ρ z w) = ρ (y * z) w := by
  rw [map_mul]
  rfl

@[expose] def eps (y : G) (w : V) : V :=
  w * ρ y w * ρ (y ^ 2) w

theorem eps_mul (y : G) (v w : V) : eps ρ y (v * w) = eps ρ y v * eps ρ y w := by
  simp only [eps]
  rw [(ρ y).map_mul, (ρ (y ^ 2)).map_mul]
  ac_rfl

theorem rho_eps {y : G} (hy : y ^ 3 = 1) (w : V) : ρ y (eps ρ y w) = eps ρ y w := by
  have h3 : ρ (y * y ^ 2) w = w := by
    rw [← pow_succ' y 2, hy, map_one]
    rfl
  simp only [eps]
  rw [(ρ y).map_mul, (ρ y).map_mul, rho_rho, rho_rho, ← pow_two, h3]
  ac_rfl

theorem eps_eq_self_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {y : G} {w : V} (hw : ρ y w = w) :
    eps ρ y w = w := by
  have h2 : ρ (y ^ 2) w = w := by
    rw [pow_two, ← rho_rho, hw, hw]
  simp only [eps, hw, h2]
  rw [mul_self_eq_one' hV, one_mul]

@[expose] def fixSub (y : G) : Subgroup V where
  carrier := {w | ρ y w = w}
  one_mem' := map_one _
  mul_mem' := fun {a b} ha hb => by
    change ρ y (a * b) = a * b
    change ρ y a = a at ha
    change ρ y b = b at hb
    rw [(ρ y).map_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    change ρ y a⁻¹ = a⁻¹
    change ρ y a = a at ha
    rw [(ρ y).map_inv, ha]

theorem mem_fixSub {y : G} {w : V} : w ∈ fixSub ρ y ↔ ρ y w = w := Iff.rfl

@[expose] def epsHom (y : G) : V →* V where
  toFun := eps ρ y
  map_one' := by simp [eps]
  map_mul' := eps_mul ρ y

@[expose] def kerSub (y : G) : Subgroup V := (epsHom ρ y).ker

theorem mem_kerSub {y : G} {w : V} : w ∈ kerSub ρ y ↔ eps ρ y w = 1 := Iff.rfl

theorem fixSub_inf_kerSub (hV : ∀ v : V, v ^ 2 = 1) (y : G) :
    fixSub ρ y ⊓ kerSub ρ y = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hf, hk⟩
  rw [Subgroup.mem_bot]
  have h1 := eps_eq_self_of_fixed ρ hV ((mem_fixSub ρ).1 hf)
  rw [← h1]
  exact (mem_kerSub ρ).1 hk

theorem eps_rho_self {y : G} (hy : y ^ 3 = 1) (w : V) : eps ρ y (ρ y w) = eps ρ y w := by
  have h3 : ρ (y ^ 2 * y) w = w := by
    rw [← pow_succ y 2, hy, map_one]
    rfl
  simp only [eps]
  rw [rho_rho, rho_rho, ← pow_two, h3]
  ac_rfl

theorem eps_rho_sq {y : G} (hy : y ^ 3 = 1) (w : V) : eps ρ y (ρ (y ^ 2) w) = eps ρ y w := by
  have h3 : ρ (y * y ^ 2) w = w := by
    rw [← pow_succ' y 2, hy, map_one]
    rfl
  have h4 : ρ (y ^ 2 * y ^ 2) w = ρ y w := by
    have : y ^ 2 * y ^ 2 = y * y ^ 3 := by group
    rw [this, hy, mul_one]
  simp only [eps]
  rw [rho_rho, rho_rho, h3, h4]
  ac_rfl

theorem card_modEq_one [Finite V] {y : G} (hy : y ^ 3 = 1) (P : Subgroup V)
    (hP : ∀ w ∈ P, ρ y w ∈ P) (hfix : ∀ w ∈ P, ρ y w = w → w = 1) :
    Nat.card P ≡ 1 [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype P := Fintype.ofFinite P
  let f : Function.End P := fun x => ⟨ρ y x, hP x x.2⟩
  have hgp : ∀ (n : ℕ) (x : P), (((f ^ n) x : P) : V) = ρ (y ^ n) x := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, pow_zero, map_one]
      rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ]
      exact (ih (f x)).trans (by rw [rho_rho])
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hgp, hy, map_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf3
  have hfp : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (map_one (ρ y))⟩, fun ⟨x, hx⟩ => ?_⟩
    have h1 : ρ y x = x := congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext (hfix x x.2 h1))
  rw [hfp, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem eq_bot_or_four_le {P : Subgroup V} [Finite V] (h : Nat.card P ≡ 1 [MOD 3]) :
    P = ⊥ ∨ 4 ≤ Nat.card P := by
  have hpos : 0 < Nat.card P := Nat.card_pos
  have h1 : Nat.card P % 3 = 1 := h
  by_cases h4 : Nat.card P = 1
  · exact Or.inl (Subgroup.card_eq_one.1 h4)
  · exact Or.inr (by omega)

end Eps

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
