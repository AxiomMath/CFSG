module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open scoped MatrixGroups

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

structure Phi6JData (G : Type) [Group G] (J : Subgroup G) (F : Type) [Field F] (r q : ℕ) where
  E₀ : Subgroup G
  w : G
  P : Sylow r G
  u : G
  x₁ : G
  x₀ : G
  c : G
  a : G
  b : G
  y₁ : G
  y₂ : G
  y₃ : G
  y₄ : G
  θ : SL(2, F) →* G
  hEp : ∀ x ∈ E₀, x ^ r = 1
  hEc : Nat.card E₀ = r ^ 2
  hww : w * w = 1
  hw1 : w ≠ 1
  hwJ : w ∈ J
  hwE : ∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹
  hEP : E₀ ≤ (P : Subgroup G)
  hPc : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x
  hPΩ : ∀ x ∈ (P : Subgroup G), x ^ r = 1 → x ∈ E₀
  hu : u * u = 1
  hu1 : u ≠ 1
  hx₁E : x₁ ∈ E₀
  hx₁1 : x₁ ≠ 1
  huw : u * w = w * u
  hux : u * x₁ = x₁ * u
  hx₀E : x₀ ∈ E₀
  hx₀1 : x₀ ≠ 1
  hcE : c ∈ E₀
  hc1 : c ≠ 1
  hcJ : c ∈ J
  hθker : ∀ s, θ s = 1 ↔ s = 1 ∨ s = -1
  hθw : ∀ s, θ s * w = w * θ s
  hθx : ∀ s, θ s * x₀ = x₀ * θ s
  hθJ : ∀ s, θ s ∈ J
  hθcard : Nat.card θ.range = q * (q ^ 2 - 1) / 2
  hθsimple : 4 ≤ q → ⁅θ.range, θ.range⁆ = θ.range ∧ IsSimpleGroup θ.range
  hy₁ : y₁ * w = w * y₁
  hy₂ : y₂ * w = w * y₂
  hy₃ : y₃ * w = w * y₃
  hy₄ : y₄ * w = w * y₄
  ha : a = y₁ * y₂ * y₁⁻¹ * y₂⁻¹
  hb : b = y₃ * y₄ * y₃⁻¹ * y₄⁻¹
  haE : ∀ x ∈ E₀, a * x * a⁻¹ ∈ E₀
  hbE : ∀ x ∈ E₀, b * x * b⁻¹ ∈ E₀
  hab : a * b * a⁻¹ * b⁻¹ = w

theorem ne_one_of_inverts {G : Type*} [Group G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {w x : G}
    (hw : w * x * w⁻¹ = x⁻¹) (hxr : x ^ r = 1) (hx1 : x ≠ 1) : w ≠ 1 := by
  intro h
  rw [h, one_mul, inv_one, mul_one] at hw
  have h2 : x ^ 2 = 1 := by
    calc x ^ 2 = x * x := sq x
      _ = x * x⁻¹ := by rw [← hw]
      _ = 1 := mul_inv_cancel x
  have h3 : orderOf x ∣ Nat.gcd 2 r :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hxr)
  have h4 : Nat.gcd 2 r = 1 := (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)
  rw [h4] at h3
  exact hx1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))

section Commutators

variable {G : Type} [Group G] {J : Subgroup G} {F : Type} [Field F] {r q : ℕ}
  (D : Phi6JData G J F r q)

theorem Phi6JData.a_mem_commutator :
    D.a ∈ ⁅Subgroup.centralizer ({D.w} : Set G), Subgroup.centralizer ({D.w} : Set G)⁆ := by
  rw [D.ha]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_centralizer_singleton_iff.2 D.hy₁)
    (Subgroup.mem_centralizer_singleton_iff.2 D.hy₂)

theorem Phi6JData.b_mem_commutator :
    D.b ∈ ⁅Subgroup.centralizer ({D.w} : Set G), Subgroup.centralizer ({D.w} : Set G)⁆ := by
  rw [D.hb]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_centralizer_singleton_iff.2 D.hy₃)
    (Subgroup.mem_centralizer_singleton_iff.2 D.hy₄)

end Commutators

section Transport

variable {G H : Type} [Group G] [Group H] (e : G ≃* H)

theorem Phi6JData.card_comap_mulEquiv (E : Subgroup H) :
    Nat.card (E.comap e.toMonoidHom) = Nat.card E :=
  Nat.card_congr (e.toEquiv.subtypeEquiv (fun _ => Iff.rfl))

theorem Phi6JData.card_range_comp_mulEquiv {F : Type} [Field F] (θ : SL(2, F) →* G) :
    Nat.card ((e.toMonoidHom.comp θ).range) = Nat.card θ.range := by
  rw [MonoidHom.range_comp]
  exact Subgroup.card_map_of_injective e.injective

theorem Phi6JData.simple_perfect_range_comp_mulEquiv {F : Type} [Field F] (θ : SL(2, F) →* G)
    (h : ⁅θ.range, θ.range⁆ = θ.range ∧ IsSimpleGroup θ.range) :
    ⁅(e.toMonoidHom.comp θ).range, (e.toMonoidHom.comp θ).range⁆ = (e.toMonoidHom.comp θ).range ∧
      IsSimpleGroup (e.toMonoidHom.comp θ).range := by
  rw [MonoidHom.range_comp]
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_commutator, h.1]
  · haveI := h.2
    exact (Subgroup.equivMapOfInjective θ.range e.toMonoidHom e.injective).symm.isSimpleGroup

noncomputable def Phi6JData.transport {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ e x ∈ J') {F : Type} [Field F] {r q : ℕ} (D : Phi6JData H J' F r q) :
    Phi6JData G J F r q where
  E₀ := D.E₀.comap e.toMonoidHom
  w := e.symm D.w
  P := D.P.comapOfInjective e.toMonoidHom e.injective (fun x _ => ⟨e.symm x, e.apply_symm_apply x⟩)
  u := e.symm D.u
  x₁ := e.symm D.x₁
  x₀ := e.symm D.x₀
  c := e.symm D.c
  a := e.symm D.a
  b := e.symm D.b
  y₁ := e.symm D.y₁
  y₂ := e.symm D.y₂
  y₃ := e.symm D.y₃
  y₄ := e.symm D.y₄
  θ := e.symm.toMonoidHom.comp D.θ
  hEp := fun x hx => e.injective (by
    have h : e x ∈ D.E₀ := hx
    rw [map_pow, D.hEp (e x) h, map_one])
  hEc := (Phi6JData.card_comap_mulEquiv e D.E₀).trans D.hEc
  hww := by rw [← map_mul, D.hww, map_one]
  hw1 := fun h => D.hw1 (e.symm.injective (by rw [h, map_one]))
  hwJ := (hJ _).2 (by simpa using D.hwJ)
  hwE := fun x hx => e.injective (by
    have h : e x ∈ D.E₀ := hx
    rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply, D.hwE (e x) h])
  hEP := fun x hx => D.hEP hx
  hPc := fun x hx y hy => e.injective (by
    have hx' : e x ∈ (D.P : Subgroup H) := hx
    have hy' : e y ∈ (D.P : Subgroup H) := hy
    rw [map_mul, map_mul, D.hPc (e x) hx' (e y) hy'])
  hPΩ := fun x hx hxr => by
    have hx' : e x ∈ (D.P : Subgroup H) := hx
    exact D.hPΩ (e x) hx' (by rw [← map_pow, hxr, map_one])
  hu := by rw [← map_mul, D.hu, map_one]
  hu1 := fun h => D.hu1 (e.symm.injective (by rw [h, map_one]))
  hx₁E := by
    show e (e.symm D.x₁) ∈ D.E₀
    rw [e.apply_symm_apply]
    exact D.hx₁E
  hx₁1 := fun h => D.hx₁1 (e.symm.injective (by rw [h, map_one]))
  huw := by rw [← map_mul, ← map_mul, D.huw]
  hux := by rw [← map_mul, ← map_mul, D.hux]
  hx₀E := by
    show e (e.symm D.x₀) ∈ D.E₀
    rw [e.apply_symm_apply]
    exact D.hx₀E
  hx₀1 := fun h => D.hx₀1 (e.symm.injective (by rw [h, map_one]))
  hcE := by
    show e (e.symm D.c) ∈ D.E₀
    rw [e.apply_symm_apply]
    exact D.hcE
  hc1 := fun h => D.hc1 (e.symm.injective (by rw [h, map_one]))
  hcJ := (hJ _).2 (by simpa using D.hcJ)
  hθker := fun s => by
    have h : (e.symm.toMonoidHom.comp D.θ) s = e.symm (D.θ s) := rfl
    rw [h, MulEquiv.map_eq_one_iff]
    exact D.hθker s
  hθw := fun s => by
    show e.symm (D.θ s) * e.symm D.w = e.symm D.w * e.symm (D.θ s)
    rw [← map_mul, ← map_mul, D.hθw s]
  hθx := fun s => by
    show e.symm (D.θ s) * e.symm D.x₀ = e.symm D.x₀ * e.symm (D.θ s)
    rw [← map_mul, ← map_mul, D.hθx s]
  hθJ := fun s => (hJ _).2 (by
    show e (e.symm (D.θ s)) ∈ J'
    rw [e.apply_symm_apply]
    exact D.hθJ s)
  hθcard := by
    have := Phi6JData.card_range_comp_mulEquiv e.symm D.θ
    rw [this]
    exact D.hθcard
  hθsimple := fun hq => Phi6JData.simple_perfect_range_comp_mulEquiv e.symm D.θ (D.hθsimple hq)
  hy₁ := by rw [← map_mul, ← map_mul, D.hy₁]
  hy₂ := by rw [← map_mul, ← map_mul, D.hy₂]
  hy₃ := by rw [← map_mul, ← map_mul, D.hy₃]
  hy₄ := by rw [← map_mul, ← map_mul, D.hy₄]
  ha := by rw [D.ha]; simp
  hb := by rw [D.hb]; simp
  haE := fun x hx => by
    have h : e x ∈ D.E₀ := hx
    show e (e.symm D.a * x * (e.symm D.a)⁻¹) ∈ D.E₀
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact D.haE (e x) h
  hbE := fun x hx => by
    have h : e x ∈ D.E₀ := hx
    show e (e.symm D.b * x * (e.symm D.b)⁻¹) ∈ D.E₀
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact D.hbE (e x) h
  hab := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, D.hab]

end Transport

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
