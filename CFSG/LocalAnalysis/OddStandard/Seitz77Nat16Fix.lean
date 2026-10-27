module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Norm
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

variable {F : Type*} [Field F]

section Count

open CFSG.GH74.KGroups

theorem card_fix_twisted_gf16 (μ : GF16) :
    Nat.card {x : GF16 // μ * x ^ 2 = x} ≤ 4 ∧ Nat.card {x : GF16 // μ * x ^ 4 = x} ≤ 4 ∧
      Nat.card {x : GF16 // μ * x ^ 8 = x} ≤ 4 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  revert μ
  decide +kernel

theorem card_fix_twisted (hF : Nat.card F = 16) (μ : F) {j : ℕ} (hj0 : 0 < j) (hj4 : j < 4) :
    Nat.card {x : F // μ * x ^ 2 ^ j = x} ≤ 4 := by
  obtain ⟨φ⟩ := Weights16.exists_ringEquiv hF
  obtain ⟨μ', rfl⟩ := φ.surjective μ
  have key : ∀ k : ℕ, Nat.card {x : F // φ μ' * x ^ k = x} =
      Nat.card {x : GF16 // μ' * x ^ k = x} := by
    intro k
    refine Nat.card_congr (Equiv.subtypeEquiv φ.symm.toEquiv fun x => ?_)
    show φ μ' * x ^ k = x ↔ μ' * φ.symm x ^ k = φ.symm x
    rw [← φ.symm.injective.eq_iff, map_mul, map_pow, RingEquiv.symm_apply_apply]
  have h := card_fix_twisted_gf16 μ'
  interval_cases j
  · rw [pow_one, key]; exact h.1
  · rw [show 2 ^ 2 = 4 from rfl, key]; exact h.2.1
  · rw [show 2 ^ 3 = 8 from rfl, key]; exact h.2.2

end Count

section Borel

variable (N : (F × F) ≃+ (F × F)) {j : ℕ}
  (hsl : ∀ (a : F) (u : F × F),
    N (a * u.1, a * u.2) = (a ^ 2 ^ j * (N u).1, a ^ 2 ^ j * (N u).2))

include hsl

theorem semilinear_form (x y : F) :
    N (x, y) = (x ^ 2 ^ j * (N (1, 0)).1 + y ^ 2 ^ j * (N (0, 1)).1,
      x ^ 2 ^ j * (N (1, 0)).2 + y ^ 2 ^ j * (N (0, 1)).2) := by
  have h1 : ((x, y) : F × F) = (x * (1 : F), x * (0 : F)) + (y * (0 : F), y * (1 : F)) := by
    ext <;> simp
  have h2 := hsl x (1, 0)
  have h3 := hsl y (0, 1)
  simp only at h2 h3
  rw [h1, map_add, h2, h3]
  ext <;> simp

variable (hU : ∃ c' : F, ∀ u, N (natHom (uE 1) u) = natHom (uE c') (N u))

include hU

theorem borel_form :
    ∃ p s t : F, p ≠ 0 ∧ t ≠ 0 ∧ ∀ x y : F,
      N (x, y) = (p * x ^ 2 ^ j + s * y ^ 2 ^ j, t * y ^ 2 ^ j) := by
  obtain ⟨c', hc'⟩ := hU
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    have h := hc' (0, 1)
    have h0 : natHom (uE (0 : F)) (N (0, 1)) = N (0, 1) := by
      rw [uE_zero, map_one]
      rfl
    rw [h0] at h
    have := N.injective h
    simp at this
  have h1 := hc' (1, 0)
  simp only [natHom_uE, mul_zero, add_zero] at h1
  have h2 := congrArg Prod.fst h1
  simp only at h2
  have hr : (N (1, 0)).2 = 0 := by
    have : c' * (N (1, 0)).2 = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left hc'0
  have hform : ∀ x y : F, N (x, y) = ((N (1, 0)).1 * x ^ 2 ^ j + (N (0, 1)).1 * y ^ 2 ^ j,
      (N (0, 1)).2 * y ^ 2 ^ j) := by
    intro x y
    rw [semilinear_form N hsl x y, hr]
    ext <;> simp [mul_comm]
  refine ⟨(N (1, 0)).1, (N (0, 1)).1, (N (0, 1)).2, ?_, ?_, hform⟩
  · intro hp
    have h3 : N (1, 0) = N 0 := by
      rw [map_zero]
      ext
      · exact hp
      · exact hr
    have := N.injective h3
    simp [Prod.ext_iff] at this
  · intro ht
    obtain ⟨u, hu⟩ := N.surjective (0, 1)
    have h3 := congrArg Prod.snd (hform u.1 u.2)
    rw [Prod.mk.eta, hu, ht] at h3
    simp at h3

end Borel

section BorelCounts

variable (hF : Nat.card F = 16) {N : (F × F) ≃+ (F × F)} {j : ℕ} {p s t : F}
  (hform : ∀ x y : F, N (x, y) = (p * x ^ 2 ^ j + s * y ^ 2 ^ j, t * y ^ 2 ^ j))

include hform

theorem borel_unip {c c' : F}
    (h : ∀ u, N (natHom (uE c) u) = natHom (uE c') (N u)) : c' * t = p * c ^ 2 ^ j := by
  have h1 := h (0, 1)
  simp only [natHom_uE, mul_one, zero_add] at h1
  rw [hform, hform] at h1
  simp only [mul_one, one_pow, zero_pow (pow_ne_zero j two_ne_zero), mul_zero,
    zero_add, Prod.mk.injEq] at h1
  have h2 := h1.1
  linear_combination -h2

include hF

theorem card_fix_borel_le (hj0 : 0 < j) (hj4 : j < 4) :
    Nat.card {u : F × F // N u = u} ≤ 16 := by
  classical
  have := charP_two hF
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  let x₀ : F → F := fun y => if h : ∃ x, N (x, y) = (x, y) then h.choose else 0
  have hx₀ : ∀ y, (∃ x, N (x, y) = (x, y)) → N (x₀ y, y) = (x₀ y, y) := by
    intro y hy
    simp only [x₀, hy, ↓reduceDIte]
    exact hy.choose_spec
  have hfix : ∀ u : F × F, N u = u → p * u.1 ^ 2 ^ j + s * u.2 ^ 2 ^ j = u.1 ∧
      t * u.2 ^ 2 ^ j = u.2 := by
    intro u hu
    have := hform u.1 u.2
    rw [Prod.mk.eta, hu] at this
    exact ⟨(Prod.ext_iff.1 this.symm).1, (Prod.ext_iff.1 this.symm).2⟩
  let ϕ : {u : F × F // N u = u} → {y : F // t * y ^ 2 ^ j = y} × {z : F // p * z ^ 2 ^ j = z} :=
    fun u => (⟨u.1.2, (hfix u.1 u.2).2⟩, ⟨u.1.1 + x₀ u.1.2, by
      have h1 := (hfix u.1 u.2).1
      have h0 := hfix (x₀ u.1.2, u.1.2) (hx₀ u.1.2 ⟨u.1.1, u.2⟩)
      simp only at h0
      rw [add_pow_char_pow, mul_add]
      calc p * u.1.1 ^ 2 ^ j + p * x₀ u.1.2 ^ 2 ^ j =
          (p * u.1.1 ^ 2 ^ j + s * u.1.2 ^ 2 ^ j) + (p * x₀ u.1.2 ^ 2 ^ j + s * u.1.2 ^ 2 ^ j) -
            2 * (s * u.1.2 ^ 2 ^ j) := by ring
        _ = u.1.1 + x₀ u.1.2 := by
          rw [h1, h0.1, CharTwo.two_eq_zero, zero_mul, sub_zero]⟩)
  have hinj : Function.Injective ϕ := by
    intro u u' h
    have h1 := congrArg (fun w => (w.1 : F)) h
    have h2 := congrArg (fun w => (w.2 : F)) h
    simp only [ϕ] at h1 h2
    apply Subtype.ext
    apply Prod.ext
    · rw [h1] at h2
      exact add_right_cancel h2
    · exact h1
  calc Nat.card {u : F × F // N u = u}
      ≤ Nat.card ({y : F // t * y ^ 2 ^ j = y} × {z : F // p * z ^ 2 ^ j = z}) :=
        Nat.card_le_card_of_injective ϕ hinj
    _ = Nat.card {y : F // t * y ^ 2 ^ j = y} * Nat.card {z : F // p * z ^ 2 ^ j = z} :=
        Nat.card_prod _ _
    _ ≤ 4 * 4 := Nat.mul_le_mul (card_fix_twisted hF t hj0 hj4) (card_fix_twisted hF p hj0 hj4)
    _ = 16 := by norm_num

end BorelCounts

section BorelGL

variable (hF : Nat.card F = 16) {ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)}
  (hρ : Function.Injective ρ) {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
  (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
    Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)
  (n : GL (Fin 8) (ZMod 2)) (hnU : ∀ c : F, ∃ c' : F, n * ρ (uE c) * n⁻¹ = ρ (uE c'))
  {j : ℕ} (hsl : IsSemilinear j (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))

include hΦ hnU hsl

theorem borel_normalizer_form :
    ∃ p s t : F, p ≠ 0 ∧ t ≠ 0 ∧
      (∀ x y : F, coordMap Φ n (x, y) = (p * x ^ 2 ^ j + s * y ^ 2 ^ j, t * y ^ 2 ^ j)) ∧
      ∀ c : F, n * ρ (uE c) * n⁻¹ = ρ (uE ((p / t) * c ^ 2 ^ j)) := by
  have hsl' := (isSemilinear_iff_coord Φ n j).1 hsl
  have hU : ∃ c' : F, ∀ u, coordMap Φ n (natHom (uE 1) u) = natHom (uE c') (coordMap Φ n u) := by
    obtain ⟨c', hc'⟩ := hnU 1
    exact ⟨c', coordMap_natural hΦ n hc'⟩
  obtain ⟨p, s, t, hp, ht, hform⟩ := borel_form (coordMap Φ n) hsl' hU
  refine ⟨p, s, t, hp, ht, hform, fun c => ?_⟩
  obtain ⟨c', hc'⟩ := hnU c
  have h1 := borel_unip hform (coordMap_natural hΦ n hc')
  rw [hc']
  congr 2
  field_simp
  linear_combination h1

omit hnU hsl
include hF

theorem card_fix_le (hnU : ∀ c : F, ∃ c' : F, n * ρ (uE c) * n⁻¹ = ρ (uE c'))
    (hsl : IsSemilinear j (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))
    (hj0 : 0 < j) (hj4 : j < 4) :
    Nat.card {v : Fin 8 → ZMod 2 // (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v} ≤ 16 := by
  obtain ⟨p, s, t, hp, ht, hform, -⟩ := borel_normalizer_form hΦ n hnU hsl
  have h1 : Nat.card {v : Fin 8 → ZMod 2 // (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v} =
      Nat.card {u : F × F // coordMap Φ n u = u} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (coord Φ).toEquiv fun v => ?_)
    show (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v ↔ coordMap Φ n (coord Φ v) = coord Φ v
    rw [coordMap_apply, (coord Φ).injective.eq_iff]
  rw [h1]
  exact card_fix_borel_le hF hform hj0 hj4

end BorelGL

end Nat16

end CFSG.OddStandard.Seitz77
