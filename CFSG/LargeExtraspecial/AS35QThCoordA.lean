module

public import CFSG.LargeExtraspecial.AS35QThModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

theorem K_cases (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = frob ω := by
  obtain ⟨x, rfl⟩ := eF4.surjective c
  obtain ⟨⟨k, hk⟩⟩ := x
  interval_cases k
  · exact Or.inl (map_zero eF4)
  · exact Or.inr (Or.inl (map_one eF4))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [frob_omega, omega_eq, ← map_one eF4, ← map_add]
    rfl

theorem omega_mul_omega : ω * ω = frob ω := by rw [frob_apply, pow_two]

theorem frob_omega_mul_frob_omega : frob ω * frob ω = ω := by
  rw [← map_mul, omega_mul_omega, frob_frob]

theorem frob_omega_mul_omega : frob ω * ω = 1 := frob_mul_self omega_ne_zero

theorem omega_mul_frob_omega : ω * frob ω = 1 := mul_frob_self omega_ne_zero

theorem tr2_zero : tr2 0 = 0 := toK_injective (by rw [toK_tr2, map_zero, map_zero, add_zero])

theorem tr2_one : tr2 1 = 0 := toK_injective (by rw [toK_tr2, map_one, map_zero, add_self_K])

theorem tr2_omega : tr2 ω = 1 := toK_injective (by rw [toK_tr2, map_one, omega_add_frob])

theorem tr2_frob_omega : tr2 (frob ω) = 1 :=
  toK_injective (by rw [toK_tr2, map_one, frob_frob, add_comm, omega_add_frob])

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_V (x : V) : x + x = 0 := by
  rw [← one_smul (ZMod 2) x, ← add_smul]
  exact (show (1 + 1 : ZMod 2) = 0 by decide) ▸ zero_smul _ x

theorem neg_V (x : V) : -x = x := neg_eq_of_add_eq_zero_left (add_self_V x)

theorem eq_of_add_eq_zero_V {x y : V} (h : x + y = 0) : x = y := by
  rw [← neg_V y]; exact eq_neg_of_add_eq_zero_left h

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  rcases zmod2_cases c with rfl | rfl <;> decide

variable (ζ : V →ₗ[ZMod 2] V)

@[expose] noncomputable def act (c : K) (v : V) : V := tr2 (frob ω * c) • v + tr2 c • ζ v

theorem act_add_left (c c' : K) (v : V) : act ζ (c + c') v = act ζ c v + act ζ c' v := by
  simp only [act, mul_add, tr2_add, add_smul]
  abel

theorem act_zero_left (v : V) : act ζ 0 v = 0 := by
  simp only [act, mul_zero, tr2_zero, zero_smul, add_zero]

theorem act_one (v : V) : act ζ 1 v = v := by
  simp only [act, mul_one, tr2_frob_omega, tr2_one, one_smul, zero_smul, add_zero]

theorem act_omega (v : V) : act ζ ω v = ζ v := by
  simp only [act, frob_omega_mul_omega, tr2_one, tr2_omega, one_smul, zero_smul, zero_add]

theorem act_frob_omega (v : V) : act ζ (frob ω) v = v + ζ v := by
  simp only [act, frob_omega_mul_frob_omega, tr2_omega, tr2_frob_omega, one_smul]

variable {ζ}

theorem zeta_zeta (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (v : V) : ζ (ζ v) = ζ v + v := by
  have h := hζ v
  rw [add_assoc] at h
  exact eq_of_add_eq_zero_V h

theorem zeta_cube (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (v : V) : ζ (ζ (ζ v)) = v := by
  rw [zeta_zeta hζ v, map_add, zeta_zeta hζ v, add_comm (ζ v) v, add_assoc, add_self_V,
    add_zero]

theorem zeta_injective (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) : Function.Injective ζ := by
  intro x y h
  rw [← zeta_cube hζ x, ← zeta_cube hζ y, h]

theorem act_omega_mul (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (c : K) (v : V) :
    act ζ (ω * c) v = ζ (act ζ c v) := by
  rcases K_cases c with rfl | rfl | rfl | rfl
  · simp only [mul_zero, act_zero_left, map_zero]
  · rw [mul_one, act_omega, act_one]
  · rw [omega_mul_omega, act_frob_omega, act_omega, zeta_zeta hζ, add_comm]
  · rw [omega_mul_frob_omega, act_one, act_frob_omega, map_add, zeta_zeta hζ v, ← add_assoc,
      add_self_V, zero_add]

theorem act_eq_zero (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) {c : K} {v : V} (h : act ζ c v = 0) :
    c = 0 ∨ v = 0 := by
  rcases K_cases c with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rw [act_one] at h; exact Or.inr h
  · rw [act_omega] at h; exact Or.inr (zeta_injective hζ (by rw [h, map_zero]))
  · rw [act_frob_omega] at h
    right
    have h2 := hζ v
    rw [add_assoc, add_comm (ζ v), h, add_zero] at h2
    exact zeta_injective hζ (zeta_injective hζ (by rw [h2, map_zero, map_zero]))

theorem act_comm {f : V →ₗ[ZMod 2] V} (hf : ∀ v, ζ (f v) = f (ζ v)) (c : K) (v : V) :
    f (act ζ c v) = act ζ c (f v) := by
  simp only [act, map_add, map_smul, hf]

variable (q : QuadraticForm (ZMod 2) V)

theorem polar_map_map {f : V →ₗ[ZMod 2] V} (hf : ∀ v, q (f v) = q v) (x y : V) :
    polar q (f x) (f y) = polar q x y := by
  simp only [polar, ← map_add, hf]

theorem polar_self_zmod (x : V) : polar q x x = 0 := by
  rw [QuadraticMap.polar_self]
  rw [two_nsmul]
  exact zmod2_add_self _

variable {q}

theorem q_eq_polar_zeta (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hqζ : ∀ v, q (ζ v) = q v) (v : V) :
    q v = polar q v (ζ v) := by
  have h1 : q (v + ζ v) = q v + q (ζ v) + polar q v (ζ v) := QuadraticMap.map_add q v (ζ v)
  have h2 : v + ζ v = ζ (ζ v) := by rw [zeta_zeta hζ, add_comm]
  rw [h2] at h1
  simp only [hqζ] at h1
  rw [zmod2_add_self, zero_add] at h1
  exact h1

variable {a : V →ₗ[ZMod 2] V}

theorem polar_eq_zero_of_shift (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) {u w : V}
    (h1 : polar q u (ζ w) = polar q u (ζ (ζ w))) : polar q u w = 0 := by
  rw [zeta_zeta hζ, polar_add_right] at h1
  exact left_eq_add.mp h1

theorem polar_eq_zero_of_shift2 (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) {u w : V}
    (h0 : polar q u w = polar q u (ζ (ζ w))) (h1 : polar q u (ζ w) = polar q u w) :
    polar q u w = 0 := by
  rw [zeta_zeta hζ, polar_add_right] at h0
  rw [← h1]
  exact right_eq_add.mp h0

end CFSG.LargeExtraspecial.AS35QTh
