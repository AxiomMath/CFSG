module

public import Mathlib.Tactic.Group
public import Mathlib.Tactic.SetLike

public section

open scoped commutatorElement

namespace CFSG.QuasithinUnique.K1.ExceptionalCat

section Helpers

variable {G : Type*} [Group G]

theorem mul_eq_of_comm' {g h c : G} (hc : ⁅g, h⁆ = c) : g * h = c * h * g := by
  rw [← hc, commutatorElement_def]; group

theorem mul_eq_of_comm_inv {g h c : G} (hc : ⁅g, h⁆ = c) : h * g = c⁻¹ * g * h := by
  rw [← hc, commutatorElement_def]; group

theorem step_mul' {p q y c₁ c₂ : G} (hq : q * y = c₂ * y * q) (hp : p * y = c₁ * y * p)
    (hpc : Commute p c₂) : (p * q) * y = (c₂ * c₁) * y * (p * q) := by
  calc p * q * y = p * (q * y) := mul_assoc _ _ _
    _ = p * (c₂ * y * q) := by rw [hq]
    _ = (p * c₂) * y * q := by simp only [mul_assoc]
    _ = (c₂ * p) * y * q := by rw [hpc.eq]
    _ = c₂ * (p * y) * q := by simp only [mul_assoc]
    _ = c₂ * (c₁ * y * p) * q := by rw [hp]
    _ = (c₂ * c₁) * y * (p * q) := by simp only [mul_assoc]

theorem step_right {g w y c : G} (hg : g * y = c * y * g) (hw : Commute w y) :
    (g * w) * y = c * y * (g * w) := by
  calc g * w * y = g * (w * y) := mul_assoc _ _ _
    _ = g * (y * w) := by rw [hw.eq]
    _ = (g * y) * w := by simp only [mul_assoc]
    _ = c * y * g * w := by rw [hg]
    _ = c * y * (g * w) := by simp only [mul_assoc]

theorem eq_one_of_central {z y c : G} (h : z * y = c * y * z) (hc : z * y = y * z) : c = 1 := by
  have : c * (y * z) = y * z := by rw [← mul_assoc, ← h, hc]
  simpa using this

theorem comm_self_of_add {M : Type*} [AddCommGroup M] (x : M → G)
    (add : ∀ c d, x (c + d) = x c * x d) (c d : M) : Commute (x c) (x d) := by
  show x c * x d = x d * x c
  rw [← add, ← add, add_comm]

theorem zero_of_add {M : Type*} [AddCommGroup M] (x : M → G)
    (add : ∀ c d, x (c + d) = x c * x d) : x 0 = 1 := by
  have h := add 0 0
  rw [add_zero] at h
  simpa using h

end Helpers

section Center

variable {G : Type*} [Group G] {K k : Type*} [AddCommGroup K] [AddCommGroup k]

theorem triality_center_aux
    (x₁ x₃ x₄ : K → G) (x₂ x₅ x₆ : k → G) (tr : K → K → k) (m : k → k → k) (one : k)
    (a₁ : ∀ c d, x₁ (c + d) = x₁ c * x₁ d) (a₂ : ∀ c d, x₂ (c + d) = x₂ c * x₂ d)
    (a₃ : ∀ c d, x₃ (c + d) = x₃ c * x₃ d) (a₄ : ∀ c d, x₄ (c + d) = x₄ c * x₄ d)
    (a₅ : ∀ c d, x₅ (c + d) = x₅ c * x₅ d) (a₆ : ∀ c d, x₆ (c + d) = x₆ c * x₆ d)
    (inj : ∀ (a a' : K) (b b' : k) (c c' d d' : K) (e e' f f' : k),
      x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f = x₁ a' * x₂ b' * x₃ c' * x₄ d' * x₅ e' * x₆ f' →
        a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f')
    (c15 : ∀ a b, Commute (x₁ a) (x₅ b)) (c16 : ∀ a b, Commute (x₁ a) (x₆ b))
    (c26 : ∀ a b, Commute (x₂ a) (x₆ b)) (c35 : ∀ a b, Commute (x₃ a) (x₅ b))
    (c45 : ∀ a b, Commute (x₄ a) (x₅ b))
    (c46 : ∀ a b, Commute (x₄ a) (x₆ b)) (c56 : ∀ a b, Commute (x₅ a) (x₆ b))
    (k14 : ∀ s t, ⁅x₁ s, x₄ t⁆ = x₅ (tr s t)) (k34 : ∀ s t, ⁅x₃ s, x₄ t⁆ = x₆ (tr s t))
    (k25 : ∀ b e, ⁅x₂ b, x₅ e⁆ = x₆ (m b e))
    (hnd : ∀ s : K, (∀ t, tr s t = 0) → s = 0) (hnd' : ∀ t : K, (∀ s, tr s t = 0) → t = 0)
    (hone : ∀ e, m one e = e) (hone' : ∀ b, m b one = b)
    (a : K) (b : k) (c d : K) (e f : k)
    (h5 : x₅ one * (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) =
      (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) * x₅ one)
    (h4 : ∀ t, x₄ t * (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) =
      (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) * x₄ t)
    (h1 : ∀ t, x₁ t * (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) =
      (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) * x₁ t)
    (h2 : x₂ one * (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) =
      (x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f) * x₂ one) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have z1 := zero_of_add x₁ a₁
  have z2 := zero_of_add x₂ a₂
  have z3 := zero_of_add x₃ a₃
  have z4 := zero_of_add x₄ a₄
  have z5 := zero_of_add x₅ a₅
  have z6 := zero_of_add x₆ a₆
  have inj6 : ∀ u, x₆ u = 1 → u = 0 := fun u hu => by
    have h := inj 0 0 0 0 0 0 0 0 0 0 u 0 (by simp [z1, z2, z3, z4, z5, z6, hu])
    exact h.2.2.2.2.2
  have inj5 : ∀ v, x₅ v = 1 → v = 0 := fun v hv => by
    have h := inj 0 0 0 0 0 0 0 0 v 0 0 0 (by simp [z1, z2, z3, z4, z5, z6, hv])
    exact h.2.2.2.2.1
  have inj56 : ∀ u v, x₆ u * x₅ v = 1 → u = 0 ∧ v = 0 := fun u v huv => by
    have h := inj 0 0 0 0 0 0 0 0 v 0 u 0 (by
      simp only [z1, z2, z3, z4, z5, z6, one_mul, mul_one]
      rw [(c56 v u).eq, huv])
    exact ⟨h.2.2.2.2.2, h.2.2.2.2.1⟩
  have hz : x₁ a * x₂ b * x₃ c * x₄ d * x₅ e * x₆ f =
      x₁ a * (x₂ b * (x₃ c * (x₄ d * (x₅ e * x₆ f)))) := by simp only [mul_assoc]
  have hb : b = 0 := by
    have hw : Commute (x₃ c * (x₄ d * (x₅ e * x₆ f))) (x₅ one) :=
      Commute.mul_left (c35 c one) (Commute.mul_left (c45 d one)
        (Commute.mul_left (comm_self_of_add x₅ a₅ e one) (c56 one f).symm))
    have hq : (x₂ b * (x₃ c * (x₄ d * (x₅ e * x₆ f)))) * x₅ one =
        x₆ (m b one) * x₅ one * (x₂ b * (x₃ c * (x₄ d * (x₅ e * x₆ f)))) :=
      step_right (mul_eq_of_comm' (k25 b one)) hw
    have hp : x₁ a * x₅ one = 1 * x₅ one * x₁ a := by rw [one_mul]; exact (c15 a one).eq
    have hstep := step_mul' hq hp (c16 a (m b one))
    rw [← hz] at hstep
    have hc := eq_one_of_central hstep h5.symm
    rw [mul_one] at hc
    rw [hone'] at hc
    exact inj6 b hc
  subst hb
  have hac : ∀ t : K, tr c t = 0 ∧ tr a t = 0 := fun t => by
    have hz' : x₁ a * x₂ 0 * x₃ c * x₄ d * x₅ e * x₆ f =
        x₁ a * (x₃ c * (x₄ d * (x₅ e * x₆ f))) := by simp [z2, mul_assoc]
    have hw : Commute (x₄ d * (x₅ e * x₆ f)) (x₄ t) :=
      Commute.mul_left (comm_self_of_add x₄ a₄ d t)
        (Commute.mul_left (c45 t e).symm (c46 t f).symm)
    have hq : (x₃ c * (x₄ d * (x₅ e * x₆ f))) * x₄ t =
        x₆ (tr c t) * x₄ t * (x₃ c * (x₄ d * (x₅ e * x₆ f))) :=
      step_right (mul_eq_of_comm' (k34 c t)) hw
    have hp : x₁ a * x₄ t = x₅ (tr a t) * x₄ t * x₁ a := mul_eq_of_comm' (k14 a t)
    have hstep := step_mul' hq hp (c16 a (tr c t))
    rw [← hz'] at hstep
    have hc := eq_one_of_central hstep (h4 t).symm
    exact inj56 _ _ hc
  have ha : a = 0 := hnd a fun t => (hac t).2
  have hc : c = 0 := hnd c fun t => (hac t).1
  subst ha
  subst hc
  have hd : d = 0 := by
    refine hnd' d fun t => ?_
    have hz' : x₁ 0 * x₂ 0 * x₃ 0 * x₄ d * x₅ e * x₆ f = x₄ d * (x₅ e * x₆ f) := by
      simp [z1, z2, z3, mul_assoc]
    have hw : Commute (x₅ e * x₆ f) (x₁ t) :=
      Commute.mul_left (c15 t e).symm (c16 t f).symm
    have hg : x₄ d * x₁ t = (x₅ (tr t d))⁻¹ * x₁ t * x₄ d :=
      mul_eq_of_comm_inv (k14 t d)
    have hstep := step_right hg hw
    rw [← hz'] at hstep
    have hc := eq_one_of_central hstep (h1 t).symm
    rw [inv_eq_one] at hc
    exact inj5 _ hc
  subst hd
  have he : e = 0 := by
    have hz' : x₁ 0 * x₂ 0 * x₃ 0 * x₄ 0 * x₅ e * x₆ f = x₅ e * x₆ f := by
      simp [z1, z2, z3, z4]
    have hw : Commute (x₆ f) (x₂ one) := (c26 one f).symm
    have hg : x₅ e * x₂ one = (x₆ (m one e))⁻¹ * x₂ one * x₅ e :=
      mul_eq_of_comm_inv (k25 one e)
    have hstep := step_right hg hw
    rw [← hz'] at hstep
    have hc := eq_one_of_central hstep h2.symm
    rw [inv_eq_one, hone] at hc
    exact inj6 e hc
  exact ⟨rfl, rfl, rfl, rfl, he⟩

end Center

end CFSG.QuasithinUnique.K1.ExceptionalCat
