module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5cn_pow4_of_sq (u : SL23) (hu : u * u = 1 ∨ u * u = -1) : u ^ 4 = 1 :=
  (by decide : ∀ u : SL23, (u * u = 1 ∨ u * u = -1) → u ^ 4 = 1) u hu

theorem sec5cn_pow4_ne_neg (u : SL23) : u ^ 4 ≠ -1 :=
  (by decide : ∀ u : SL23, u ^ 4 ≠ -1) u

theorem sec5cn_pow12 (u : SL23) : u ^ 12 = 1 :=
  (by decide : ∀ u : SL23, u ^ 12 = 1) u

theorem sec5cn_exists_anti (x : SL23) (hx : x * x = -1) :
    ∃ c : SL23, c ^ 4 = 1 ∧ c⁻¹ * x * c = -x :=
  (by decide : ∀ x : SL23, x * x = -1 → ∃ c : SL23, c ^ 4 = 1 ∧ c⁻¹ * x * c = -x) x hx

theorem sec5cn_conj_q8 (a c : SL23) (ha : a ^ 4 = 1) (hc : c ^ 4 = 1) :
    c⁻¹ * a * c = a ∨ c⁻¹ * a * c = -a :=
  (by decide : ∀ a c : SL23, a ^ 4 = 1 → c ^ 4 = 1 → c⁻¹ * a * c = a ∨ c⁻¹ * a * c = -a) a c ha hc

theorem sec5cn_commutator_onto (κ : SL23) (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1) (q : SL23)
    (hq : q ^ 4 = 1) :
    ∃ q₁ : SL23, q₁ ^ 4 = 1 ∧ (q₁⁻¹ * κ⁻¹ * q₁ * κ = q ∨ q₁⁻¹ * κ⁻¹ * q₁ * κ = -q) :=
  (by decide : ∀ κ : SL23, κ ^ 3 = 1 → κ ≠ 1 → ∀ q : SL23, q ^ 4 = 1 →
    ∃ q₁ : SL23, q₁ ^ 4 = 1 ∧ (q₁⁻¹ * κ⁻¹ * q₁ * κ = q ∨ q₁⁻¹ * κ⁻¹ * q₁ * κ = -q))
    κ hκ3 hκ1 q hq

theorem sec5cn_centralizer_q8 (k : SL23) (hk : ∀ p : SL23, p ^ 4 = 1 → k * p = p * k) :
    k = 1 ∨ k = -1 :=
  (by decide : ∀ k : SL23, (∀ p : SL23, p ^ 4 = 1 → k * p = p * k) → k = 1 ∨ k = -1) k hk

theorem sec5cn_pair_expand (x₁ x₂ p : SL23) (h₁ : x₁ * x₁ = -1) (h₂ : x₂ * x₂ = -1)
    (h₁₂ : x₁ * x₂ = -(x₂ * x₁)) (hp : p ^ 4 = 1) :
    ∃ i j k : Fin 2, p = (-1) ^ (k : ℕ) * x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) ∧
      ((j = 0 ∧ p * x₁ = x₁ * p) ∨ (j = 1 ∧ p * x₁ = -(x₁ * p))) ∧
      ((i = 0 ∧ p * x₂ = x₂ * p) ∨ (i = 1 ∧ p * x₂ = -(x₂ * p))) := by
  letI : DecidableEq SL23 := inferInstance
  exact (by decide : ∀ x₁ x₂ p : SL23, x₁ * x₁ = -1 → x₂ * x₂ = -1 → x₁ * x₂ = -(x₂ * x₁) →
    p ^ 4 = 1 → ∃ i j k : Fin 2, p = (-1) ^ (k : ℕ) * x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) ∧
      ((j = 0 ∧ p * x₁ = x₁ * p) ∨ (j = 1 ∧ p * x₁ = -(x₁ * p))) ∧
      ((i = 0 ∧ p * x₂ = x₂ * p) ∨ (i = 1 ∧ p * x₂ = -(x₂ * p)))) x₁ x₂ p h₁ h₂ h₁₂ hp

theorem sec5cn_neg_eq (u : SL23) : -u = (-1) * u :=
  (by decide : ∀ u : SL23, -u = (-1) * u) u

theorem sec5cn_mul_neg_one (u : SL23) : u * (-1) = -u :=
  (by decide : ∀ u : SL23, u * (-1) = -u) u

theorem sec5cn_neg_neg (u : SL23) : -(-u) = u :=
  (by decide : ∀ u : SL23, -(-u) = u) u

theorem sec5cn_neg_ne (u : SL23) : -u ≠ u :=
  (by decide : ∀ u : SL23, -u ≠ u) u

theorem sec5cn_q8_div (u v : SL23) (hu : u ^ 4 = 1) (hv : v ^ 4 = 1) : (u⁻¹ * v) ^ 4 = 1 :=
  (by decide : ∀ u v : SL23, u ^ 4 = 1 → v ^ 4 = 1 → (u⁻¹ * v) ^ 4 = 1) u v hu hv

theorem sec5cn_comm_q8 (p a : SL23) (hp : p ^ 4 = 1) (ha : a ^ 4 = 1) :
    p * a = a * p ∨ p * a = -(a * p) :=
  (by decide : ∀ p a : SL23, p ^ 4 = 1 → a ^ 4 = 1 → p * a = a * p ∨ p * a = -(a * p)) p a hp ha

theorem sec5cn_q8_mul (u v : SL23) (hu : u ^ 4 = 1) (hv : v ^ 4 = 1) : (u * v) ^ 4 = 1 :=
  (by decide : ∀ u v : SL23, u ^ 4 = 1 → v ^ 4 = 1 → (u * v) ^ 4 = 1) u v hu hv

theorem sec5cn_comm_iff_pm (x y : SL23) (hx : x * x = -1) (hy : y * y = -1) :
    x * y = y * x ↔ (y = x ∨ y = -x) :=
  (by decide : ∀ x y : SL23, x * x = -1 → y * y = -1 → (x * y = y * x ↔ (y = x ∨ y = -x))) x y hx hy

theorem sec5cn_neg_absurd {w w' : SL23} (h₁ : w = w') (h₂ : w = -w') : False :=
  sec5cn_neg_ne w' (h₂.symm.trans h₁)

theorem sec5cn_sign_match {x y x' y' : SL23} {j j' : Fin 2}
    (hc : (y * x = x * y ∧ y' * x' = x' * y') ∨ (y * x = -(x * y) ∧ y' * x' = -(x' * y')))
    (hj : (j = 0 ∧ x * y = y * x) ∨ (j = 1 ∧ x * y = -(y * x)))
    (hj' : (j' = 0 ∧ x' * y' = y' * x') ∨ (j' = 1 ∧ x' * y' = -(y' * x'))) : j = j' := by
  rcases hc with ⟨c₁, c₂⟩ | ⟨c₁, c₂⟩
  · rcases hj with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rcases hj' with ⟨e₁', e₂'⟩ | ⟨e₁', e₂'⟩
      · exact e₁.trans e₁'.symm
      · rw [c₂] at e₂'
        exact (sec5cn_neg_absurd (w := x' * y') (w' := x' * y') rfl e₂').elim
    · rw [c₁] at e₂
      exact (sec5cn_neg_absurd (w := x * y) (w' := x * y) rfl e₂).elim
  · rcases hj with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rw [c₁] at e₂
      exact (sec5cn_neg_absurd (w := x * y) (w' := -(x * y)) e₂ (by rw [sec5cn_neg_neg])).elim
    · rcases hj' with ⟨e₁', e₂'⟩ | ⟨e₁', e₂'⟩
      · rw [c₂] at e₂'
        exact (sec5cn_neg_absurd (w := x' * y') (w' := -(x' * y')) e₂'
          (by rw [sec5cn_neg_neg])).elim
      · exact e₁.trans e₁'.symm

theorem sec5cn_pm_of_conj (t u a : SL23) (ht : t ^ 4 = 1) (hu : u ^ 4 = 1)
    (ha : a = u⁻¹ * t * u ∨ a = u⁻¹ * t * u * (-1)) : a = t ∨ a = -t :=
  (by decide : ∀ t u a : SL23, t ^ 4 = 1 → u ^ 4 = 1 →
    (a = u⁻¹ * t * u ∨ a = u⁻¹ * t * u * (-1)) → a = t ∨ a = -t) t u a ht hu ha

end CFSG.OddStandard.SmallF3.Omega
