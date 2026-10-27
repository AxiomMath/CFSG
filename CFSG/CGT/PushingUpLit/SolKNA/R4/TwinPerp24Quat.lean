module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open QuaternionGroup

section Quat

variable {n : ℕ} [NeZero n]

theorem sq_eq_or_inv {x y : QuaternionGroup n} (h4 : (x * x) * (x * x) * ((x * x) * (x * x)) = 1)
    (h2 : (x * x) * (x * x) ≠ 1) (hxy : (y * y) * (y * y) = (x * x) * (x * x)) :
    y * y = x * x ∨ y * y = (x * x)⁻¹ := by
  have hnn : ((n : ℕ) : ZMod (2 * n)) + ((n : ℕ) : ZMod (2 * n)) = 0 := QSub.Alg.n_add_n
  have hsq : ∀ i : ZMod (2 * n), (xa i : QuaternionGroup n) * xa i = a (n : ZMod (2 * n)) := by
    intro i
    rw [xa_mul_xa]
    congr 1
    ring
  have hsq' : (a (n : ZMod (2 * n)) : QuaternionGroup n) * a (n : ZMod (2 * n)) = 1 := by
    rw [a_mul_a, hnn]
    rfl
  rcases x with i | i
  · rcases y with j | j
    ·
      simp only [a_mul_a] at h4 h2 hxy ⊢
      have h4' : (i + i + (i + i)) + (i + i + (i + i)) = 0 := by
        rw [one_def] at h4
        exact QuaternionGroup.a.inj h4
      have h2' : i + i + (i + i) ≠ 0 := fun h => h2 (by rw [one_def, h])
      have hx : i + i + (i + i) = ((n : ℕ) : ZMod (2 * n)) := by
        have h8 : 2 * (i + i + (i + i)) = 0 := by linear_combination h4'
        rcases QSub.Alg.two_mul_eq_zero_iff.mp h8 with h | h
        · exact absurd h h2'
        · exact h
      have hxy' : j + j + (j + j) = i + i + (i + i) := QuaternionGroup.a.inj hxy
      have hd : 2 * ((j + j) - (i + i)) = 0 := by linear_combination hxy'
      rcases QSub.Alg.two_mul_eq_zero_iff.mp hd with h | h
      · left
        congr 1
        linear_combination h
      · right
        rw [QSub.Alg.inv_a]
        congr 1
        linear_combination h + hx + hnn
    · exfalso
      rw [hsq j, hsq'] at hxy
      exact h2 hxy.symm
  · exfalso
    rw [hsq i, hsq'] at h2
    exact h2 rfl

end Quat

section Transport

variable {G : Type*} [Group G]

theorem sq_rel_of_mulEquiv {N : Subgroup G} [N.Normal] {n : ℕ} [NeZero n]
    (φ : G ⧸ N ≃* QuaternionGroup n) {x y p q : G} (hp : p = x * x) (hq : q = y * y)
    (h4 : (p * p) * (p * p) ∈ N) (h2 : p * p ∉ N) (hpq : (q * q)⁻¹ * (p * p) ∈ N) :
    q⁻¹ * p ∈ N ∨ q * p ∈ N := by
  subst hp hq
  have hX : ∀ g : G, φ (QuotientGroup.mk g) * φ (QuotientGroup.mk g) =
      φ (QuotientGroup.mk (g * g)) := fun g => by rw [← map_mul, ← QuotientGroup.mk_mul]
  have e4 : (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) *
      (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) *
      ((φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) *
        (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x))) = 1 := by
    rw [hX, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr h4, map_one]
  have e2 : (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) *
      (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) ≠ 1 := by
    intro h
    apply h2
    rw [hX, ← map_mul, ← QuotientGroup.mk_mul] at h
    exact (QuotientGroup.eq_one_iff _).mp (φ.injective (by rw [h, map_one]))
  have e3 : (φ (QuotientGroup.mk y) * φ (QuotientGroup.mk y)) *
      (φ (QuotientGroup.mk y) * φ (QuotientGroup.mk y)) =
      (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) *
      (φ (QuotientGroup.mk x) * φ (QuotientGroup.mk x)) := by
    rw [hX, hX, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg φ (QuotientGroup.eq.mpr hpq)
  rcases sq_eq_or_inv e4 e2 e3 with h | h
  · left
    rw [hX, hX] at h
    exact QuotientGroup.eq.mp (φ.injective h)
  · right
    rw [hX, hX, ← map_inv] at h
    have h' := φ.injective h
    have : QuotientGroup.mk (y * y * (x * x)) = (1 : G ⧸ N) := by
      rw [QuotientGroup.mk_mul, h', inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this

end Transport

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
