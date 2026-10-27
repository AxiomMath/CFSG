module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L412A
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L412N

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem two_ne_zero_of_card_three [Finite K] (hK : Nat.card K = 3) : (2 : K) ≠ 0 :=
  CFSG.ClassicalInvolution.Models.OrthogonalPairs.IsFundamental.two_ne_zero_of_odd
    (by rw [hK]; decide)

theorem quadOdd_smul_vec_add_smul_vec (r : Fin n) (a b : K) :
    quadOdd n K (a • (oddFrame n K).vec r true + b • (oddFrame n K).vec r false) = a * b := by
  have hp : polar (quadOdd n K) ((oddFrame n K).vec r true) ((oddFrame n K).vec r false) = 1 :=
    (oddFrame n K).polar_vec_not r true
  rw [QuadraticMap.map_add (quadOdd n K), QuadraticMap.map_smul, QuadraticMap.map_smul,
    (oddFrame n K).map_vec, (oddFrame n K).map_vec, polar_smul_left, polar_smul_right, hp]
  simp

theorem polar_smul_vec_add_smul_vec (r : Fin n) (a b c d : K) :
    polar (quadOdd n K) (a • (oddFrame n K).vec r true + b • (oddFrame n K).vec r false)
      (c • (oddFrame n K).vec r true + d • (oddFrame n K).vec r false) = a * d + b * c := by
  have hp : polar (quadOdd n K) ((oddFrame n K).vec r true) ((oddFrame n K).vec r false) = 1 :=
    (oddFrame n K).polar_vec_not r true
  have hp' : polar (quadOdd n K) ((oddFrame n K).vec r false) ((oddFrame n K).vec r true) = 1 :=
    (oddFrame n K).polar_vec_not r false
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hp, hp',
    HypFrame.polar_vec_self, smul_eq_mul]
  ring

theorem spinAction_longTorus_vec_right {i r : Fin n} (hir : i ≠ r) (s : Bool) :
    spinAction (quadOdd n K) ((oddFrame n K).longTorus hir true true (-1))
      ((oddFrame n K).vec r s) = -(oddFrame n K).vec r s := by
  rw [HypFrame.spinAction_longTorus_vec]
  cases s <;> simp [longCoroot, Ne.symm hir]

theorem spinAction_longTorus_vec_of_ne {i r k : Fin n} (hir : i ≠ r) (hki : k ≠ i) (hkr : k ≠ r)
    (s : Bool) :
    spinAction (quadOdd n K) ((oddFrame n K).longTorus hir true true (-1))
      ((oddFrame n K).vec k s) = (oddFrame n K).vec k s := by
  rw [HypFrame.spinAction_longTorus_vec]
  simp [longCoroot, hki, hkr]

theorem spinAction_longTorus_z {i r : Fin n} (hir : i ≠ r) (τ : Kˣ) :
    spinAction (quadOdd n K) ((oddFrame n K).longTorus hir true true τ) (oddFrame n K).z =
      (oddFrame n K).z := by
  rw [HypFrame.spinAction_longTorus]
  simp only [OddFrame.polar_z_vec, zero_smul, add_zero, smul_zero]

variable [Finite K]

theorem sq_vec_of_commute_neg_plane (hK : Nat.card K = 3) {i r : Fin n} (hir : i ≠ r)
    (A T : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K))
    (hApol : ∀ v w, polar (quadOdd n K) (A v) (A w) = polar (quadOdd n K) v w)
    (hAQ : ∀ v, quadOdd n K (A v) = quadOdd n K v)
    (hTpol : ∀ v w, polar (quadOdd n K) (T v) (T w) = polar (quadOdd n K) v w)
    (hcomm : ∀ v, A (T v) = T (A v))
    (hTr : ∀ s, T ((oddFrame n K).vec r s) = -(oddFrame n K).vec r s)
    (hTk : ∀ k s, k ≠ i → k ≠ r → T ((oddFrame n K).vec k s) = (oddFrame n K).vec k s)
    (hTz : T (oddFrame n K).z = (oddFrame n K).z) {c : K} (hc : c ≠ 0)
    (hi : ∀ s, A ((oddFrame n K).vec i s) = c • (oddFrame n K).vec i s) (u : Bool) :
    A (A ((oddFrame n K).vec r u)) = (oddFrame n K).vec r u := by
  have h2 := two_ne_zero_of_card_three hK
  have hvv : ∀ k l s t, polar (quadOdd n K) ((oddFrame n K).vec k s) ((oddFrame n K).vec l t) =
      if k = l ∧ s = !t then 1 else 0 := fun k l s t => (oddFrame n K).polar_vec_vec k l s t
  have hvz : ∀ k s, polar (quadOdd n K) ((oddFrame n K).vec k s) (oddFrame n K).z = 0 :=
    fun k s => (oddFrame n K).polar_vec_z k s
  have hspan : ∀ u', A ((oddFrame n K).vec r u') =
      polar (quadOdd n K) (A ((oddFrame n K).vec r u')) ((oddFrame n K).vec r false) •
          (oddFrame n K).vec r true +
        polar (quadOdd n K) (A ((oddFrame n K).vec r u')) ((oddFrame n K).vec r true) •
          (oddFrame n K).vec r false := by
    intro u'
    have hTw : T (A ((oddFrame n K).vec r u')) = -A ((oddFrame n K).vec r u') := by
      rw [← hcomm, hTr, map_neg]
    have hvan : ∀ v, T v = v → polar (quadOdd n K) (A ((oddFrame n K).vec r u')) v = 0 := by
      intro v hv
      have h := hTpol (A ((oddFrame n K).vec r u')) v
      rw [hTw, hv, polar_neg_left] at h
      have h' : (2 : K) * polar (quadOdd n K) (A ((oddFrame n K).vec r u')) v = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left h2
    have hvi : ∀ s,
        polar (quadOdd n K) (A ((oddFrame n K).vec r u')) ((oddFrame n K).vec i s) = 0 := by
      intro s
      have h := hApol ((oddFrame n K).vec r u') ((oddFrame n K).vec i s)
      have hri : ¬ (r = i ∧ u' = !s) := fun h' => hir h'.1.symm
      rw [hi s, polar_smul_right, hvv, ite_eq_right hri, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_left hc
    apply eq_of_polar_quadOdd h2
    · intro k s
      rw [polar_add_left, polar_smul_left, polar_smul_left, hvv, hvv, smul_eq_mul, smul_eq_mul]
      by_cases hkr : k = r
      · subst hkr
        cases s <;> simp
      · have hc1 : ¬ (r = k ∧ true = !s) := fun h' => hkr h'.1.symm
        have hc2 : ¬ (r = k ∧ false = !s) := fun h' => hkr h'.1.symm
        rw [ite_eq_right hc1, ite_eq_right hc2, mul_zero, mul_zero, add_zero]
        by_cases hki : k = i
        · subst hki
          exact hvi s
        · exact hvan _ (hTk k s hki hkr)
    · rw [polar_add_left, polar_smul_left, polar_smul_left, hvz, hvz, smul_zero, smul_zero,
        add_zero]
      exact hvan _ hTz
  have hwt := hspan true
  have hwf := hspan false
  set a := polar (quadOdd n K) (A ((oddFrame n K).vec r true)) ((oddFrame n K).vec r false)
    with ha
  set b := polar (quadOdd n K) (A ((oddFrame n K).vec r true)) ((oddFrame n K).vec r true)
    with hb
  set c' := polar (quadOdd n K) (A ((oddFrame n K).vec r false)) ((oddFrame n K).vec r false)
    with hc'
  set d := polar (quadOdd n K) (A ((oddFrame n K).vec r false)) ((oddFrame n K).vec r true)
    with hd
  have hab : a * b = 0 := by
    have h := hAQ ((oddFrame n K).vec r true)
    rw [hwt, quadOdd_smul_vec_add_smul_vec, (oddFrame n K).map_vec] at h
    exact h
  have hcd : c' * d = 0 := by
    have h := hAQ ((oddFrame n K).vec r false)
    rw [hwf, quadOdd_smul_vec_add_smul_vec, (oddFrame n K).map_vec] at h
    exact h
  have had : a * d + b * c' = 1 := by
    have h := hApol ((oddFrame n K).vec r true) ((oddFrame n K).vec r false)
    rw [hwt, hwf, polar_smul_vec_add_smul_vec] at h
    exact h.trans ((oddFrame n K).polar_vec_not r true)
  obtain ⟨e1, e2, e3, e4⟩ := hyperbolic_sq_three hK hab hcd had
  cases u
  · rw [hwf, map_add, map_smul, map_smul, hwt, hwf]
    have : c' • (a • (oddFrame n K).vec r true + b • (oddFrame n K).vec r false) +
        d • (c' • (oddFrame n K).vec r true + d • (oddFrame n K).vec r false) =
        (c' * a + d * c') • (oddFrame n K).vec r true +
          (c' * b + d * d) • (oddFrame n K).vec r false := by module
    rw [this, e3, e4, zero_smul, one_smul, zero_add]
  · rw [hwt, map_add, map_smul, map_smul, hwt, hwf]
    have : a • (a • (oddFrame n K).vec r true + b • (oddFrame n K).vec r false) +
        b • (c' • (oddFrame n K).vec r true + d • (oddFrame n K).vec r false) =
        (a * a + b * c') • (oddFrame n K).vec r true +
          (a * b + b * d) • (oddFrame n K).vec r false := by module
    rw [this, e1, e2, zero_smul, one_smul, add_zero]

omit [Finite K] in
theorem sq_z_of_fix (h2 : (2 : K) ≠ 0)
    (B : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K))
    (hBpol : ∀ v w, polar (quadOdd n K) (B v) (B w) = polar (quadOdd n K) v w)
    (hBQ : ∀ v, quadOdd n K (B v) = quadOdd n K v)
    (hB : ∀ k s, B ((oddFrame n K).vec k s) = (oddFrame n K).vec k s) :
    B (B (oddFrame n K).z) = (oddFrame n K).z := by
  have hw0 : ∀ k s,
      polar (quadOdd n K) (B (oddFrame n K).z) ((oddFrame n K).vec k s) = 0 := by
    intro k s
    have h := hBpol (oddFrame n K).z ((oddFrame n K).vec k s)
    rwa [hB, OddFrame.polar_z_vec] at h
  have hzz : polar (quadOdd n K) (oddFrame n K).z (oddFrame n K).z = 2 :=
    (oddFrame n K).polar_z_self
  have hwμ : B (oddFrame n K).z =
      (polar (quadOdd n K) (B (oddFrame n K).z) (oddFrame n K).z * 2⁻¹) • (oddFrame n K).z := by
    apply eq_of_polar_quadOdd h2
    · intro k s
      rw [hw0, polar_smul_left, OddFrame.polar_z_vec, smul_zero]
    · rw [polar_smul_left, hzz, smul_eq_mul, inv_mul_cancel_right₀ h2]
  set μ := polar (quadOdd n K) (B (oddFrame n K).z) (oddFrame n K).z * 2⁻¹ with hμ
  have hμ2 : μ * μ = 1 := by
    have h := hBQ (oddFrame n K).z
    rw [hwμ, QuadraticMap.map_smul, (oddFrame n K).map_z, smul_eq_mul, mul_one] at h
    exact h
  rw [hwμ, map_smul, hwμ, smul_smul, hμ2, one_smul]

omit [Finite K] in
theorem spinAction_eq_one_of_fix {y : spinGroup (quadOdd n K)}
    (hvec : ∀ k s, spinAction (quadOdd n K) y ((oddFrame n K).vec k s) = (oddFrame n K).vec k s)
    (hz : spinAction (quadOdd n K) y (oddFrame n K).z = (oddFrame n K).z) :
    spinAction (quadOdd n K) y = 1 := by
  have h : (spinAction (quadOdd n K) y).toLinearMap = LinearMap.id := by
    apply LinearMap.pi_ext'
    intro idx
    apply LinearMap.ext_ring
    rcases idx with k | k | u
    · simpa using hvec k true
    · simpa using hvec k false
    · cases u
      simpa [oddZ] using hz
  refine LinearEquiv.ext fun v => ?_
  show spinAction (quadOdd n K) y v = v
  exact congrArg (fun f => f v) h

theorem eq_one_of_commute_three (hK : Nat.card K = 3) {i j : Fin n} (hij : i ≠ j)
    {x : spinGroup (quadOdd n K)} (hx : Nat.Coprime 2 (orderOf x))
    (h1 : x * (oddFrame n K).longRoot hij true true (.ofAdd 1) =
      (oddFrame n K).longRoot hij true true (.ofAdd 1) * x)
    (h2' : x * (oddFrame n K).longRoot hij true false (.ofAdd 1) =
      (oddFrame n K).longRoot hij true false (.ofAdd 1) * x)
    (h3 : x * (oddFrame n K).longRoot hij.symm false false (.ofAdd 1) =
      (oddFrame n K).longRoot hij.symm false false (.ofAdd 1) * x)
    (h4 : x * (oddFrame n K).longRoot hij.symm true false (.ofAdd 1) =
      (oddFrame n K).longRoot hij.symm true false (.ofAdd 1) * x)
    (hrest : ∀ (r : Fin n) (hir : i ≠ r), r ≠ j →
      x * (oddFrame n K).longTorus hir true true (-1) =
          (oddFrame n K).longTorus hir true true (-1) * x ∨
        ∀ b : Bool, x * (oddFrame n K).shortRoot r b (.ofAdd 1) =
          (oddFrame n K).shortRoot r b (.ofAdd 1) * x) :
    x = 1 := by
  have h2 := two_ne_zero_of_card_three hK
  have hApol := polar_spinAction (quadOdd n K) x
  have hAQ := map_spinAction (quadOdd n K) x
  obtain ⟨c, hc⟩ := exists_spinAction_vec_eq_smul (oddFrame n K).toHypFrame hij h1 h2'
  obtain ⟨hcj, hci, hcj'⟩ :=
    spinAction_vec_eq_smul_of_commute (oddFrame n K).toHypFrame hij hc h3 h4
  have hne : ∀ k s, (oddFrame n K).vec k s ≠ 0 := fun k s h => by
    have h' := (oddFrame n K).polar_vec_not k s
    rw [h, polar_zero_left] at h'
    exact zero_ne_one h'
  have hsq : ∀ (v : Fin n ⊕ Fin n ⊕ Unit → K) (μ : K), v ≠ 0 →
      spinAction (quadOdd n K) x v = μ • v →
        spinAction (quadOdd n K) x (spinAction (quadOdd n K) x v) = v := by
    intro v μ hv hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact hv ((LinearEquiv.map_eq_zero_iff _).mp hμ)
    rw [hμ, map_smul, hμ, smul_smul, mul_self_eq_one_of_card_three hK hμ0, one_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hne i true ((LinearEquiv.map_eq_zero_iff _).mp hc)
  have hvec : ∀ k s, spinAction (quadOdd n K) (x * x) ((oddFrame n K).vec k s) =
      (oddFrame n K).vec k s := by
    intro k s
    rw [map_mul, LinearEquiv.mul_apply]
    by_cases hki : k = i
    · subst hki
      cases s
      · exact hsq _ c (hne _ _) hci
      · exact hsq _ c (hne _ _) hc
    · by_cases hkj : k = j
      · subst hkj
        cases s
        · exact hsq _ c (hne _ _) hcj'
        · exact hsq _ c (hne _ _) hcj
      · rcases hrest k (Ne.symm hki) hkj with h | h
        · exact sq_vec_of_commute_neg_plane hK (Ne.symm hki) _ _ hApol hAQ
            (polar_spinAction _ _) (spinAction_comm_apply h)
            (spinAction_longTorus_vec_right (Ne.symm hki))
            (fun k' s' hk'i hk'k => spinAction_longTorus_vec_of_ne (Ne.symm hki) hk'i hk'k s')
            (spinAction_longTorus_z (Ne.symm hki) (-1)) hc0
            (fun s' => by cases s'; exact hci; exact hc) s
        · obtain ⟨μ, hμ⟩ :=
            exists_spinAction_vec_eq_smul_of_commute_shortRoot (oddFrame n K) h2 k s (h s)
          exact hsq _ μ (hne _ _) hμ
  have hz := sq_z_of_fix h2 (spinAction (quadOdd n K) (x * x)) (polar_spinAction _ _)
    (map_spinAction _ _) hvec
  have hone : spinAction (quadOdd n K) (x * x * (x * x)) = 1 := by
    apply spinAction_eq_one_of_fix
    · intro k s
      rw [map_mul, LinearEquiv.mul_apply, hvec, hvec]
    · rw [map_mul, LinearEquiv.mul_apply]
      exact hz
  have h8 : x ^ 8 = 1 := by
    have h := mul_self_eq_one_of_mem_ker_spinAction_quadOdd h2 (MonoidHom.mem_ker.mpr hone)
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    exact h
  have hdvd : orderOf x ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left 3 hx).symm hdvd)

end CFSG.ComponentClassification.HarrisLit.T1
