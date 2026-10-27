module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.ComponentClassification.WalterSchur

open scoped commutatorElement IsMulCommutative

section Relations

variable {W : Type*} [CommGroup W]

theorem eq_one_of_seven_relations_aux (e : ℕ → W) {j : ℕ} (hj2 : 2 ≤ j) (hj6 : j ≤ 6)
    (h0 : e 0 = 1) (hsq : ∀ k, e k * e k = 1) (h7 : ∀ k, e (k + 7) = e k) (h61 : e 6 = e 1)
    (h52 : e 5 = e 2) (h43 : e 4 = e 3) (hrec : ∀ n, e (n + j) = e n * e (n + 1)) :
    e 1 = 1 ∧ e 2 = 1 ∧ e 3 = 1 := by
  have r0 := hrec 0
  have r1 := hrec 1
  have r2 := hrec 2
  have r3 := hrec 3
  have e7 : e 7 = 1 := by simpa [h0] using h7 0
  have e8 : e 8 = e 1 := h7 1
  have e9 : e 9 = e 2 := h7 2
  have s1 := hsq 1
  have s3 := hsq 3
  rw [h0, one_mul] at r0
  interval_cases j
  ·
    have e2 : e 2 = e 1 := r0
    have e3 : e 3 = 1 := by rw [r1, e2, s1]
    have e1 : e 1 = 1 := by
      have h := r2
      rw [h43, e3, e2, mul_one] at h
      exact h.symm
    exact ⟨e1, e2.trans e1, e3⟩
  ·
    have e3 : e 3 = e 1 := r0
    have e2 : e 2 = 1 := by
      have h := r1
      rw [h43, e3] at h
      exact mul_eq_left.mp h.symm
    have e1 : e 1 = 1 := by
      have h := r2
      rw [h52, e2, e3, one_mul] at h
      exact h.symm
    exact ⟨e1, e2, e3.trans e1⟩
  ·
    have e3 : e 3 = e 1 := by rw [← h43]; exact r0
    have e1 : e 1 = 1 := by
      have h := r1
      rw [h52] at h
      exact mul_eq_right.mp h.symm
    have e2 : e 2 = 1 := by
      have h := r2
      rw [h61, e3, e1, mul_one] at h
      exact h.symm
    exact ⟨e1, e2, e3.trans e1⟩
  ·
    have e2 : e 2 = e 1 := by rw [← h52]; exact r0
    have e1 : e 1 = 1 := by
      have h := r1
      rw [h61, e2, s1] at h
      exact h
    have e3 : e 3 = 1 := by
      have h := r2
      rw [e7, e2, e1, one_mul] at h
      exact h.symm
    exact ⟨e1, e2.trans e1, e3⟩
  ·
    have e2 : e 2 = 1 := by
      have h := r3
      rw [e9, h43, s3] at h
      exact h
    have e1 : e 1 = 1 := by
      have h := r1
      rw [e7, e2, mul_one] at h
      exact h.symm
    have e3 : e 3 = 1 := by
      have h := r2
      rw [e8, e1, e2, one_mul] at h
      exact h.symm
    exact ⟨e1, e2, e3⟩

theorem eq_one_of_seven_relations (e : ℕ → W) {j : ℕ} (hj : 2 ≤ j % 7)
    (h0 : e 0 = 1) (hsq : ∀ k, e k * e k = 1) (h7 : ∀ k, e (k + 7) = e k) (h61 : e 6 = e 1)
    (h52 : e 5 = e 2) (h43 : e 4 = e 3) (hrec : ∀ n, e (n + j) = e n * e (n + 1)) :
    ∀ k, e k = 1 := by
  have hper : ∀ k q, e (k + 7 * q) = e k := by
    intro k q
    induction q with
    | zero => rfl
    | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, h7, ih]
  have hrec' : ∀ n, e (n + j % 7) = e n * e (n + 1) := by
    intro n
    rw [← hrec n, ← Nat.mod_add_div j 7, ← Nat.add_assoc, hper, Nat.mod_add_div]
  obtain ⟨e1, e2, e3⟩ := eq_one_of_seven_relations_aux e hj (Nat.le_of_lt_succ (Nat.mod_lt _
    (by norm_num))) h0 hsq h7 h61 h52 h43 hrec'
  intro k
  rw [← Nat.mod_add_div k 7, hper]
  have hk : k % 7 < 7 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 7)
  · exact h0
  · exact e1
  · exact e2
  · exact e3
  · rw [h43, e3]
  · rw [h52, e2]
  · rw [h61, e1]

end Relations

section Lifts

variable {E : Type*} [Group E]

theorem commutatorElement_mul_right_of_mem_center {u v w : E}
    (h : ⁅u, w⁆ ∈ Subgroup.center E) : ⁅u, v * w⁆ = ⁅u, v⁆ * ⁅u, w⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅u, v⁆,
    Subgroup.mem_center_iff.mp h v, mul_assoc, mul_inv_cancel_right]

theorem commutatorElement_mul_center {u v z : E} (hz : z ∈ Subgroup.center E) :
    ⁅u, v * z⁆ = ⁅u, v⁆ := by
  have h1 : ⁅u, z⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz u)
  rw [commutatorElement_mul_right_of_mem_center (h1 ▸ Subgroup.one_mem _), h1, mul_one]

theorem conj_eq_of_mem_center {k z : E} (hz : z ∈ Subgroup.center E) : k * z * k⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz k, mul_inv_cancel_right]

end Lifts

section Pairing

variable {E Q : Type*} [Group E] [Group Q]

theorem pow_conj_mem {T : Subgroup Q} {g : Q} (hgT : ∀ x ∈ T, g * x * g⁻¹ ∈ T) :
    ∀ k : ℕ, ∀ x ∈ T, g ^ k * x * (g ^ k)⁻¹ ∈ T := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    have h := hgT _ (ih x hx)
    rwa [show g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ = g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ by
      rw [pow_succ', mul_inv_rev]; group] at h

theorem pow_conj_mod_seven {T : Subgroup Q} {g : Q} (hg7 : ∀ x ∈ T, g ^ 7 * x * (g ^ 7)⁻¹ = x) :
    ∀ k : ℕ, ∀ x ∈ T, g ^ k * x * (g ^ k)⁻¹ = g ^ (k % 7) * x * (g ^ (k % 7))⁻¹ := by
  have hstep : ∀ k : ℕ, ∀ x ∈ T, g ^ (k + 7) * x * (g ^ (k + 7))⁻¹ =
      g ^ k * x * (g ^ k)⁻¹ := by
    intro k x hx
    rw [show g ^ (k + 7) * x * (g ^ (k + 7))⁻¹ = g ^ k * (g ^ 7 * x * (g ^ 7)⁻¹) * (g ^ k)⁻¹ by
      rw [pow_add, mul_inv_rev]; group, hg7 x hx]
  have hper : ∀ q r : ℕ, ∀ x ∈ T, g ^ (r + 7 * q) * x * (g ^ (r + 7 * q))⁻¹ =
      g ^ r * x * (g ^ r)⁻¹ := by
    intro q
    induction q with
    | zero => intro r x _; rfl
    | succ q ih =>
      intro r x hx
      rw [Nat.mul_succ, ← Nat.add_assoc, hstep _ x hx, ih r x hx]
  intro k x hx
  conv_lhs => rw [← Nat.mod_add_div k 7]
  exact hper _ _ x hx

theorem commute_of_transitive_seven (π : E →* Q) (hZ : π.ker ≤ Subgroup.center E)
    (T : Subgroup Q) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT2 : ∀ x ∈ T, x * x = 1)
    {g : Q} (hgT : ∀ x ∈ T, g * x * g⁻¹ ∈ T) (hg7 : ∀ x ∈ T, g ^ 7 * x * (g ^ 7)⁻¹ = x)
    (htrans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = y)
    {h : E} (hh : π h = g) {a b : E} (ha : π a ∈ T) (hb : π b ∈ T) : a * b = b * a := by
  have hcen : ∀ z ∈ π.ker, ∀ u : E, u * z = z * u := fun z hz u =>
    Subgroup.mem_center_iff.mp (hZ hz) u
  have hlift : ∀ u v : E, π u = π v → ∃ z ∈ π.ker, v = u * z := by
    intro u v huv
    refine ⟨u⁻¹ * v, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
  have hker : ∀ u v : E, π u ∈ T → π v ∈ T → ⁅u, v⁆ ∈ π.ker := by
    intro u v hu hv
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hTc _ hu _ hv
  by_cases ha1 : π a = 1
  · exact (hcen a ha1 b).symm
  by_cases hb1 : π b = 1
  · exact hcen b hb1 a
  set x := π a with hx
  set σ : ℕ → Q := fun k => g ^ k * x * (g ^ k)⁻¹ with hσ
  have hσT : ∀ k, σ k ∈ T := fun k => pow_conj_mem hgT k x ha
  set A : ℕ → E := fun k => h ^ k * a * (h ^ k)⁻¹ with hA
  have hπA : ∀ k, π (A k) = σ k := fun k => by
    simp only [hA, hσ, map_mul, map_inv, map_pow, hh, hx]
  have hA0 : A 0 = a := by simp [hA]
  have hAadd : ∀ m p, A (m + p) = h ^ m * A p * (h ^ m)⁻¹ := fun m p => by
    simp only [hA, pow_add, mul_inv_rev]; group
  have hxx : x * x = 1 := hT2 x ha
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  by_cases hfix : g * x * g⁻¹ = x
  ·
    have hσx : ∀ k, σ k = x := by
      intro k
      induction k with
      | zero => simp [hσ]
      | succ k ih =>
        change g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = x
        rw [pow_succ', mul_inv_rev]
        calc g * g ^ k * x * ((g ^ k)⁻¹ * g⁻¹) = g * (σ k) * g⁻¹ := by
              simp only [hσ]; group
          _ = x := by rw [ih, hfix]
    obtain ⟨k, hk⟩ := htrans x ha ha1 (π b) hb hb1
    have hbx : π a = π b := by rw [← hk]; exact (hσx k).symm
    obtain ⟨z, hz, rfl⟩ := hlift a b hbx
    rw [mul_assoc a z a, ← hcen z hz a]
  have hσ1 : σ 1 = g * x * g⁻¹ := by simp [hσ]
  have hprod : x * σ 1 ∈ T := T.mul_mem ha (hσT 1)
  have hprod1 : x * σ 1 ≠ 1 := by
    intro h1
    apply hfix
    rw [← hσ1, ← hxinv]
    exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨j, hj⟩ := htrans x ha ha1 _ hprod hprod1
  have hσmod : ∀ k, σ k = σ (k % 7) := fun k => pow_conj_mod_seven hg7 k x ha
  have hσinj : ∀ k, σ k = 1 → x = 1 := by
    intro k h1
    have h' : g ^ k * x * (g ^ k)⁻¹ = 1 := h1
    rw [mul_inv_eq_one, mul_eq_left] at h'
    exact h'
  have hj2 : 2 ≤ j % 7 := by
    have hj' : σ (j % 7) = x * σ 1 := by rw [← hσmod]; exact hj
    by_contra hlt
    push Not at hlt
    interval_cases hr : j % 7
    ·
      have h0 : σ 0 = x := by simp [hσ]
      rw [h0] at hj'
      exact ha1 (hσinj 1 (mul_eq_left.mp hj'.symm))
    ·
      exact ha1 (mul_eq_right.mp hj'.symm)
  have hAT : ∀ k, π (A k) ∈ T := fun k => (hπA k).symm ▸ hσT k
  have hdker : ∀ k, ⁅a, A k⁆ ∈ π.ker := fun k => hker a (A k) ha (hAT k)
  have hdc : ∀ k, ⁅a, A k⁆ ∈ Subgroup.center E := fun k => hZ (hdker k)
  have hinv : ∀ m p, ⁅A m, A (m + p)⁆ = ⁅a, A p⁆ := by
    intro m p
    have hm : A m = h ^ m * a * (h ^ m)⁻¹ := rfl
    rw [hAadd, hm, ← conjugate_commutatorElement, conj_eq_of_mem_center (hdc p)]
  have hcomm_eq : ∀ u v : E, π u = π v → ⁅a, u⁆ = ⁅a, v⁆ := by
    intro u v huv
    obtain ⟨z, hz, hv⟩ := hlift u v huv
    rw [hv, commutatorElement_mul_center (hZ hz)]
  have hd7 : ∀ k, ⁅a, A (k + 7)⁆ = ⁅a, A k⁆ := by
    intro k
    apply (hcomm_eq _ _ _).symm
    rw [hπA, hπA, hσmod (k + 7), hσmod k, Nat.add_mod_right]
  have hdsq : ∀ k, ⁅a, A k⁆ * ⁅a, A k⁆ = 1 := by
    intro k
    rw [← commutatorElement_mul_right_of_mem_center (hdc k)]
    have hAA : A k * A k ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, hπA]
      exact hT2 _ (hσT k)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hcen _ hAA a
  have hd0 : ⁅a, A 0⁆ = 1 := by rw [hA0, commutatorElement_self]
  have hA7 : π (A 7) = π a := by
    rw [hπA, hσmod 7]
    simp [hσ, hx]
  have hdsym : ∀ k, k ≤ 7 → ⁅a, A (7 - k)⁆ = ⁅a, A k⁆ := by
    intro k hk
    have h1 := hinv k (7 - k)
    rw [Nat.add_sub_cancel' hk] at h1
    rw [← h1]
    obtain ⟨z, hz, h7'⟩ := hlift a (A 7) hA7.symm
    rw [h7', commutatorElement_mul_center (hZ hz), ← commutatorElement_inv]
    exact inv_eq_of_mul_eq_one_right (hdsq k)
  have hrec : ∀ n, ⁅a, A (n + j)⁆ = ⁅a, A n⁆ * ⁅a, A (n + 1)⁆ := by
    intro n
    have hAj : π (A j) = π (a * A 1) := by
      rw [hπA, map_mul, hπA]
      exact hj
    obtain ⟨z, hz, hAj'⟩ := hlift (a * A 1) (A j) hAj.symm
    have hnj : A (n + j) = A n * A (n + 1) * z := by
      rw [hAadd n j, hAadd n 1, hAj']
      calc h ^ n * (a * A 1 * z) * (h ^ n)⁻¹ =
            h ^ n * a * (h ^ n)⁻¹ * (h ^ n * A 1 * (h ^ n)⁻¹) * (h ^ n * z * (h ^ n)⁻¹) := by
            group
        _ = A n * (h ^ n * A 1 * (h ^ n)⁻¹) * z := by
            rw [conj_eq_of_mem_center (hZ hz)]
    rw [hnj, commutatorElement_mul_center (hZ hz),
      commutatorElement_mul_right_of_mem_center (hdc (n + 1))]
  let e : ℕ → Subgroup.center E := fun k => ⟨⁅a, A k⁆, hdc k⟩
  have he : ∀ k, e k = 1 := by
    refine eq_one_of_seven_relations e hj2 (Subtype.ext hd0) (fun k => Subtype.ext (hdsq k))
      (fun k => Subtype.ext (hd7 k)) (Subtype.ext (hdsym 1 (by norm_num)))
      (Subtype.ext (hdsym 2 (by norm_num))) (Subtype.ext (hdsym 3 (by norm_num)))
      (fun n => Subtype.ext (hrec n))
  obtain ⟨k, hk⟩ := htrans x ha ha1 (π b) hb hb1
  have hbk : π (A k) = π b := by rw [hπA]; exact hk
  have hab : ⁅a, b⁆ = 1 := by
    rw [← hcomm_eq _ _ hbk]
    exact congrArg Subtype.val (he k)
  exact commutatorElement_eq_one_iff_mul_comm.mp hab

end Pairing

end CFSG.ComponentClassification.WalterSchur
