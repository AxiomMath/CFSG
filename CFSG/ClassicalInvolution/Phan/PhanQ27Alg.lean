module

public import CFSG.ClassicalInvolution.Phan.PhanQ22Plane

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Alg

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem Q8_add' {R : Type} [Field R] (x y : V8 R) : Q8 (x + y) = Q8 x + Q8 y + B8 x y := by
  have h := Q8_lin (1 : R) 1 x y
  rw [one_smul, one_smul] at h
  rw [h]
  ring

theorem B8_zero_self {R : Type} [Field R] {x : V8 R} (hx : Q8 x = 0) : B8 x x = 0 := by
  rw [B8_self, hx, mul_zero]

theorem InW0.coord {v : V8 K} (hv : InW0 v) :
    v (Sum.inl 2) = 0 ∧ v (Sum.inr 2) = 0 ∧ v (Sum.inl 3) = 0 ∧ v (Sum.inr 3) = 0 := by
  obtain ⟨h1, h2⟩ := hv 2 (by decide)
  obtain ⟨h3, h4⟩ := hv 3 (by decide)
  exact ⟨h1, h2, h3, h4⟩

theorem inW0_of_coord {v : V8 K} (h1 : v (Sum.inl 2) = 0) (h2 : v (Sum.inr 2) = 0)
    (h3 : v (Sum.inl 3) = 0) (h4 : v (Sum.inr 3) = 0) : InW0 v := by
  intro i hi
  fin_cases i
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact ⟨h1, h2⟩
  · exact ⟨h3, h4⟩

theorem her_zero_of_W0_W2 {u v : V8 K} (hu : InW0 u) (hv : InW2 v) : her D u v = 0 :=
  B8_eq_zero_of_support hu (inW2_conj D hv)

theorem her_zero_of_W2_W0 {u v : V8 K} (hu : InW2 u) (hv : InW0 v) : her D u v = 0 := by
  rw [her, B8_comm]
  exact B8_eq_zero_of_support (inW0_conj D hv) hu

theorem B8_zero_of_W2_W0 {u v : V8 K} (hu : InW2 u) (hv : InW0 v) : B8 u v = 0 := by
  rw [B8_comm]
  exact B8_eq_zero_of_support hv hu

theorem her_wvec_left (a b c d : K) (z : V8 K) :
    her D (wvec a b c d) z = a * D.τ (z (Sum.inr 2)) + b * D.τ (z (Sum.inr 3)) +
      c * D.τ (z (Sum.inl 2)) + d * D.τ (z (Sum.inl 3)) := by
  rw [her, B8_wvec_left]
  rfl

theorem her_wvec_right (a b c d : K) (z : V8 K) :
    her D z (wvec a b c d) = D.τ a * z (Sum.inr 2) + D.τ b * z (Sum.inr 3) +
      D.τ c * z (Sum.inl 2) + D.τ d * z (Sum.inl 3) := by
  rw [her, conj_wvec, B8_comm, B8_wvec_left]

theorem wvec_apply_inl2 (a b c d : K) : (wvec a b c d) (Sum.inl 2) = a := rfl
theorem wvec_apply_inl3 (a b c d : K) : (wvec a b c d) (Sum.inl 3) = b := rfl
theorem wvec_apply_inr2 (a b c d : K) : (wvec a b c d) (Sum.inr 2) = c := rfl
theorem wvec_apply_inr3 (a b c d : K) : (wvec a b c d) (Sum.inr 3) = d := rfl

theorem wc_add (x y : V8 K) (k : Fin 4) : wc (x + y) k = wc x k + wc y k := by
  fin_cases k <;> simp [wc]

theorem wc_smul (μ : K) (x : V8 K) (k : Fin 4) : wc (μ • x) k = μ * wc x k := by
  fin_cases k <;> simp [wc]

theorem wc_of_inW0 {v : V8 K} (hv : InW0 v) (k : Fin 4) : wc v k = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hv.coord
  fin_cases k <;> simp [wc, h1, h2, h3, h4]

theorem wc_wvec (a b c d : K) (k : Fin 4) : wc (wvec a b c d) k = ![a, b, c, d] k := by
  fin_cases k <;> simp [wc, wvec]

omit [Field K] in
theorem wc_zero (z : V8 K) : wc z 0 = z (Sum.inl 2) := rfl

omit [Field K] in
theorem wc_one (z : V8 K) : wc z 1 = z (Sum.inl 3) := rfl

omit [Field K] in
theorem wc_two (z : V8 K) : wc z 2 = z (Sum.inr 2) := rfl

omit [Field K] in
theorem wc_three (z : V8 K) : wc z 3 = z (Sum.inr 3) := rfl

theorem eq_of_wc_eq {x y : V8 K} (hx : InW2 x) (hy : InW2 y) (h : ∀ k, wc x k = wc y k) :
    x = y := by
  ext i
  rcases i with i | i
  · fin_cases i
    · exact (hx 0 (by decide)).1.trans (hy 0 (by decide)).1.symm
    · exact (hx 1 (by decide)).1.trans (hy 1 (by decide)).1.symm
    · exact h 0
    · exact h 1
  · fin_cases i
    · exact (hx 0 (by decide)).2.trans (hy 0 (by decide)).2.symm
    · exact (hx 1 (by decide)).2.trans (hy 1 (by decide)).2.symm
    · exact h 2
    · exact h 3

theorem B8_W2_of_coord {ω c d : V8 K} (hω : InW2 ω) (κ : K)
    (hcd : ∀ k, wc c k = κ * wc d k) : B8 ω c = κ * B8 ω d := by
  have e : ω = wvec (ω (Sum.inl 2)) (ω (Sum.inl 3)) (ω (Sum.inr 2)) (ω (Sum.inr 3)) := by
    refine eq_of_wc_eq hω (inW2_wvec _ _ _ _) fun k => ?_
    fin_cases k <;> simp [wc, wvec]
  rw [e, B8_wvec_left, B8_wvec_left]
  have h0 := hcd 0
  have h1 := hcd 1
  have h2 := hcd 2
  have h3 := hcd 3
  rw [wc_zero, wc_zero] at h0
  rw [wc_one, wc_one] at h1
  rw [wc_two, wc_two] at h2
  rw [wc_three, wc_three] at h3
  rw [h0, h1, h2, h3]
  ring

end Alg

end CFSG.ClassicalInvolution.PhanQ
