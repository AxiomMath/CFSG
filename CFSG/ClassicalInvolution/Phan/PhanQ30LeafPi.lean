module

public import CFSG.ClassicalInvolution.Phan.PhanQ29LeafA
public import CFSG.ClassicalInvolution.Phan.PhanQ23Generic

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Plane6

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} {D : KData F K ε}

theorem exists_ratPlane (h2 : (2 : K) ≠ 0) {x y : V8 K} (hw : ∃ i j, wedge x y i j ≠ 0) :
    ∃ ω₁ ω₂ : V8 K, RatPlane D ω₁ ω₂ ∧ B8 ω₁ x * B8 ω₂ y - B8 ω₂ x * B8 ω₁ y ≠ 0 := by
  have key : ∀ {a b c d a' b' c' d' : K}, D.τ a = a → D.τ b = b → D.τ c = c → D.τ d = d →
      D.τ a' = a' → D.τ b' = b' → D.τ c' = c' → D.τ d' = d' → a * c + b * d = 0 →
      a' * c' + b' * d' = 0 → a * c' + b * d' + c * a' + d * b' = 0 →
      (a * x (Sum.inr 2) + b * x (Sum.inr 3) + c * x (Sum.inl 2) + d * x (Sum.inl 3)) *
          (a' * y (Sum.inr 2) + b' * y (Sum.inr 3) + c' * y (Sum.inl 2) + d' * y (Sum.inl 3)) -
        (a' * x (Sum.inr 2) + b' * x (Sum.inr 3) + c' * x (Sum.inl 2) + d' * x (Sum.inl 3)) *
          (a * y (Sum.inr 2) + b * y (Sum.inr 3) + c * y (Sum.inl 2) + d * y (Sum.inl 3)) ≠ 0 →
      ∃ ω₁ ω₂ : V8 K, RatPlane D ω₁ ω₂ ∧ B8 ω₁ x * B8 ω₂ y - B8 ω₂ x * B8 ω₁ y ≠ 0 := by
    intro a b c d a' b' c' d' ha hb hc hd ha' hb' hc' hd' h1 h2' h12 hΔ
    refine ⟨wvec a b c d, wvec a' b' c' d',
      ratPlane_wvec D ha hb hc hd ha' hb' hc' hd' h1 h2' h12, ?_⟩
    rw [B8_wvec_left, B8_wvec_left, B8_wvec_left, B8_wvec_left]
    exact hΔ
  by_contra hno
  set x1 := x (Sum.inl 2) with hx1
  set x2 := x (Sum.inl 3) with hx2
  set x3 := x (Sum.inr 2) with hx3
  set x4 := x (Sum.inr 3) with hx4
  set y1 := y (Sum.inl 2) with hy1
  set y2 := y (Sum.inl 3) with hy2
  set y3 := y (Sum.inr 2) with hy3
  set y4 := y (Sum.inr 3) with hy4
  have n1 : x3 * y4 - x4 * y3 = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 0) (c := 0) (d := 0) (a' := 0) (b' := 1) (c' := 0) (d' := 0)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n2 : x1 * y2 - x2 * y1 = 0 := by
    by_contra h
    exact hno (key (a := 0) (b := 0) (c := 1) (d := 0) (a' := 0) (b' := 0) (c' := 0) (d' := -1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination -h0))
  have n3 : (x3 - x2) * (y4 + y1) - (x4 + x1) * (y3 - y2) = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 0) (c := 0) (d := -1) (a' := 0) (b' := 1) (c' := 1) (d' := 0)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n4 : x2 * y3 - x3 * y2 = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 0) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := 0) (d' := -1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n5 : x4 * y1 - x1 * y4 = 0 := by
    by_contra h
    exact hno (key (a := 0) (b := 1) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := 1) (d' := 0)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n6 : (x3 + x4) * (y1 - y2) - (x1 - x2) * (y3 + y4) = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 1) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := 1) (d' := -1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have p13 : x1 * y3 - x3 * y1 = 0 := by
    have h : (2 : K) * (x1 * y3 - x3 * y1) = 0 := by
      linear_combination n1 + n2 - n3 - n6 + n4 + n5
    exact (mul_eq_zero.1 h).resolve_left h2
  have p24 : x2 * y4 - x4 * y2 = 0 := by
    have h : (2 : K) * (x2 * y4 - x4 * y2) = 0 := by
      linear_combination n1 + n2 - n3 + n6 - n4 - n5
    exact (mul_eq_zero.1 h).resolve_left h2
  obtain ⟨i, j, hij⟩ := hw
  fin_cases i <;> fin_cases j <;> simp [wedge, wc] at hij
  · apply hij
    linear_combination n2
  · apply hij
    linear_combination p13
  · apply hij
    linear_combination -n5
  · apply hij
    linear_combination -n2
  · apply hij
    linear_combination n4
  · apply hij
    linear_combination p24
  · apply hij
    linear_combination -p13
  · apply hij
    linear_combination -n4
  · apply hij
    linear_combination n1
  · apply hij
    linear_combination n5
  · apply hij
    linear_combination -p24
  · apply hij
    linear_combination -n1

end Plane6

section LeafPi

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

theorem leaf_pi (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d : V8 K} (Fr : QFrame D a b c d)
    {κ : K} (hκ : κ ≠ 0) (hcd2 : ∀ k, wc c k = κ * wc d k)
    (hnr : ∃ i j, wedge d (conj D d) i j ≠ 0) : Resolved D a b c d := by
  obtain ⟨ω₁, ω₂, P, hΔ⟩ := exists_ratPlane (D := D) h2 hnr
  have hconj₁ : B8 ω₁ (conj D d) = D.τ (B8 ω₁ d) := by
    have := B8_conj D ω₁ d
    rwa [P.fix₁] at this
  have hconj₂ : B8 ω₂ (conj D d) = D.τ (B8 ω₂ d) := by
    have := B8_conj D ω₂ d
    rwa [P.fix₂] at this
  rw [hconj₁, hconj₂] at hΔ
  have hΔ' : B8 ω₁ d * D.τ (B8 ω₂ d) - B8 ω₂ d * D.τ (B8 ω₁ d) ≠ 0 := hΔ
  have htW : InW2 (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) := inW2_comb P.inW2₁ P.inW2₂ _ _
  have hQt : Q8 (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) = 0 := P.Q_comb _ _
  have hhtt : her D (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) = 0 :=
    P.her_comb _ _ _ _
  have hBtd : B8 (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) d = 0 := by
    rw [B8_lin_left]
    ring
  have hcω : ∀ ω : V8 K, InW2 ω → B8 ω c = κ * B8 ω d := fun ω hω => B8_W2_of_coord hω κ hcd2
  have hBct : B8 c (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) = 0 := by
    rw [B8_comm, B8_lin_left, hcω ω₁ P.inW2₁, hcω ω₂ P.inW2₂]
    ring
  have hherct : her D c (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) =
      κ * (B8 ω₁ d * D.τ (B8 ω₂ d) - B8 ω₂ d * D.τ (B8 ω₁ d)) := by
    rw [her, P.conj_comb, B8_lin_right, map_neg, B8_comm c ω₁, B8_comm c ω₂,
      hcω ω₁ P.inW2₁, hcω ω₂ P.inW2₂]
    ring
  have hne : her D c (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) ≠ 0 := by
    rw [hherct]
    exact mul_ne_zero hκ hΔ'
  have hβ : B8 ω₁ d ≠ 0 ∨ B8 ω₂ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hΔ'
    rw [h.1, h.2]
    simp
  have hω₁t : B8 ω₁ (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) = 0 := by
    have := P.B_comb 1 0 (B8 ω₂ d) (-B8 ω₁ d)
    simpa using this
  have hω₂t : B8 ω₂ (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂) = 0 := by
    have := P.B_comb 0 1 (B8 ω₂ d) (-B8 ω₁ d)
    simpa using this
  have hw : ∀ μ : K, μ ≠ 0 →
      ∃ i j, wedge (c + μ • (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂)) d i j ≠ 0 := by
    intro μ hμ
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, j0, hd0⟩ := hnr
    obtain ⟨l, m, hlm, hrel⟩ := exists_parallel_of_wedge_zero
      (X := wc (c + μ • (B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂))) (Y := wc d)
      (fun i j => hcon i j)
    set t := B8 ω₂ d • ω₁ + (-B8 ω₁ d) • ω₂ with ht
    have hdnz : ∃ k, wc d k ≠ 0 := by
      by_contra h
      push Not at h
      apply hd0
      simp [wedge, wc_conj, h]
    have hl : l ≠ 0 := by
      intro hl0
      rcases hlm with h | h
      · exact h hl0
      · obtain ⟨k, hk⟩ := hdnz
        have := hrel k
        rw [hl0, zero_mul, zero_add] at this
        exact hk ((mul_eq_zero.1 this).resolve_left h)
    set lam : K := -(l * κ + m) / (l * μ) with hlam
    have hct' : ∀ k, wc t k = lam * wc d k := by
      intro k
      have := hrel k
      rw [wc_add, wc_smul, hcd2 k] at this
      rw [hlam]
      field_simp
      linear_combination this
    have e1 : B8 ω₁ t = lam * B8 ω₁ d := B8_W2_of_coord P.inW2₁ lam hct'
    have e2 : B8 ω₂ t = lam * B8 ω₂ d := B8_W2_of_coord P.inW2₂ lam hct'
    rw [hω₁t] at e1
    rw [hω₂t] at e2
    have hlam0 : lam = 0 := by
      rcases hβ with h | h
      · exact (mul_eq_zero.1 e1.symm).resolve_right h
      · exact (mul_eq_zero.1 e2.symm).resolve_right h
    have ht0 : t = 0 := by
      refine eq_of_wc_eq htW (fun i hi => ?_) fun k => ?_
      · simp
      · rw [hct' k, hlam0, zero_mul]
        fin_cases k <;> simp [wc]
    apply hne
    rw [ht0]
    have h0 := her_smul_right D (0 : K) c (0 : V8 K)
    rw [zero_smul, map_zero, zero_mul] at h0
    exact h0
  exact resolved_of_T D h2 hq2 hq5 Fr htW hQt hhtt hBct hBtd hne hw

end LeafPi

end CFSG.ClassicalInvolution.PhanQ
