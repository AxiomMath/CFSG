module

public import CFSG.ClassicalInvolution.Phan.PhanQ27Move

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Leaf0

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem exists_T (β : K) {d : V8 K}
    (hd : d (Sum.inl 2) ≠ 0 ∨ d (Sum.inl 3) ≠ 0 ∨ d (Sum.inr 2) ≠ 0 ∨ d (Sum.inr 3) ≠ 0) :
    ∃ t1 t2 t3 t4 : K, ((t3 = 0 ∧ t4 = 0) ∨ (t1 = 0 ∧ t2 = 0)) ∧
      t1 * d (Sum.inr 2) + t2 * d (Sum.inr 3) + t3 * d (Sum.inl 2) + t4 * d (Sum.inl 3) = -β ∧
      (∃ i j, wedge (wvec t1 t2 t3 t4) d i j ≠ 0) ∧
      (β = 0 → (∀ i j, wedge d (conj D d) i j = 0) →
        her D d (wvec t1 t2 t3 t4) = 0) := by
  by_cases hC : d (Sum.inr 2) = 0
  · by_cases hD : d (Sum.inr 3) = 0
    · by_cases hA : d (Sum.inl 2) = 0
      · have hB : d (Sum.inl 3) ≠ 0 := by
          rcases hd with h | h | h | h
          · exact absurd hA h
          · exact h
          · exact absurd hC h
          · exact absurd hD h
        refine ⟨0, 0, d (Sum.inl 3), -β / d (Sum.inl 3), Or.inr ⟨rfl, rfl⟩, ?_, ⟨2, 1, ?_⟩, ?_⟩
        · rw [hC, hD, hA]
          field_simp
          ring
        · simp [wedge, wc, wvec, hB]
        · intro hβ _
          rw [her_wvec_right]
          simp [hβ, hC, hD, hA]
      · refine ⟨0, 0, -β / d (Sum.inl 2) + d (Sum.inl 3), -d (Sum.inl 2), Or.inr ⟨rfl, rfl⟩, ?_,
          ⟨3, 0, ?_⟩, ?_⟩
        · rw [hC, hD]
          field_simp
          ring
        · simp [wedge, wc, wvec, hA]
        · intro hβ hrat
          have h01 := hrat 0 1
          simp [wedge, wc, conj, hC, hD] at h01
          rw [her_wvec_right]
          simp [hβ, hC, hD]
          linear_combination h01
    · refine ⟨d (Sum.inr 3), -β / d (Sum.inr 3), 0, 0, Or.inl ⟨rfl, rfl⟩, ?_, ⟨0, 3, ?_⟩, ?_⟩
      · rw [hC]
        field_simp
        ring
      · simp [wedge, wc, wvec, hD]
      · intro hβ _
        rw [her_wvec_right]
        simp [hβ, hC]
  · refine ⟨-β / d (Sum.inr 2) + d (Sum.inr 3), -d (Sum.inr 2), 0, 0, Or.inl ⟨rfl, rfl⟩, ?_,
      ⟨1, 2, ?_⟩, ?_⟩
    · field_simp
      ring
    · simp [wedge, wc, wvec, hC]
    · intro hβ hrat
      have h23 := hrat 2 3
      simp [wedge, wc, conj] at h23
      rw [her_wvec_right]
      simp [hβ]
      linear_combination h23

end Leaf0

section LeafNR0

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
theorem wedge_move_bT {b c d T : V8 K} (hb : InW0 b) (κ μ : K)
    (hcd : ∀ k, wc c k = κ * wc d k) (i j : Fin 4) :
    wedge (c + μ • (b + T)) d i j = μ * wedge T d i j := by
  have e : ∀ k, wc (c + μ • (b + T)) k = κ * wc d k + μ * wc T k := by
    intro k
    rw [wc_add, wc_smul, wc_add, wc_of_inW0 hb, hcd k]
    ring
  unfold wedge
  rw [e i, e j]
  ring

omit [Fintype K] [DecidableEq K] in
theorem Q8_wvec_shape {t1 t2 t3 t4 : K} (hsh : (t3 = 0 ∧ t4 = 0) ∨ (t1 = 0 ∧ t2 = 0)) :
    Q8 (wvec t1 t2 t3 t4) = 0 := by
  rw [Q8_wvec]
  rcases hsh with ⟨h3, h4⟩ | ⟨h1, h2⟩
  · rw [h3, h4]
    ring
  · rw [h1, h2]
    ring

omit [Fintype K] [DecidableEq K] in
theorem her_wvec_shape {t1 t2 t3 t4 : K} (hsh : (t3 = 0 ∧ t4 = 0) ∨ (t1 = 0 ∧ t2 = 0)) :
    her D (wvec t1 t2 t3 t4) (wvec t1 t2 t3 t4) = 0 := by
  rw [her_wvec_left]
  simp only [wvec_apply_inl2, wvec_apply_inl3, wvec_apply_inr2, wvec_apply_inr3]
  rcases hsh with ⟨h3, h4⟩ | ⟨h1, h2⟩
  · rw [h3, h4]
    simp
  · rw [h1, h2]
    simp

theorem leaf_NR0 (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d : V8 K} (Fr : QFrame D a b c d)
    (hc0 : InW0 c)
    (hd : d (Sum.inl 2) ≠ 0 ∨ d (Sum.inl 3) ≠ 0 ∨ d (Sum.inr 2) ≠ 0 ∨ d (Sum.inr 3) ≠ 0) :
    Resolved D a b c d := by
  obtain ⟨t1, t2, t3, t4, hsh, hB, ⟨i, j, hij⟩, -⟩ := exists_T D (B8 b d) hd
  have hT : InW2 (wvec t1 t2 t3 t4) := inW2_wvec t1 t2 t3 t4
  refine resolved_of_bT D h2 hq2 hq5 Fr hT (Q8_wvec_shape hsh) (her_wvec_shape D hsh)
    (B8_eq_zero_of_support hc0 hT) ?_ (her_zero_of_W0_W2 D hc0 hT) ?_
  · rw [B8_wvec_left]
    exact hB
  · intro μ hμ
    refine ⟨i, j, ?_⟩
    rw [wedge_move_bT Fr.hb 0 μ (fun k => by rw [wc_of_inW0 hc0, zero_mul]) i j]
    exact mul_ne_zero hμ hij

theorem leaf_P (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d : V8 K} (Fr : QFrame D a b c d)
    (κ : K) (hcd2 : ∀ k, wc c k = κ * wc d k) (hrat : ∀ i j, wedge d (conj D d) i j = 0)
    (hbd : B8 b d = 0)
    (hd : d (Sum.inl 2) ≠ 0 ∨ d (Sum.inl 3) ≠ 0 ∨ d (Sum.inr 2) ≠ 0 ∨ d (Sum.inr 3) ≠ 0) :
    Resolved D a b c d := by
  obtain ⟨t1, t2, t3, t4, hsh, hB, ⟨i, j, hij⟩, hher⟩ := exists_T D (B8 b d) hd
  have hT : InW2 (wvec t1 t2 t3 t4) := inW2_wvec t1 t2 t3 t4
  have e0 : c (Sum.inl 2) = κ * d (Sum.inl 2) := by
    have := hcd2 0
    rwa [wc_zero, wc_zero] at this
  have e1 : c (Sum.inl 3) = κ * d (Sum.inl 3) := by
    have := hcd2 1
    rwa [wc_one, wc_one] at this
  have e2 : c (Sum.inr 2) = κ * d (Sum.inr 2) := by
    have := hcd2 2
    rwa [wc_two, wc_two] at this
  have e3 : c (Sum.inr 3) = κ * d (Sum.inr 3) := by
    have := hcd2 3
    rwa [wc_three, wc_three] at this
  have hdT : B8 (wvec t1 t2 t3 t4) d = -B8 b d := by
    rw [B8_wvec_left]
    exact hB
  refine resolved_of_bT D h2 hq2 hq5 Fr hT (Q8_wvec_shape hsh) (her_wvec_shape D hsh) ?_ hdT ?_ ?_
  · rw [B8_comm, B8_wvec_left, e0, e1, e2, e3]
    have : t1 * (κ * d (Sum.inr 2)) + t2 * (κ * d (Sum.inr 3)) + t3 * (κ * d (Sum.inl 2)) +
        t4 * (κ * d (Sum.inl 3)) = κ * (t1 * d (Sum.inr 2) + t2 * d (Sum.inr 3) +
          t3 * d (Sum.inl 2) + t4 * d (Sum.inl 3)) := by ring
    rw [this, hB, hbd]
    ring
  · have h0 := hher hbd hrat
    rw [her_wvec_right] at h0 ⊢
    rw [e0, e1, e2, e3]
    linear_combination κ * h0
  · intro μ hμ
    refine ⟨i, j, ?_⟩
    rw [wedge_move_bT Fr.hb κ μ hcd2 i j]
    exact mul_ne_zero hμ hij

end LeafNR0

end CFSG.ClassicalInvolution.PhanQ
