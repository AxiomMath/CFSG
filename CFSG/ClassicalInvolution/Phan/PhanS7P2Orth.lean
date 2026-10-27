module

public import CFSG.ClassicalInvolution.Phan.PhanS7P1Count
public import CFSG.ClassicalInvolution.Phan.PhanS5D6Common

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.P

open CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S.Std.D

variable {K : Type} [Field K] {M : Model K}

theorem conicPt_pencil (c d : Vec K) (μ : K) : conicPt c d 0 μ = c + μ • d := by
  simp [conicPt]

theorem bf_pencil_left (c d x : Vec K) (μ : K) :
    bf M (c + μ • d) x = bf M c x + μ * bf M d x := by
  rw [bf_add_left, bf_smul_left]

theorem bf_pencil_self (c d : Vec K) (μ : K) :
    bf M (c + μ • d) (c + μ • d) = bf M c c + 2 * μ * bf M c d + μ ^ 2 * bf M d d := by
  simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, bf_comm M d c]
  ring

theorem exists_cs_pencil {G : Vec K → Vec K → K} {c d : Vec K}
    (h : G c c ≠ 0 ∨ G c d ≠ 0 ∨ G d c ≠ 0 ∨ G d d ≠ 0) :
    ∃ i j : Fin 3, G (cs c d 0 i) (cs c d 0 j) ≠ 0 := by
  rcases h with h | h | h | h
  · exact ⟨0, 0, by rw [cs_zero]; exact h⟩
  · exact ⟨0, 1, by rw [cs_zero, cs_one]; exact h⟩
  · exact ⟨1, 0, by rw [cs_one, cs_zero]; exact h⟩
  · exact ⟨1, 1, by rw [cs_one]; exact h⟩

theorem gramForm_ne_zero_pair {a c d : Vec K} (ha : IsFF M a) (hcd : gram M c d ≠ 0) :
    gramForm M a c c ≠ 0 ∨ gramForm M a c d ≠ 0 ∨ gramForm M a d c ≠ 0 ∨
      gramForm M a d d ≠ 0 := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨h00, h01, h10, h11⟩ := hcon
  simp only [gramForm] at h00 h01 h10 h11
  have key : her M a a ^ 2 * gram M c d = 0 := by
    have e : her M a a ^ 2 * gram M c d =
        (her M a a * her M c c) * (her M a a * her M d d) -
          (her M a a * her M c d) * (her M a a * her M d c) := by
      simp only [gram]
      ring
    rw [e, show her M a a * her M c c = her M c a * her M a c by linear_combination h00,
      show her M a a * her M d d = her M d a * her M a d by linear_combination h11,
      show her M a a * her M c d = her M c a * her M a d by linear_combination h01,
      show her M a a * her M d c = her M d a * her M a c by linear_combination h10]
    ring
  rcases mul_eq_zero.1 key with h | h
  · exact ha.2 (pow_eq_zero_iff two_ne_zero |>.1 h)
  · exact hcd h

theorem exists_apex_orth [Finite K] (hq : 5 ≤ M.q) {a c d : Vec K} (ha : IsFF M a)
    (hc : IsFF M c) (hd : IsFF M d) (hcd : Col M c d) (hca : bf M c a = 0) (hda : bf M d a = 0) :
    ∃ f : Vec K, IsFF M f ∧ Col M f c ∧ Col M f d ∧ Col M f a := by
  have hdc : gram M d c ≠ 0 := by rw [gram_comm]; exact hcd.2
  have hdc' : bf M d c = 0 := by rw [bf_comm]; exact hcd.1
  have w₁ : ∃ i j : Fin 3, her M (cs c d 0 i) (cs c d 0 j) ≠ 0 :=
    exists_cs_pencil (Or.inl hc.2)
  have w₂ : ∃ i j : Fin 3, gramForm M c (cs c d 0 i) (cs c d 0 j) ≠ 0 :=
    exists_cs_pencil (Or.inr (Or.inr (Or.inr (by rw [gramForm_self]; exact hdc))))
  have w₃ : ∃ i j : Fin 3, gramForm M d (cs c d 0 i) (cs c d 0 j) ≠ 0 :=
    exists_cs_pencil (Or.inl (by rw [gramForm_self]; exact hcd.2))
  have w₄ : ∃ i j : Fin 3, gramForm M a (cs c d 0 i) (cs c d 0 j) ≠ 0 :=
    exists_cs_pencil (gramForm_ne_zero_pair ha hcd.2)
  obtain ⟨μ, h1, h2, h3, h4⟩ := exists_mu_pencil_four hq (sesq_her M) (sesq_gramForm M c)
    (sesq_gramForm M d) (sesq_gramForm M a) w₁ w₂ w₃ w₄
  simp only [conicPt_pencil] at h1 h2 h3 h4
  rw [gramForm_self] at h2 h3 h4
  refine ⟨c + μ • d, ⟨?_, h1⟩, ⟨?_, h2⟩, ⟨?_, h3⟩, ⟨?_, h4⟩⟩
  · rw [bf_pencil_self, hc.1, hd.1, hcd.1]
    ring
  · rw [bf_pencil_left, hc.1, hdc']
    ring
  · rw [bf_pencil_left, hcd.1, hd.1]
    ring
  · rw [bf_pencil_left, hca, hda]
    ring

end CFSG.ClassicalInvolution.PhanB3.S.Std.P
