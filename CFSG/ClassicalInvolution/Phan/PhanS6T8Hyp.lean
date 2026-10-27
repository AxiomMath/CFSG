module

public import CFSG.ClassicalInvolution.Phan.PhanS6T3Octa
public import CFSG.ClassicalInvolution.Phan.PhanS6T5Count

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] {M : Model K}

theorem exists_hyp [Finite K] (hq : 7 ≤ M.q) (g : Gd M) {α β : K} (hna : g.na ≠ 0)
    (hnb : g.nb ≠ 0) (hD : g.D ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hnc : g.nc α β ≠ 0)
    (hζ : g.ζ ≠ 0) : ∃ w u : K, Gd.Hyp g α β w u := by
  classical
  have := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := M.two_ne
  have hNα : nrm M α ≠ 0 := norm_ne_zero M hα
  have hNβ : nrm M β ≠ 0 := norm_ne_zero M hβ
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_w M (by omega) (g.na / (2 * g.ζ * nrm M β * g.D))
    (g.nb / (2 * g.ζ * nrm M α * g.D))
  have hs : w - M.τ w ≠ 0 := sub_ne_zero.2 fun h => hw1 h.symm
  have hnf : g.nf w ≠ 0 := by
    simp only [Gd.nf]
    exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero h2 hζ) (pow_ne_zero 2 hs))
  have hF1 : nrm M β * g.D * g.nf w + g.na ≠ 0 := by
    intro h
    apply hw2
    simp only [Gd.nf] at h
    field_simp
    linear_combination (-1 : K) * h
  have hF2 : nrm M α * g.D * g.nf w + g.nb ≠ 0 := by
    intro h
    apply hw3
    simp only [Gd.nf] at h
    field_simp
    linear_combination (-1 : K) * h
  obtain ⟨u, hu⟩ := exists_u M hq
    ![1, 1, 1, 1, M.τ α, M.τ β]
    ![0, 0, 0, 0, α * g.h + β * g.nb, -(α * g.na + β * M.τ g.h)]
    ![-(g.D * (nrm M α * g.D * g.nf w + g.nb)) / g.nb,
      -(g.D * (nrm M β * g.D * g.nf w + g.na)) / g.na, -g.D,
      -(g.D * g.nf w * g.nc α β + g.D), -(nrm M α * g.D * g.nf w * g.nc α β),
      -(nrm M β * g.D * g.nf w * g.nc α β)]
    (by
      intro i
      fin_cases i <;> simp [tau_ne_zero M hα, tau_ne_zero M hβ])
  have hu0 := hu 0
  have hu1 := hu 1
  have hu2 := hu 2
  have hu3 := hu 3
  have hu4 := hu 4
  have hu5 := hu 5
  simp only [nrm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul, add_zero]
    at hu0 hu1 hu2 hu3 hu4 hu5
  refine ⟨w, u, ⟨hna, hnb, hD, hα, hβ, hnc, hζ, hw1, hF1, hF2, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h
    apply hu0
    simp only [nrm] at h
    field_simp
    linear_combination h
  · intro h
    apply hu1
    simp only [nrm] at h
    field_simp
    linear_combination h
  · intro h
    apply hu2
    linear_combination h
  · intro h
    apply hu3
    linear_combination h
  · intro h
    apply hu4
    simp only [nrm] at h
    linear_combination h
  · intro h
    apply hu5
    simp only [nrm, sub_eq_add_neg] at h
    linear_combination h

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
