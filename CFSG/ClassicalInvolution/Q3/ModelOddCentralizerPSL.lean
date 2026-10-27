module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLDiag
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLComplex

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Square

variable {F : Type} [Field F] [Finite F]

theorem oddCoreIn_centralizer_eq_bot_of_sq_eq_one (hF : Nat.card F = 3) {n : ℕ} (g : SL(n, F))
    (hg2 : (g : Matrix (Fin n) (Fin n) F) * g = 1) (hgc : g ∉ Subgroup.center SL(n, F)) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : SL(n, F) ⧸ Subgroup.center SL(n, F))} :
        Set (SL(n, F) ⧸ Subgroup.center SL(n, F)))) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (Subsingleton.elim g 1 ▸ Subgroup.one_mem _) hgc
    · exact hn
  obtain ⟨a, han, P, hP⟩ := exists_sl_conj_diagonal h2 hn hg2
  set g₀ : SL(n, F) := P⁻¹ * g * P with hg₀
  have hg₀m : (g₀ : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun j : Fin n => if j.val < a then (-1 : F) else 1) := by
    rw [hg₀, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_assoc, hP, ← Matrix.mul_assoc, coe_inv_mul_coe, Matrix.one_mul]
  have hg₀c : g₀ ∉ Subgroup.center SL(n, F) := by
    intro hc
    apply hgc
    have hg : g = g₀ := by
      calc g = P * g₀ * P⁻¹ := by rw [hg₀]; group
        _ = g₀ * P * P⁻¹ := by rw [Subgroup.mem_center_iff.mp hc P]
        _ = g₀ := by group
    rw [hg]
    exact hc
  have ha0 : 0 < a := by
    by_contra h
    have h0 : a = 0 := by omega
    apply hg₀c
    have : g₀ = 1 := by
      ext i j
      rw [hg₀m, h0]
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [this]
    exact Subgroup.one_mem _
  have han' : a < n := by
    by_contra h
    have hn' : a = n := by omega
    apply hg₀c
    have hdiag : (g₀ : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) (-1 : F) := by
      rw [hg₀m, Matrix.scalar_apply]
      congr 1
      funext j
      have := j.isLt
      simp [show j.val < a by omega]
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, ?_, hdiag.symm⟩
    have hdet := g₀.2
    rw [hdiag, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  have hneg : (g₀ : Matrix (Fin n) (Fin n) F) = negBlockK F n 0 a := by
    rw [hg₀m, negBlockK_eq_diagonal]
    congr 1
    funext x
    simp
  refine oddCoreIn_centralizer_eq_bot_of_equiv (MulAut.conj P⁻¹ : SL(n, F) ≃* SL(n, F)) g ?_
  have e : (MulAut.conj P⁻¹ : SL(n, F) ≃* SL(n, F)) g = g₀ := by simp [hg₀]
  rw [e]
  exact oddCoreIn_centralizer_eq_bot_of_blockDiag hF ha0 han' g₀ hneg

theorem oddCoreIn_centralizer_eq_bot_of_orderOf_eq_two (hF : Nat.card F = 3) {n : ℕ} (hn : 3 ≤ n)
    (s : SL(n, F) ⧸ Subgroup.center SL(n, F)) (hs : orderOf s = 2) :
    oddCoreIn (Subgroup.centralizer ({s} : Set (SL(n, F) ⧸ Subgroup.center SL(n, F)))) = ⊥ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hs2 : (QuotientGroup.mk g : SL(n, F) ⧸ Subgroup.center SL(n, F)) ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one _
  have hs1 : (QuotientGroup.mk g : SL(n, F) ⧸ Subgroup.center SL(n, F)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hgc : g ∉ Subgroup.center SL(n, F) := fun h => hs1 ((QuotientGroup.eq_one_iff g).mpr h)
  have hg2c : g ^ 2 ∈ Subgroup.center SL(n, F) :=
    (QuotientGroup.eq_one_iff (g ^ 2)).mp (by rw [QuotientGroup.mk_pow]; exact hs2)
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg2c
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by omega)] at hr
    exact zero_ne_one hr
  have hrr : r * r = 1 := by
    have : Fintype F := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one r hr0
    rw [← Nat.card_eq_fintype_card, hF] at h1
    simpa [pow_two] using h1
  have hgg : (g : Matrix (Fin n) (Fin n) F) * g = Matrix.scalar (Fin n) r := by
    rw [hrg, pow_two, Matrix.SpecialLinearGroup.coe_mul]
  rcases mul_self_eq_one_iff.mp hrr with h1 | h1
  · refine oddCoreIn_centralizer_eq_bot_of_sq_eq_one hF g ?_ hgc
    rw [hgg, h1]
    simp
  · refine oddCoreIn_centralizer_eq_bot_of_sq_eq_neg_one hF hn g ?_
    rw [hgg, h1, Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j <;> simp [hij]

end Square

theorem simpleOddCentralizerFreeTag_PSL : SimpleOddCentralizerFreeTag .PSL := by
  intro n hp hadm s hs
  have hn : 3 ≤ n := by
    obtain ⟨_, _, h2n, _, h23⟩ := hadm
    by_contra h
    have h2 : n = 2 := by omega
    exact h23 (by simp [h2])
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    simpa using GaloisField.card 3 1 one_ne_zero
  exact oddCoreIn_centralizer_eq_bot_of_orderOf_eq_two hF hn s hs

end CFSG.ClassicalInvolution.Q3
