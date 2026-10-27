module

public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup Matrix GL83.I713
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem two_le_pRank_caseC {K : Type*} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) {x : K} (hx : x ≠ 0) (hxr : x ^ r = 1)
    (hkey : ∀ m : ℕ, x ^ m = 1 → r ∣ m) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (projectiveSL 3 K)) := by
  have hdA : ∏ k : Fin 3, (![x, x⁻¹, 1] : Fin 3 → K) k = 1 := by
    simp [Fin.prod_univ_three, mul_inv_cancel₀ hx]
  have hdB : ∏ k : Fin 3, (![1, x, x⁻¹] : Fin 3 → K) k = 1 := by
    simp [Fin.prod_univ_three, mul_inv_cancel₀ hx]
  obtain ⟨A, hAc⟩ : ∃ A : SpecialLinearGroup (Fin 3) K,
      (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![x, x⁻¹, 1] := ⟨diagSL _ hdA, rfl⟩
  obtain ⟨B, hBc⟩ : ∃ B : SpecialLinearGroup (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, x, x⁻¹] := ⟨diagSL _ hdB, rfl⟩
  have hAB : A * B = B * A := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hAc, hBc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _)
  have hApow : A ^ r = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hAc,
      Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [hxr, inv_pow])
  have hBpow : B ^ r = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hBc,
      Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [hxr, inv_pow])
  have hu : proj 3 K A ^ r = 1 := by rw [← map_pow (proj 3 K) A r, hApow, map_one]
  have hv : proj 3 K B ^ r = 1 := by rw [← map_pow (proj 3 K) B r, hBpow, map_one]
  have hcomm : Commute (proj 3 K A) (proj 3 K B) := by
    show proj 3 K A * proj 3 K B = proj 3 K B * proj 3 K A
    rw [← map_mul, ← map_mul, hAB]
  have hind : ∀ i j : ℕ, proj 3 K A ^ i * proj 3 K B ^ j = 1 → r ∣ i ∧ r ∣ j := by
    intro i j h
    have h' : proj 3 K (A ^ i * B ^ j) = 1 := by
      rw [map_mul, map_pow, map_pow]
      exact h
    rw [proj_eq_one_iff, mem_scalars] at h'
    obtain ⟨c, -, hM⟩ := h'
    have hM' : diagonal (![x, x⁻¹, 1] : Fin 3 → K) ^ i * diagonal (![1, x, x⁻¹] : Fin 3 → K) ^ j
        = scalar (Fin 3) (c : K) := by
      rw [← hAc, ← hBc, ← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_pow,
        ← Matrix.SpecialLinearGroup.coe_mul]
      exact hM
    have hdiag : ∀ k : Fin 3, (![x, x⁻¹, 1] : Fin 3 → K) k ^ i * (![1, x, x⁻¹] : Fin 3 → K) k ^ j
        = (c : K) := by
      intro k
      have := congrFun (congrFun hM' k) k
      rw [diagonal_pow_mul_diagonal_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
      exact this
    have h0 := hdiag 0
    have h1 := hdiag 1
    have h2 := hdiag 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_pow, mul_one,
      one_mul, inv_pow] at h0 h1 h2
    have hy0 : x ^ i ≠ 0 := pow_ne_zero _ hx
    have hxj : x ^ j = (x ^ i)⁻¹ := by
      have : (x ^ j)⁻¹ = x ^ i := by rw [h2, ← h0]
      rw [← this, inv_inv]
    have hy3 : (x ^ i) ^ 3 = 1 := by
      have h1' : (x ^ i)⁻¹ * (x ^ i)⁻¹ = x ^ i := by
        have h1'' := h1
        rw [hxj] at h1''
        exact h1''.trans h0.symm
      calc (x ^ i) ^ 3 = (x ^ i) ^ 2 * x ^ i := by ring
        _ = (x ^ i) ^ 2 * ((x ^ i)⁻¹ * (x ^ i)⁻¹) := by rw [h1']
        _ = 1 := by field_simp
    have hr3i : r ∣ 3 * i := hkey _ (by rw [mul_comm, pow_mul]; exact hy3)
    have hri : r ∣ i := by
      rcases (Nat.Prime.dvd_mul hr).1 hr3i with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3) hr3
      · exact h3
    have hxi : x ^ i = 1 := by
      obtain ⟨t, rfl⟩ := hri
      rw [pow_mul, hxr, one_pow]
    refine ⟨hri, hkey _ ?_⟩
    rw [hxj, hxi, inv_one]
  exact two_le_pRank_of_commute hr hcomm hu hv hind

theorem two_le_pRank_psl_of_dvd_sub_one {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (projectiveSL n K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvdK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hrq
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' r hdvdK
  have hωK : (ω : K) ^ r = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one ω)
    rw [hω] at h
    simpa using h
  have hkey : ∀ m : ℕ, (ω : K) ^ m = 1 → r ∣ m := by
    intro m hm
    rw [← hω, orderOf_dvd_iff_pow_eq_one]
    ext
    simpa using hm
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · have hn3 : n = 3 := by omega
    subst hn3
    by_cases hr3 : r = 3
    · subst hr3
      exact two_le_pRank_caseB (Units.ne_zero ω) hωK hkey
    · exact two_le_pRank_caseC hr hr2 hr3 (Units.ne_zero ω) hωK hkey
  · exact two_le_pRank_caseA hge hr hr2 (Units.ne_zero ω) hωK hkey

theorem not_dvd_sub_one_of_pRank_le_one {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL n K)) ≤ 1) :
    ¬ p ∣ Nat.card K - 1 := fun h =>
  absurd (two_le_pRank_psl_of_dvd_sub_one hn hp (by omega) h) (by omega)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
