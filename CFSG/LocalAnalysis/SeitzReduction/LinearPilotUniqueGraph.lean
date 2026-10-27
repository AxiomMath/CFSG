module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphOrth
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeInner

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)

section Conj

variable {n : ℕ} {F : Type*} [Field F]

theorem card_fixedSubgroup_conjAut_mul (H : GL (Fin n) F) (β : MulAut (projectiveSL n F)) :
    Nat.card (fixedSubgroup (conjAut n F H * β * (conjAut n F H)⁻¹)) =
      Nat.card (fixedSubgroup β) := by
  rw [← mulAut_congr_eq_mul, card_fixedSubgroup_congr]

theorem card_perfectCore_fixedSubgroup_conjAut_mul [Finite F] (H : GL (Fin n) F)
    (β : MulAut (projectiveSL n F)) :
    Nat.card (perfectCore (fixedSubgroup (conjAut n F H * β * (conjAut n F H)⁻¹))) =
      Nat.card (perfectCore (fixedSubgroup β)) := by
  rw [← mulAut_congr_eq_mul, card_perfectCore_fixedSubgroup_congr]

end Conj

section Orders

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem card_fixedSubgroup_graph_eq {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e) (hn : 3 ≤ n)
    (A : GL (Fin n) F)
    (hθ : (conjAut n F A * dualAut n F) * (conjAut n F A * dualAut n F) = 1) :
    ∃ C : GL (Fin n) F,
      ((C : Matrix (Fin n) (Fin n) F) = 1 ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) = UnitaryHigher.blockSwapJ n r) ∧
      Nat.card (fixedSubgroup (conjAut n F A * dualAut n F)) =
        Nat.card (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) F)) ∧
      Nat.card (perfectCore (fixedSubgroup (conjAut n F A * dualAut n F))) =
        Nat.card (perfectCore (fixedSubgroup (conjAut n F C * dualAut n F))) := by
  obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms he hF hn A (by rw [sq]; exact hθ)
  have hC' : (C : Matrix (Fin n) (Fin n) F) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) = UnitaryHigher.blockSwapJ n r := by
    rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, hJ⟩
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv he hF hn C
    hC'
  refine ⟨C, hC', ?_, ?_⟩
  · rw [hconj, card_fixedSubgroup_conjAut_mul]
    exact Nat.card_congr E.toEquiv
  · rw [hconj, card_perfectCore_fixedSubgroup_conjAut_mul]

end Orders

section Arith

open CFSG.Assembly.LowTwoRank (StatedSp)

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem not_card_statedSp_dvd_two_mul_card_mulAut (hn : 3 ≤ n) {f r : ℕ} (hf : 1 ≤ f)
    (hr : 1 ≤ r) (hnr : n < 4 * r) (hK : Nat.card K = 2 ^ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * f)) :
    ¬ Nat.card (StatedSp r F) ∣ 2 * Nat.card (MulAut (projectiveSL n K)) := by
  intro h
  have hk2 : 2 ≤ 2 * (2 * f) * r := by nlinarith
  have hk6 : 2 * (2 * f) * r ≠ 6 := by
    intro h6
    have : 4 * (f * r) = 6 := by rw [← h6]; ring
    omega
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
  have hpS := ppd_dvd_card_statedSp hF hr hp.dvd
  have hfn : f * n < 2 * (2 * f) * r := by nlinarith
  exact not_dvd_two_mul_card_mulAut_of_ppd hn hf hK hp hfn (hpS.trans h)

theorem not_two_pow_dvd_two_mul_card_mulAut (hn : 3 ≤ n) {f r : ℕ} (hf : 1 ≤ f) (hr : n = 2 * r)
    (hfr : 2 ≤ f ∨ 3 ≤ r) (hK : Nat.card K = 2 ^ f) :
    ¬ 2 ^ (2 * f * r ^ 2) ∣ 2 * Nat.card (MulAut (projectiveSL n K)) := by
  intro h
  have h0 : 2 * Nat.card (MulAut (projectiveSL n K)) ≠ 0 :=
    mul_ne_zero two_ne_zero Nat.card_pos.ne'
  have hv := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).1 h
  rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at hv
  have hA := factorization_card_mulAut_projectiveSL_le (K := K) hn hf hK
  have hN : n * (n - 1) / 2 = r * (2 * r - 1) := by
    rw [hr, show 2 * r * (2 * r - 1) = 2 * (r * (2 * r - 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [hN] at hA
  have hr2 : 2 ≤ r := by omega
  have hsplit : f * (r * (2 * r - 1)) + f * r = 2 * f * r ^ 2 := by
    have h2r : 2 * r - 1 + 1 = 2 * r := by omega
    calc f * (r * (2 * r - 1)) + f * r = f * (r * (2 * r - 1 + 1)) := by ring
      _ = 2 * f * r ^ 2 := by rw [h2r]; ring
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hB : f * r ≤ 2 + f.factorization 2 := by omega
  rcases hfr with hf2 | hr3
  · have : f * 2 ≤ f * r := Nat.mul_le_mul_left f hr2
    omega
  · have : f * 3 ≤ f * r := Nat.mul_le_mul_left f hr3
    omega

end Arith

theorem not_card_fixedSubgroup_graph_dvd {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n)
    (h4 : n ≠ 4 ∨ 2 ≤ f) {K F : Type} [Field K] [Finite K] [Field F] [Finite F]
    (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = 2 ^ (2 * f)) (A : GL (Fin n) F)
    (hθ : (conjAut n F A * dualAut n F) * (conjAut n F A * dualAut n F) = 1) :
    ¬ Nat.card (fixedSubgroup (conjAut n F A * dualAut n F)) ∣
      2 * Nat.card (MulAut (projectiveSL n K)) := by
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  obtain ⟨C, hC, hcard, -⟩ := card_fixedSubgroup_graph_eq (by omega : 1 ≤ 2 * f) hF hn A hθ
  rw [hcard]
  rcases hC with hC1 | ⟨r, hr, hJ⟩
  · rw [hC1]
    obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
    ·
      intro h
      have hfr : 2 ≤ f ∨ 3 ≤ r := by omega
      refine not_two_pow_dvd_two_mul_card_mulAut (K := K) hn hf hr hfr hK ?_
      refine dvd_trans ?_ ((pow_dvd_card_matrixIsometryGroup_one (F := F) hr (by omega)).trans h)
      exact dvd_of_eq (by rw [hF, ← pow_mul])
    ·
      rw [card_matrixIsometryGroup_one_of_odd hr]
      exact not_card_statedSp_dvd_two_mul_card_mulAut hn hf (by omega) (by omega) hK hF
  · rw [hJ, card_matrixIsometryGroup_blockSwapJ hr]
    exact not_card_statedSp_dvd_two_mul_card_mulAut hn hf (by omega) (by omega) hK hF

theorem graphInvolutionExclusion_of_ne_four {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) (h4 : n ≠ 4 ∨ 2 ≤ f)
    {K F : Type} [Field K] [Finite K] [Field F] (hK : Nat.card K = 2 ^ f)
    (hF : Nat.card F = 2 ^ (2 * f)) : GraphInvolutionExclusion n K F := by
  have : Finite F := finite_of_card_eq_two_pow hF
  intro A hθ h1
  exact absurd h1 (not_card_fixedSubgroup_graph_dvd hf hn h4 hK hF A hθ)

end CFSG.SeitzReduction.LinearPilot
