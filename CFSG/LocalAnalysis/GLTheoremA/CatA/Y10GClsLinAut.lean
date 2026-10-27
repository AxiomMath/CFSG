module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSL
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.StandardType.AutPSL CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem odd_order_aut_eq_conj_mul_field {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (hd : 3 ≤ d) {p : ℕ} (hp : Odd p) (α : MulAut (projectiveSL d K)) (hα : α ^ p = 1) :
    ∃ (A : GL (Fin d) K) (σ : K ≃+* K), α = conjAut d K A * fieldAut d K σ := by
  obtain ⟨i, hi, c, hc, rfl⟩ := exists_mul_compl hd α
  obtain ⟨σ, hσ⟩ := (mem_compl).1 hc
  rcases hσ with rfl | rfl
  · obtain ⟨A, rfl⟩ := hi
    exact ⟨A, σ, rfl⟩
  · exfalso
    haveI : (inndiag : Subgroup (MulAut (projectiveSL d K))).Normal := inndiag_normal hd
    have hcpI : (fieldAut d K σ * graphAut) ^ p ∈
        (inndiag : Subgroup (MulAut (projectiveSL d K))) := by
      have h1 : QuotientGroup.mk' (inndiag : Subgroup (MulAut (projectiveSL d K)))
          (fieldAut d K σ * graphAut) = QuotientGroup.mk' _ (i * (fieldAut d K σ * graphAut)) := by
        have hi1 : QuotientGroup.mk' (inndiag : Subgroup (MulAut (projectiveSL d K))) i = 1 :=
          (QuotientGroup.eq_one_iff i).2 hi
        simp only [map_mul, hi1, one_mul]
      have h2 : QuotientGroup.mk' (inndiag : Subgroup (MulAut (projectiveSL d K)))
          ((fieldAut d K σ * graphAut) ^ p) = 1 := by
        rw [map_pow, h1, ← map_pow, hα, map_one]
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hcpC : (fieldAut d K σ * graphAut) ^ p ∈ (compl : Subgroup (MulAut (projectiveSL d K))) :=
      pow_mem hc p
    have hbot : (fieldAut d K σ * graphAut) ^ p ∈
        (inndiag : Subgroup (MulAut (projectiveSL d K))) ⊓ compl := ⟨hcpI, hcpC⟩
    rw [inndiag_inf_compl hd, Subgroup.mem_bot] at hbot
    have hcomm : Commute (fieldAut d K σ) (graphAut (n := d) (K := K)) :=
      fieldAut_mul_graphAut σ
    have hgp : (graphAut (n := d) (K := K)) ^ p = graphAut (n := d) (K := K) := by
      obtain ⟨k, rfl⟩ := hp
      rw [pow_succ, pow_mul, show (graphAut (n := d) (K := K)) ^ 2 = 1 by
        rw [pow_two]; exact graphAut_mul_self, one_pow, one_mul]
    have hpow : (fieldAut d K σ * graphAut) ^ p = fieldAut d K (σ ^ p) * graphAut := by
      rw [hcomm.mul_pow, hgp, ← map_pow]
    rw [hpow, mul_eq_one_iff_eq_inv] at hbot
    have hγ : graphAut (n := d) (K := K) = (fieldAut d K (σ ^ p))⁻¹ := by
      rw [hbot, inv_inv]
    have hδ : dualAut d K = (conjAut d K (Matrix.SpecialLinearGroup.toGL
        (revSL (n := d) (K := K))))⁻¹ * (fieldAut d K (σ ^ p))⁻¹ := by
      have hG : graphAut (n := d) (K := K) = conjAut d K (Matrix.SpecialLinearGroup.toGL
          (revSL (n := d) (K := K))) * dualAut d K := rfl
      rw [← hγ, hG, ← mul_assoc, inv_mul_cancel, one_mul]
    have hlin : conjAut d K (Matrix.SpecialLinearGroup.toGL (revSL (n := d) (K := K))) ∈
        semilinearAutGroup d K :=
      linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)
    have hfld : fieldAut d K (σ ^ p) ∈ semilinearAutGroup d K :=
      fieldAut_mem_semilinearAutGroup _
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) hd
    rw [hδ]
    exact mul_mem (inv_mem hlin) (inv_mem hfld)

theorem aut_eq_conj_mul_field_two {K : Type} [Field K] [Finite K] (α : MulAut (projectiveSL 2 K)) :
    ∃ (A : GL (Fin 2) K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ :=
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_conjAut_fieldAut_two α

theorem odd_order_aut_eq_conj_mul_field' {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (hd : 2 ≤ d) {p : ℕ} (hp : Odd p) (α : MulAut (projectiveSL d K)) (hα : α ^ p = 1) :
    ∃ (A : GL (Fin d) K) (σ : K ≃+* K), α = conjAut d K A * fieldAut d K σ := by
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl : d = 2 := by omega
    obtain ⟨A, σ, hA⟩ := aut_eq_conj_mul_field_two (K := K) α
    exact ⟨A, σ, hA⟩
  · exact odd_order_aut_eq_conj_mul_field h hp α hα

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
