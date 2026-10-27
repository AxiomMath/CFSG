module

public import CFSG.ClassicalInvolution.Phan.PhanS11Adj
public import CFSG.ClassicalInvolution.Phan.PhanS9O5Span

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3

section Span

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem emb_span_decomp (s a b z : F) :
    emb (K := K) (mk7 s a b s (-a) (-b) z : W7 F) =
      emb (K := K) (mk7 s 0 0 s 0 0 z : W7 F) +
        algebraMap F K a • emb (K := K) (mk7 0 1 0 0 (-1) 0 0 : W7 F) +
          algebraMap F K b • emb (K := K) (mk7 0 0 1 0 0 (-1) 0 : W7 F) := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7, Algebra.algebraMap_eq_smul_one]
  · fin_cases i <;> simp [emb, mk7, Algebra.algebraMap_eq_smul_one]
  · simp [emb, mk7, Algebra.algebraMap_eq_smul_one]

theorem polar_perp_pPrime (h2 : (2 : K) ≠ 0) {y : W7 K}
    (h1 : polar (quadOdd 3 K) y (vE2 D) = 0) (h3 : hrm D y (vE2 D) = 0) :
    polar (quadOdd 3 K) y (emb (K := K) (mk7 0 1 0 0 (-1) 0 0 : W7 F)) = 0 ∧
      polar (quadOdd 3 K) y (emb (K := K) (mk7 0 0 1 0 0 (-1) 0 : W7 F)) = 0 := by
  have h2θ : (2 * D.θ : K) ≠ 0 := mul_ne_zero h2 (theta_ne_zero D)
  have h6 : polar (quadOdd 3 K) y (conjV D (vE2 D)) = 0 := h3
  constructor
  · have h5 := congrArg (polar (quadOdd 3 K) y) (two_smul_emb_c (F := F) D)
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_add_right, h1, h6] at h5
    have : (2 : K) * polar (quadOdd 3 K) y (emb (K := K) (mk7 0 1 0 0 (-1) 0 0 : W7 F)) = 0 := by
      simpa [smul_eq_mul] using h5
    exact (mul_eq_zero.mp this).resolve_left h2
  · have h5 := congrArg (polar (quadOdd 3 K) y) (two_theta_smul_emb_d (F := F) D)
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_sub_right, h1, h6] at h5
    have : (2 * D.θ : K) * polar (quadOdd 3 K) y
        (emb (K := K) (mk7 0 0 1 0 0 (-1) 0 : W7 F)) = 0 := by
      simpa [smul_eq_mul] using h5
    exact (mul_eq_zero.mp this).resolve_left h2θ

theorem polar_perp_fr0_span (h2K : (2 : K) ≠ 0) {h2F : (2 : F) ≠ 0} {y : W7 K}
    (h1 : polar (quadOdd 3 K) y (vXi D) = 0) (h2 : hrm D y (vXi D) = 0)
    (h3 : polar (quadOdd 3 K) y (vE2 D) = 0) (h4 : hrm D y (vE2 D) = 0) :
    ∀ r ∈ (fr0 h2F).span, polar (quadOdd 3 K) y (emb r) = 0 := by
  intro r hr
  obtain ⟨s, a, b, z, rfl⟩ := mem_span_fr0 h2F hr
  have hP := polar_perp_plSpan D h2K h1 h2 (mk7 s 0 0 s 0 0 z) ⟨(s, z), rfl⟩
  obtain ⟨hc, hd⟩ := polar_perp_pPrime (F := F) D h2K h3 h4
  rw [emb_span_decomp, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hP, hc, hd]
  simp

theorem actK_fix_of_fixSpan {h2F : (2 : F) ≠ 0} {g : spinGroup (quadOdd 3 F)}
    (hg : ∀ x ∈ (fr0 h2F).span, spinAction (quadOdd 3 F) g x = x) :
    actK g (vXi D) = vXi D ∧ actK g (vE2 D) = vE2 D := by
  have hm := fun s a b z => hg _ (fr0_span_mk7_mem h2F s a b z)
  refine ⟨actK_vXi_of_fix D g ?_ ?_, actK_vE2_of_fix D g ?_ ?_⟩
  · simpa using hm 1 0 0 0
  · simpa using hm 0 0 0 1
  · simpa using hm 0 1 0 0
  · simpa using hm 0 0 1 0

end Span

section Moves

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

variable (S : Setup M E D)

include S

theorem Setup.exists_two_moves {y z : W7 (GaloisField p (2 * f))} (hy : IsFF7 D y)
    (hz : IsFF7 D z) (hyξ : polar (quadOdd 3 (GaloisField p (2 * f))) y (vXi D) = 0)
    (hyξ' : hrm D y (vXi D) = 0) (hzξ : polar (quadOdd 3 (GaloisField p (2 * f))) z (vXi D) = 0)
    (hzξ' : hrm D z (vXi D) = 0) (hzy : polar (quadOdd 3 (GaloisField p (2 * f))) z y = 0)
    (hzy' : hrm D z y = 0) :
    ∃ w : spinGroup (quadOdd 3 (GaloisField p f)), ∃ c₁ c₂ : GaloisField p (2 * f),
      c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ actK w (vXi D) = vXi D ∧ actK w y = c₁ • vE2 D ∧
        actK w z = c₂ • vE3 D := by
  obtain ⟨w₁, hw₁P, c₁, hc₁, hw₁⟩ := S.exists_move_perpP hy (polar_perp_plSpan D S.h2K hyξ hyξ')
  have hw₁ξ : actK w₁ (vXi D) = vXi D :=
    actK_vXi_of_fixP D (fun s z => hw₁P (mk7 s 0 0 s 0 0 z) ⟨(s, z), rfl⟩)
  have hvE2 : vE2 D = c₁⁻¹ • actK w₁ y := by
    rw [hw₁, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
  have hz₄ : IsFF7 D (actK w₁ z) := isFF7_actK D S.h2K w₁ hz
  have h5 : polar (quadOdd 3 (GaloisField p (2 * f))) (actK w₁ z) (vXi D) = 0 := by
    have := polar_actK (K := GaloisField p (2 * f)) w₁ z (vXi D)
    rw [hw₁ξ] at this
    rw [this]
    exact hzξ
  have h6 : hrm D (actK w₁ z) (vXi D) = 0 := by
    have := hrm_actK D w₁ z (vXi D)
    rw [hw₁ξ] at this
    rw [this]
    exact hzξ'
  have h7 : polar (quadOdd 3 (GaloisField p (2 * f))) (actK w₁ z) (vE2 D) = 0 := by
    rw [hvE2, QuadraticMap.polar_smul_right, polar_actK, hzy]
    simp
  have h8 : hrm D (actK w₁ z) (vE2 D) = 0 := by
    rw [hvE2, hrm_smul_right, hrm_actK, hzy']
    simp
  have hzR := polar_perp_fr0_span (F := GaloisField p f) D S.h2K (h2F := h2) h5 h6 h7 h8
  have hE3R := polar_perp_fr0_span (F := GaloisField p f) D S.h2K (h2F := h2)
    (y := vE3 D) (by rw [QuadraticMap.polar_comm]; exact polar_vXi_vE3 D) (hrm_vE3_vXi D)
    (by rw [QuadraticMap.polar_comm]; exact polar_vE2_vE3 D) (hrm_vE3_vE2 D)
  obtain ⟨w₂, hw₂R, c₂, hc₂, hw₂⟩ := S.witt.move S.hodd S.h2K S.hn1 (R := (fr0 h2).span)
    (fr0_span_regular h2) (by rw [finrank_fr0_span h2]) hz₄ (isFF7_vE3 D S.h2K) hzR hE3R
  obtain ⟨hw₂ξ, hw₂ε⟩ := actK_fix_of_fixSpan D hw₂R
  refine ⟨w₂ * w₁, c₁, c₂, hc₁, hc₂, ?_, ?_, ?_⟩
  · rw [actK_mul, hw₁ξ, hw₂ξ]
  · rw [actK_mul, hw₁, map_smul, hw₂ε]
  · rw [actK_mul, hw₂]

end Moves

end CFSG.ClassicalInvolution.PhanB3.S
