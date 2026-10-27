module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TB
public import CFSG.ClassicalInvolution.Q3.TL4E3C269Sec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix QuaternionGroup
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.Blueprint
open scoped MatrixGroups

namespace E3S3T

variable {K : Type} [Field K]

theorem diag_sq_eq (l : Kˣ) :
    (!![(l : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![(l : K), 0; 0, 1] =
      Matrix.scalar (Fin 2) (l : K) * !![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]

end E3S3T

theorem twKindL3_proved : TwKindL3 := by
  intro X _ _ R S z hm hs h3 hi6 p f hp hp2 hl
  by_cases hq3 : p ^ f = 3
  · exact absurd (E3C269.tightActs3_of_psl3_three hm hl hq3) h3
  obtain ⟨K, _, _, hK, ⟨e⟩, -⟩ := E3C269.exists_psl3_equiv hl
  set N := genFittingFStar X with hNdef
  have hNn : N.Normal := genFittingFStar_normal X
  have hD := hm.datum
  have hoddK : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact h
  have h5 : 5 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  have h4 : 4 ≤ Nat.card K := by omega
  obtain ⟨ιq, hιq, hιqK, hιqz⟩ := MF163.exists_quat_of_member hm
  have hιqR : ∀ q, ιq q ∈ R := fun q => tightCore_le R (hιqK q)
  obtain ⟨q, hq2, hqN⟩ := E3S3T.exists_q8_mem_of_index_dvd_six hi6 ιq
  have hqq : q * q = a 2 := by
    have hQ : ∀ q : QuaternionGroup 2, q ^ 2 ≠ 1 → q * q = a 2 := by decide
    exact hQ q hq2
  have hc2 : ιq q * ιq q = z := by rw [← map_mul, hqq, hιqz]
  have hzN : z ∈ N := hc2 ▸ N.mul_mem hqN hqN
  obtain ⟨Q, π, hrange, hk, -, -⟩ := exists_frame hoddK e hzN hD.order
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hoddK h4 slPartTopEquiv
  obtain ⟨A, hA, l, hl⟩ := MF163.exists_scalar_of_mem hD hrange hk slCentScalar_top hoddK h4
    slPartTopEquiv (hιqR q) hqN
  obtain ⟨q', hq'N, hq'q'⟩ := MF163.exists_quat_not_mem hD hrange hk slCentScalar_top hoddK h4
    slPartTopEquiv ιq hιq hιqR (hιqz ▸ hzN)
  have hq'4 : ιq q' ^ 4 = 1 := by
    have h4' : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by decide
    rw [← map_pow, h4', map_one]
  refine ⟨E3S3T.two_dvd_index_of_not_mem hq'4 hq'N, ?_⟩
  have hq'2 : q' ^ 2 ≠ 1 := by
    rw [pow_two, hq'q']
    decide
  have hne1 : q' ≠ q := fun h => hq'N (h ▸ hqN)
  have hne2 : q' ≠ q⁻¹ := fun h => hq'N (by rw [h, map_inv]; exact N.inv_mem hqN)
  have hσc : ιq q' * ιq q * (ιq q')⁻¹ = (ιq q)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, E3S3T.q8_conj_eq_inv q q' hq2 hne1 hne2 hq'2, map_inv]
  have hdg : (!![(l : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]
  have hdj : (!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]
  set Ag : (⊤ : Subgroup (GL (Fin 2) K)) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero _ hdg, Subgroup.mem_top _⟩ with hAg
  set Aj : (⊤ : Subgroup (GL (Fin 2) K)) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero _ hdj, Subgroup.mem_top _⟩ with hAj
  have hAjJ : Aj ∈ slPart (⊤ : Subgroup (GL (Fin 2) K)) := by
    rw [mem_slPart]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    simp [Aj, Matrix.det_fin_two_of]
  have hgC : π Ag ∈ Subgroup.centralizer ({z} : Set X) := by
    have h1 : π Ag ∈ π.range := ⟨Ag, rfl⟩
    rw [hrange] at h1
    exact h1.2
  have hjσ : π Aj * ιq q' = ιq q' * π Aj :=
    Subgroup.mem_centralizer_iff.mp (hRJ (hιqR q')) (π Aj) ⟨Aj, hAjJ, rfl⟩
  have hgg : π Ag * π Ag = ιq q * π Aj := by
    rw [← map_mul, ← hA, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hl,
      GeneralLinearGroup.coe_scalar]
    exact E3S3T.diag_sq_eq l
  exact E3S3T.twSwap_of_sq hD hm.cls.1 hc2 (hιqR q') hσc hgC hjσ hgg

end CFSG.ClassicalInvolution.Q3.TL4
