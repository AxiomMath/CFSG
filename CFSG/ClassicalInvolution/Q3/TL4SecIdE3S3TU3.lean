module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TB
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.ClassicalInvolution.Q3.TL4MF163L2
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Ck
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3F
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix QuaternionGroup
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TA3.Q5U3 CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open scoped MatrixGroups

namespace E3S3T

variable {K : Type} [Field K]

theorem diag_sq_eq' {x : K} (hx : x ≠ 0) :
    (!![x, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![x, 0; 0, 1] =
      Matrix.scalar (Fin 2) x * !![x, 0; 0, x⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply, hx]

end E3S3T

theorem twKindU3_of (h33 : TwKindU33) : TwKindU3 := by
  intro X _ _ R S z hm hs h3 hi6 p f hp hp2 hL
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
    exact h33 X R S z hm hs h3 hi6 hL
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have hq3' : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a := by
    by_contra hcomm
    simp only [not_exists, ne_eq, not_not] at hcomm
    have hZ : Subgroup.center (genFittingFStar X) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hcomm y x
    have h1 : Nat.card (FStarQuot X) = 1 := by
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
      exact Subgroup.index_top
    have h2 := MFMuZ2.card_psu3_mul hp hf hK
    rw [← Nat.card_congr e₀.toEquiv, h1, one_mul] at h2
    have h4 : 4 ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
      have h5 : 27 ≤ (p ^ f) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3' 3
      have h6 : 1 ≤ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
        have : 9 ≤ (p ^ f) ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3' 2
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      calc 4 ≤ (p ^ f) ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    have h7 : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    omega
  set N := genFittingFStar X with hNdef
  have hNn : N.Normal := genFittingFStar_normal X
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by omega
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hD := hm.datum
  obtain ⟨ιq, hιq, hιqK, hιqz⟩ := MF163.exists_quat_of_member hm
  have hιqR : ∀ q, ιq q ∈ R := fun q => tightCore_le R (hιqK q)
  obtain ⟨q, hq2, hqN⟩ := E3S3T.exists_q8_mem_of_index_dvd_six hi6 ιq
  have hqq : q * q = a 2 := by
    have hQ : ∀ q : QuaternionGroup 2, q ^ 2 ≠ 1 → q * q = a 2 := by decide
    exact hQ q hq2
  have hc2 : ιq q * ιq q = z := by rw [← map_mul, hqq, hιqz]
  have hzN : z ∈ N := hc2 ▸ N.mul_mem hqN hqN
  obtain ⟨c₀, π, hrange, hk, -, -⟩ := exists_frame_formula h hp2 (eF.trans e₀) hzN hD.order
  have hcs := slCentScalar_GU2 h
  obtain ⟨eJ⟩ := nonempty_slPart_equiv h
  have hF₀card := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have hF₀ : Odd (Nat.card (LieType.Steinberg.fixedSubfield K p f)) := by
    rw [hF₀card]
    exact (h.prime.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (LieType.Steinberg.fixedSubfield K p f) := by rw [hF₀card]; omega
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hF₀ h4 eJ
  obtain ⟨A, hA, l, hl⟩ := MF163.exists_scalar_of_mem hD hrange hk hcs hF₀ h4 eJ (hιqR q) hqN
  obtain ⟨q', hq'N, hq'q'⟩ := MF163.exists_quat_not_mem hD hrange hk hcs hF₀ h4 eJ ιq hιq hιqR
    (hιqz ▸ hzN)
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
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hlu : h.bar (l : K) * l = 1 := by
    have hu := (Lemma41aU3.mem_GU2Stated_iff h).mp A.2
    rw [hl, GeneralLinearGroup.coe_scalar] at hu
    have h1 := congrFun (congrFun hu 0) 0
    simpa [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two] using h1
  have hdg : (!![(l : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]
  have hgU : GeneralLinearGroup.mkOfDetNeZero _ hdg ∈ GU2Stated (p ^ f) K := by
    rw [Lemma41aU3.mem_GU2Stated_iff h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, hlu]
  set Ag : ↥(GU2Stated (p ^ f) K) := ⟨_, hgU⟩ with hAg
  set Aj : ↥(GU2Stated (p ^ f) K) := ⟨_, dx_mem h hlu hl0⟩ with hAj
  have hAjJ : Aj ∈ slPart (GU2Stated (p ^ f) K) := by
    rw [mem_slPart]
    exact det_mk2 _ _ _ _ (dx_det hl0)
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
    exact E3S3T.diag_sq_eq' hl0
  exact E3S3T.twSwap_of_sq hD hm.cls.1 hc2 (hιqR q') hσc hgC hjσ hgg

end CFSG.ClassicalInvolution.Q3.TL4
