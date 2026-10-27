module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6ClsD

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4

namespace Cat7E6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem frame_of_conj {T g B : StatedSp 2 K} (h : g⁻¹ * T * g = B) :
    mat (spG T) * smat g = smat g * smat B := by
  have e : T * g = g * B := by rw [← h]; group
  exact congrArg smat e

theorem mul_ne_of_anticomm (h2 : (2 : K) ≠ 0) {d : K} (hd0 : d ≠ 0)
    {A Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hAA : A * A = d • 1) (hYY : Y * Y = -1)
    (hYA : Y * A = -(A * Y)) : Y * A ≠ A * Y := by
  intro h
  have h0 : A * Y = -(A * Y) := h.symm.trans hYA
  have h1 : A * Y = 0 := by
    have h3 : (2 : K) • (A * Y) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h0]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h3).resolve_left h2
  have h3 : A = 0 := by
    have h4 : A * (Y * Y) = 0 := by rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
    rw [hYY, Matrix.mul_neg, Matrix.mul_one, neg_eq_zero] at h4
    exact h4
  rw [h3, Matrix.zero_mul] at hAA
  have h4 := congrFun (congrFun hAA (Sum.inl 0)) (Sum.inl 0)
  simp at h4
  exact hd0 h4.symm

theorem cls_model [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (c : Cat8.QConf (StatedProj (StatedSp 2 K)) (p ^ f))
    {w : MulAut (StatedProj (StatedSp 2 K))} (hw : w ∈ Cat8.innA _ c.a) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) :
    ∃ n ∈ Cat8.innA (StatedProj (StatedSp 2 K)) c.a, n⁻¹ * w * n = c.a ∨ n⁻¹ * w * n = c.z ∨
      n⁻¹ * w * n = c.a * c.z * c.tau ∨ n⁻¹ * w * n = c.z * c.tau := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨A, hA, d, hd0, hdsq, hAA, hμ⟩ := admissible_data hp hp2 hf hK c.adm
  obtain ⟨Y, Z, hY, hZ, hYY, hZZ, hYA, hZA, hZY⟩ := exists_YZ hp hp2 hf hK c hA hd0 hdsq hAA hμ
  rw [innA_eq_range hp hp2 hf hK c.adm] at hw ⊢
  obtain ⟨X, rfl⟩ := hw
  have hk : conjAut 2 K (X * X) = 1 := by rw [map_mul]; exact hw2
  rw [conjAut_eq_one_iff] at hk
  obtain ⟨l, hl⟩ := hk
  have hXX : mat X * mat X = (l : K) • 1 := by
    have h := Units.ext_iff.mp hl
    change mat (X * X) = _ at h
    rw [mat_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at h
    exact h
  obtain ⟨μ, hXμ⟩ := mem_gsp.mp X.2
  have hXμ' : (mat X)ᵀ * formJ 2 K * mat X = (μ : K) • formJ 2 K := hXμ
  have hlμ : (l : K) = μ ∨ (l : K) = -μ := by
    have e1 : (mat X * mat X)ᵀ * formJ 2 K * (mat X * mat X) = ((μ : K) * μ) • formJ 2 K := by
      calc (mat X * mat X)ᵀ * formJ 2 K * (mat X * mat X) =
          (mat X)ᵀ * ((mat X)ᵀ * formJ 2 K * mat X) * mat X := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = ((μ : K) * μ) • formJ 2 K := by
            rw [hXμ', Matrix.mul_smul, Matrix.smul_mul, hXμ', smul_smul]
    rw [hXX, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at e1
    have e2 := smul_formJ_injective 2 e1
    have e3 : ((l : K) - μ) * ((l : K) + μ) = 0 := by linear_combination e2
    rcases mul_eq_zero.mp e3 with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  by_cases hsq : ∃ s : K, s ^ 2 = μ
  ·
    obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hs
      exact μ.ne_zero hs.symm
    have hT : (s⁻¹ • mat X)ᵀ * formJ 2 K * (s⁻¹ • mat X) = formJ 2 K := by
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hXμ', smul_smul,
        smul_smul, ← hs, show s⁻¹ * s⁻¹ * s ^ 2 = 1 by field_simp, one_smul]
    set T := toSp (s⁻¹ • mat X) hT
    have hsT : smat T = s⁻¹ • mat X := coe_toSp _ _
    have hwT : conjAut 2 K X = conjAut 2 K (spG T) :=
      conjAut_eq_of_smul _ _ (c := s) (by
        change mat X = s • smat T
        rw [hsT, smul_smul, mul_inv_cancel₀ hs0, one_smul])
    have hTT : smat T * smat T = (s⁻¹ * s⁻¹ * l) • 1 := by
      rw [hsT, Matrix.smul_mul, Matrix.mul_smul, hXX, smul_smul, smul_smul]
    have hT1 : smat T ≠ 1 := by
      intro h
      apply hw1
      rw [hwT]
      exact conjAut_eq_one_of_smul _ (c := 1) (by rw [one_smul]; exact h)
    have hTm : smat T ≠ -1 := by
      intro h
      apply hw1
      rw [hwT]
      exact conjAut_eq_one_of_smul _ (c := -1) (by rw [neg_one_smul]; exact h)
    rcases hlμ with hl' | hl'
    ·
      have hTT' : smat T * smat T = 1 := by
        rw [hTT, hl', ← hs, show s⁻¹ * s⁻¹ * s ^ 2 = 1 by field_simp, one_smul]
      obtain ⟨g, hg⟩ := exists_conj_T1 h2 T hTT' hT1 hTm
      have hsU : smat (Z * Y) = smat Z * smat Y := rfl
      have hUU : smat (Z * Y) * smat (Z * Y) = 1 := by
        rw [hsU]
        calc smat Z * smat Y * (smat Z * smat Y) = smat Z * (smat Y * smat Z) * smat Y := by
              simp only [Matrix.mul_assoc]
          _ = smat Z * (smat Z * smat Y) * smat Y := by rw [hZY]
          _ = (smat Z * smat Z) * (smat Y * smat Y) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hZZ, hYY, Matrix.neg_mul, Matrix.one_mul, neg_neg]
      have hU1 : smat (Z * Y) ≠ 1 := by
        intro h
        rw [hsU] at h
        have hZm : smat Z = -smat Y := by
          calc smat Z = -(smat Z * (smat Y * smat Y)) := by
                rw [hYY, Matrix.mul_neg, Matrix.mul_one, neg_neg]
            _ = -smat Y := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
        apply mul_ne_of_anticomm h2 hd0 hAA hYY hYA
        have h3 := hZA
        rw [hZm, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at h3
        exact h3
      have hUm : smat (Z * Y) ≠ -1 := by
        intro h
        rw [hsU] at h
        have hZm : smat Z = smat Y := by
          calc smat Z = -(smat Z * (smat Y * smat Y)) := by
                rw [hYY, Matrix.mul_neg, Matrix.mul_one, neg_neg]
            _ = smat Y := by rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.one_mul, neg_neg]
        apply mul_ne_of_anticomm h2 hd0 hAA hYY hYA
        rw [← hZm]
        exact hZA
      obtain ⟨g', hg'⟩ := exists_conj_T1 h2 (Z * Y) hUU hU1 hUm
      obtain ⟨n, hn, hconj⟩ := exists_conj_of_frames (frame_of_conj hg) (frame_of_conj hg')
      refine ⟨n, hn, Or.inr (Or.inr (Or.inr ?_))⟩
      rw [hwT, hconj, hZ, hY, ← map_mul, spG_mul]
    ·
      have hTT' : smat T * smat T = -1 := by
        rw [hTT, hl', ← hs, show s⁻¹ * s⁻¹ * -s ^ 2 = -1 by field_simp, neg_one_smul]
      obtain ⟨g, hg⟩ := exists_conj_T2 h2 T hTT'
      obtain ⟨g', hg'⟩ := exists_conj_T2 h2 Z hZZ
      obtain ⟨n, hn, hconj⟩ := exists_conj_of_frames (frame_of_conj hg) (frame_of_conj hg')
      refine ⟨n, hn, Or.inr (Or.inl ?_)⟩
      rw [hwT, hconj, hZ]
  ·
    have hμsq : ∀ s : K, s ^ 2 ≠ μ := fun s h => hsq ⟨s, h⟩
    obtain ⟨s, hs0, hs⟩ := exists_sq_mul_eq (μ := (μ : K)) μ.ne_zero hd0 hμsq hdsq
    set X' := gspOf (s • mat X) (Units.mk0 (s ^ 2) (pow_ne_zero 2 hs0) * μ) (by
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hXμ', smul_smul,
        smul_smul, Units.val_mul, Units.val_mk0]
      ring_nf)
    have hwX : conjAut 2 K X' = conjAut 2 K X := conjAut_smul X hs0 hXμ'
    have hmX' : mat X' = s • mat X := coe_gspOf _ _ _
    have hX'μ : (mat X')ᵀ * formJ 2 K * mat X' = d • formJ 2 K := by
      rw [hmX', transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hXμ',
        smul_smul, smul_smul, ← hs, sq]
    rcases hlμ with hl' | hl'
    ·
      have hX'X' : mat X' * mat X' = d • 1 := by
        rw [hmX', Matrix.smul_mul, Matrix.mul_smul, hXX, smul_smul, smul_smul, hl', ← hs, sq]
      obtain ⟨g, hg⟩ := exists_frame_typeII h2 hd0 hdsq hX'μ hX'X'
      obtain ⟨g', hg'⟩ := exists_frame_typeII h2 hd0 hdsq hμ hAA
      obtain ⟨n, hn, hconj⟩ := exists_conj_of_frames hg hg'
      refine ⟨n, hn, Or.inl ?_⟩
      rw [← hwX, hconj, hA]
    ·
      have hX'X' : mat X' * mat X' = (-d) • 1 := by
        rw [hmX', Matrix.smul_mul, Matrix.mul_smul, hXX, smul_smul, smul_smul, hl', ← hs, sq]
        congr 1
        ring
      have hMM : mat (A * spG Z * spG Y) * mat (A * spG Z * spG Y) = (-d) • 1 := by
        change mat A * smat Z * smat Y * (mat A * smat Z * smat Y) = (-d) • 1
        calc mat A * smat Z * smat Y * (mat A * smat Z * smat Y)
            = mat A * smat Z * (smat Y * mat A) * (smat Z * smat Y) := by
              simp only [Matrix.mul_assoc]
          _ = -(mat A * (smat Z * mat A) * (smat Y * smat Z) * smat Y) := by
              rw [hYA]
              simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
          _ = -(mat A * (mat A * smat Z) * (smat Z * smat Y) * smat Y) := by rw [hZA, hZY]
          _ = -((mat A * mat A) * (smat Z * smat Z) * (smat Y * smat Y)) := by
              simp only [Matrix.mul_assoc]
          _ = (-d) • 1 := by
              rw [hAA, hZZ, hYY]
              simp only [Matrix.mul_neg, Matrix.mul_one, neg_neg, neg_smul]
      have hMμ : (mat (A * spG Z * spG Y))ᵀ * formJ 2 K * mat (A * spG Z * spG Y) =
          d • formJ 2 K := by
        change (mat A * smat Z * smat Y)ᵀ * formJ 2 K * (mat A * smat Z * smat Y) =
          d • formJ 2 K
        calc (mat A * smat Z * smat Y)ᵀ * formJ 2 K * (mat A * smat Z * smat Y)
            = (smat Y)ᵀ * ((smat Z)ᵀ * ((mat A)ᵀ * formJ 2 K * mat A) * smat Z) * smat Y := by
              simp only [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = d • formJ 2 K := by
              rw [hμ, Matrix.mul_smul, Matrix.smul_mul, symplectic_of_mem Z, Matrix.mul_smul,
                Matrix.smul_mul, symplectic_of_mem Y]
      have hd' : -d ≠ 0 := neg_ne_zero.mpr hd0
      obtain ⟨g, hg⟩ := exists_frame_typeI h2 hd' (by rw [neg_neg]; exact hX'μ) hX'X'
      obtain ⟨g', hg'⟩ := exists_frame_typeI h2 hd' (by rw [neg_neg]; exact hMμ) hMM
      obtain ⟨n, hn, hconj⟩ := exists_conj_of_frames hg hg'
      refine ⟨n, hn, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [← hwX, hconj, map_mul, map_mul, hA, hZ, hY]

end Cat7E6

open Cat7E6 in
theorem cf81E6ClsPSp : CF81E6ClsPSp := by
  intro K₀ _ _ p f hp hp2 hf _ hL c w hw hw2 hw1
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hL
  have hw' : MulAut.congr e w ∈ Cat8.innA _ (qConfCongr e c).a := by
    rw [qConfCongr_a, ← map_innA]
    exact ⟨w, hw, rfl⟩
  obtain ⟨n', hn', h⟩ := cls_model hp hp2 hf hK (qConfCongr e c) hw'
    (by rw [← map_mul, hw2, map_one])
    (fun h => hw1 ((MulAut.congr e).injective (by rw [h, map_one])))
  have key : ∀ t : MulAut K₀, n'⁻¹ * MulAut.congr e w * n' = MulAut.congr e t →
      ((MulAut.congr e).symm n')⁻¹ * w * (MulAut.congr e).symm n' = t := by
    intro t ht
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ht]
  refine ⟨(MulAut.congr e).symm n', ?_, ?_⟩
  · rw [qConfCongr_a, ← map_innA] at hn'
    obtain ⟨n, hn, rfl⟩ := hn'
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hn
  · rw [qConfCongr_a, qConfCongr_z, qConfCongr_tau] at h
    rcases h with h | h | h | h
    · exact Or.inl (key _ h)
    · exact Or.inr (Or.inl (key _ h))
    · refine Or.inr (Or.inr (Or.inl (key (c.a * c.z * c.tau) ?_)))
      rw [h, map_mul (MulAut.congr e) (c.a * c.z) c.tau, map_mul (MulAut.congr e) c.a c.z]
    · refine Or.inr (Or.inr (Or.inr (key (c.z * c.tau) ?_)))
      rw [h, map_mul (MulAut.congr e) c.z c.tau]

end CFSG.ComponentClassification.GSThmB
