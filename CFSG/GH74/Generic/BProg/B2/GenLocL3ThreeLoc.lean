module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3ThreeShape
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial Matrix GenLocL3Pair GenLocL3Good
open scoped MatrixGroups

namespace GenLocL3Three

theorem fixed_VV {k m : Fin 3} (hkm : k ≠ m) {x : P3} (hxk : cT k x = x) (hxm : cT m x = x) :
    x ^ 4 = 1 := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K3 x
  have hc := (conjAut_fixed_iff (diag3 (tauU k)) g).1 hxk
  have hc' := (conjAut_fixed_iff (diag3 (tauU m)) g).1 hxm
  rw [coe_diag3] at hc hc'
  have hdiag := isDiag_of_comm2 hkm (g : Matrix (Fin 3) (Fin 3) K3) hc hc'
  have hdet : (g : Matrix (Fin 3) (Fin 3) K3).det ≠ 0 := by
    rw [g.2]; exact one_ne_zero
  have h2 := diag_sq _ hdiag hdet
  refine pow_of_matrix ?_
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, one_pow]

theorem fixed_VW (k : Fin 3) (u : Fin 3 → K3ˣ) {x : P3} (hxk : cT k x = x) (hxu : (cU u * dl) x = x) :
    x ^ 4 = 1 := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K3 x
  have hc := (conjAut_fixed_iff (diag3 (tauU k)) g).1 hxk
  have hd := (conjAut_dual_fixed_iff (diag3 u) g).1 hxu
  rw [coe_diag3] at hc hd
  exact pow_of_matrix (block_pow4 k (fun i => (u i : K3)) (fun i => (u i).ne_zero) _ hc hd)

theorem pair_pow4 (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (s t : D) (hs : s ≠ 1) (ht : t ≠ 1) (hst : s ≠ t) {x : P3}
    (hxs : (s : MulAut P3) x = x) (hxt : (t : MulAut P3) x = x) : x ^ 4 = 1 := by
  obtain ⟨a, b, -, -, -, hfix, hshape⟩ := pair_shape D hfs hD s t hs ht hst
  obtain ⟨hxa, hxb⟩ := hfix x hxs hxt
  rcases hshape with ⟨k, m, hkm, hak, hbm⟩ | ⟨k, u, hak, hbu⟩
  · rw [hak] at hxa
    rw [hbm] at hxb
    exact fixed_VV hkm hxa hxb
  · rw [hak] at hxa
    rw [hbu] at hxb
    exact fixed_VW k u hxa hxb

theorem locE1_three (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3)
    (hA : IsRank23 ↥D) (h8 : Nat.card ↥D = 8) : LocE1 D.subtype := by
  intro E hE
  refine noOddNormal_of_isPGroup ?_
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hrk : pRank 2 ↥D = 3 := by
    have h1 := GenLocBasic.card_eq_two_pow_pRank_type hA.1
    have h2 : 2 ^ pRank 2 ↥D = 2 ^ 3 := by rw [← h1, h8]; norm_num
    exact Nat.pow_right_injective le_rfl h2
  have hEA := GenLocBasic.isEA_subgroup hA.1 E
  have hEcard := GenLocBasic.card_eq_two_pow_pRank_type hEA
  have h4 : 2 < Nat.card ↥E := by
    rw [hEcard]
    have h2 : 2 ≤ pRank 2 ↥E := by omega
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨t, ht, s, hs, ht1, hs1, hts⟩ := GenLocBasic.exists_two_ne_one h4
  have hpow : ∀ x ∈ fixedIn P3 (E.map D.subtype), x ^ 4 = 1 := by
    intro x hx
    rw [mem_fixedIn] at hx
    exact pair_pow4 D hfs hA.1 t s ht1 hs1 hts (hx _ ⟨t, ht, rfl⟩) (hx _ ⟨s, hs, rfl⟩)
  intro x
  exact ⟨2, Subtype.ext (by simpa using hpow x x.2)⟩

@[expose] def dSL (a b c : K3) (h : a * b * c = 1) : SL(3, K3) :=
  ⟨Matrix.diagonal ![a, b, c], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h⟩

theorem coe_dSL (a b c : K3) (h : a * b * c = 1) :
    ((dSL a b c h : SL(3, K3)) : Matrix (Fin 3) (Fin 3) K3) = Matrix.diagonal ![a, b, c] := rfl

theorem diag_sandwich (d : Fin 3 → K3) (A : Matrix (Fin 3) (Fin 3) K3) (i l : Fin 3) :
    (Matrix.diagonal d * A * (Matrix.diagonal d).transpose) i l = d i * A i l * d l := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_transpose]

theorem fixed_dSL_of_diag (u : Fin 3 → K3ˣ) (a b c : K3) (h : a * b * c = 1) :
    cU u (LinearFlag.proj 3 K3 (dSL a b c h)) = LinearFlag.proj 3 K3 (dSL a b c h) := by
  unfold cU
  rw [conjAut_fixed_iff, coe_diag3, coe_dSL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem fixed_dual_dSL (u : Fin 3 → K3ˣ) (a b c : K3) (h : a * b * c = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) :
    (cU u * dl) (LinearFlag.proj 3 K3 (dSL a b c h)) = LinearFlag.proj 3 K3 (dSL a b c h) := by
  unfold cU dl
  rw [conjAut_dual_fixed_iff, coe_dSL, coe_diag3, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · show a * (u 0 : K3) * a = (u 0 : K3)
    linear_combination (u 0 : K3) * ha
  · show b * (u 1 : K3) * b = (u 1 : K3)
    linear_combination (u 1 : K3) * hb
  · show c * (u 2 : K3) * c = (u 2 : K3)
    linear_combination (u 2 : K3) * hc

theorem off_zero (d : Fin 3 → K3) (N : Matrix (Fin 3) (Fin 3) K3)
    (h : Matrix.diagonal d * N = N * Matrix.diagonal d) (i l : Fin 3) (hne : d i - d l ≠ 0) :
    N i l = 0 :=
  (mul_eq_zero.1 (comm_entry d N h i l)).resolve_left hne

theorem off_zero_sandwich (d : Fin 3 → K3) (N : Matrix (Fin 3) (Fin 3) K3)
    (h : Matrix.diagonal d * N * (Matrix.diagonal d).transpose = N) (i l : Fin 3) (hne : d i * d l - 1 ≠ 0) :
    N i l = 0 := by
  have h5 := congrFun (congrFun h i) l
  rw [diag_sandwich] at h5
  have h6 : (d i * d l - 1) * N i l = 0 := by linear_combination h5
  exact (mul_eq_zero.1 h6).resolve_left hne

theorem isDiag_of_two (A : Matrix (Fin 3) (Fin 3) K3)
    (h01 : A 0 1 = 0 ∧ A 1 0 = 0) (h02 : A 0 2 = 0 ∧ A 2 0 = 0) (h12 : A 1 2 = 0 ∧ A 2 1 = 0) :
    A.IsDiag := by
  intro i l hil
  fin_cases i <;> fin_cases l
  · exact absurd rfl hil
  · exact h01.1
  · exact h02.1
  · exact h01.2
  · exact absurd rfl hil
  · exact h12.1
  · exact h02.2
  · exact h12.2
  · exact absurd rfl hil

theorem locE2_three (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3)
    (hA : CFSG.IsElementaryAbelian 2 ↥D) [Finite ↥D] : LocE2 D.subtype := by
  have hα : D.subtype.range ≤ frameStab 3 K3 := by rwa [Subgroup.range_subtype]
  have hadm := adm_comap_noDual hA D.subtype hα
  set E : Subgroup ↥D := (noDual K3).comap D.subtype with hE
  have hfix : ∀ (a b c : K3) (h : a * b * c = 1), ∀ ψ ∈ E.map D.subtype,
      ψ (LinearFlag.proj 3 K3 (dSL a b c h)) = LinearFlag.proj 3 K3 (dSL a b c h) := by
    rintro a b c h _ ⟨e, he, rfl⟩
    obtain ⟨x, σ, hx, hax⟩ := he
    obtain ⟨u, rfl⟩ := exists_diag3 hx
    have : D.subtype e = cU u := by
      rw [hax, sigma_eq_one σ, map_one, mul_one]; rfl
    rw [this]
    exact fixed_dSL_of_diag u a b c h
  refine locE2_of_fix D.subtype (fixedIn _ (E.map D.subtype)) (le_gammaAct D.subtype hadm) ?_
  intro φ hφ
  have ht1 : (-1 : K3) * -1 * 1 = 1 := by decide
  have ht2 : (-1 : K3) * 1 * -1 = 1 := by decide
  have hφ1 := hφ _ (mem_fixedIn.2 (hfix (-1) (-1) 1 ht1))
  have hφ2 := hφ _ (mem_fixedIn.2 (hfix (-1) 1 (-1) ht2))
  obtain ⟨A, σ, ε, hε, hφeq⟩ := (LinearFlag.automorphism_generation (K := K3) (n := 3) le_rfl).2 φ
  rw [sigma_eq_one σ, map_one, mul_one] at hφeq
  have hdet : (A : Matrix (Fin 3) (Fin 3) K3).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hφeq
    rw [hφeq] at hφ1 hφ2
    have c1 := (conjAut_fixed_iff A _).1 hφ1
    have c2 := (conjAut_fixed_iff A _).1 hφ2
    rw [coe_dSL] at c1 c2
    have hdiag : (A : Matrix (Fin 3) (Fin 3) K3).IsDiag :=
      isDiag_of_two _ ⟨off_zero ![-1, 1, -1] _ c2.symm 0 1 (by decide),
          off_zero ![-1, 1, -1] _ c2.symm 1 0 (by decide)⟩
        ⟨off_zero ![-1, -1, 1] _ c1.symm 0 2 (by decide), off_zero ![-1, -1, 1] _ c1.symm 2 0 (by decide)⟩
        ⟨off_zero ![-1, -1, 1] _ c1.symm 1 2 (by decide), off_zero ![-1, -1, 1] _ c1.symm 2 1 (by decide)⟩
    have h2 : A ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, diag_sq _ hdiag hdet]; rfl)
    refine ⟨1, ?_⟩
    rw [hφeq, show (2 : ℕ) ^ 1 = 2 by norm_num, ← map_pow, h2, map_one]
  · rw [pow_one] at hφeq
    rw [hφeq] at hφ1 hφ2
    have c1 := (conjAut_dual_fixed_iff A _).1 hφ1
    have c2 := (conjAut_dual_fixed_iff A _).1 hφ2
    rw [coe_dSL] at c1 c2
    have hdiag : (A : Matrix (Fin 3) (Fin 3) K3).IsDiag := by
      refine isDiag_of_two _ ?_ ?_ ?_
      · exact ⟨off_zero_sandwich ![-1, 1, -1] _ c2 0 1 (by decide),
          off_zero_sandwich ![-1, 1, -1] _ c2 1 0 (by decide)⟩
      · exact ⟨off_zero_sandwich ![-1, -1, 1] _ c1 0 2 (by decide),
          off_zero_sandwich ![-1, -1, 1] _ c1 2 0 (by decide)⟩
      · exact ⟨off_zero_sandwich ![-1, -1, 1] _ c1 1 2 (by decide),
          off_zero_sandwich ![-1, -1, 1] _ c1 2 1 (by decide)⟩
    obtain ⟨u, rfl⟩ := exists_diag3 hdiag
    refine ⟨1, ?_⟩
    rw [hφeq, show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
    change (cU u * dl) * (cU u * dl) = 1
    rw [outer_mul_outer]
    have : (fun i => u i * (u i)⁻¹) = fun _ : Fin 3 => (1 : K3ˣ) := by
      funext i; exact mul_inv_cancel (u i)
    rw [this]
    unfold cU
    rw [diag3_const_one, map_one]

@[expose] def swapSL : SL(3, K3) :=
  ⟨!![0, 0, -1; 0, 1, 0; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

theorem dSL_sq (a b c : K3) (h : a * b * c = 1) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    dSL a b c h ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_dSL, Matrix.SpecialLinearGroup.coe_one, pow_two,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

theorem locE3_three (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3) : LocE3 D.subtype := by
  have ht1 : (-1 : K3) * -1 * 1 = 1 := by decide
  refine ⟨⊤, ?_, LinearFlag.proj 3 K3 (dSL (-1) (-1) 1 ht1), ?_, ⟨1, ?_⟩, LinearFlag.proj 3 K3 swapSL, ?_⟩
  · have h := GenLocBasic.pRank_congr (Subgroup.topEquiv : (⊤ : Subgroup ↥D) ≃* ↥D)
    omega
  · rw [mem_fixedIn]
    rintro φ ⟨d, -, rfl⟩
    rcases D_cases D hfs d with ⟨u, hu⟩ | ⟨u, hu⟩
    · show (d : MulAut P3) _ = _
      rw [hu]
      exact fixed_dSL_of_diag u _ _ _ ht1
    · show (d : MulAut P3) _ = _
      rw [hu]
      exact fixed_dual_dSL u _ _ _ ht1 (by decide) (by decide) (by decide)
  · rw [pow_one, ← map_pow, dSL_sq _ _ _ ht1 (by decide) (by decide) (by decide), map_one]
  · intro h
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg (fun x : SL(3, K3) => (x : Matrix (Fin 3) (Fin 3) K3) 0 2) (proj_injective h)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dSL, Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
    have e : ((swapSL : SL(3, K3)) : Matrix (Fin 3) (Fin 3) K3) 0 2 = -1 := rfl
    rw [e] at h'
    revert h'
    decide

end GenLocL3Three

end CFSG.GH74.Generic.BProg.B2
