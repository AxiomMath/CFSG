module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical.SteinbergBY

section Mult

variable {K : Type} [Field K]

local notation "M2" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K

theorem multiplier_scalarGsp (b : Kˣ) : multiplier 2 K (scalarGsp b : gsp 2 K) = b * b := by
  apply multiplier_eq
  rw [coe_scalarGsp, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_transpose,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, Units.val_mul]

theorem multiplier_gspFieldMap (σ : K ≃+* K) (A : gsp 2 K) :
    multiplier 2 K (gspFieldMap σ A) = Units.map (σ : K →* K) (multiplier 2 K A) := by
  apply multiplier_eq
  change (((A : GL (Fin 2 ⊕ Fin 2) K) : M2).map σ).transpose * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : M2).map σ = σ (multiplier 2 K A : K) • formJ 2 K
  have h1 : (((A : GL (Fin 2 ⊕ Fin 2) K) : M2).transpose * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : M2)).map σ =
      (((A : GL (Fin 2 ⊕ Fin 2) K) : M2).map σ).transpose * formJ 2 K *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : M2).map σ := by
    rw [map_mul_ringEquiv, map_mul_ringEquiv, Matrix.transpose_map,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ_map]
  rw [← h1, multiplier_spec]
  ext i j
  have h := congrFun (congrFun
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ_map (r := 2) σ) i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h ⊢
  rw [h]

theorem isSquare_ratio [Finite K] (hodd : ringChar K ≠ 2) (σ : K ≃+* K) (x : Kˣ) :
    ∃ c : Kˣ, Units.map (σ : K →* K) x * x⁻¹ = c * c := by
  classical
  have := Fintype.ofFinite K
  set q := Fintype.card K with hq
  have hx : (x : K) ≠ 0 := x.ne_zero
  have hqodd : Odd q := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
  have hq2 : 2 * (q / 2) = q - 1 := by
    obtain ⟨m, hm⟩ := hqodd
    omega
  have hs2 : ((x : K) ^ (q / 2)) * ((x : K) ^ (q / 2)) = 1 := by
    rw [← pow_add, ← two_mul, hq2]
    exact FiniteField.pow_card_sub_one_eq_one _ hx
  have hsσ : σ ((x : K) ^ (q / 2)) = (x : K) ^ (q / 2) := by
    rcases mul_self_eq_one_iff.mp hs2 with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  have hσx : σ (x : K) ≠ 0 := fun h => hx (σ.injective (by rw [h, map_zero]))
  have ha : σ (x : K) * (x : K)⁻¹ ≠ 0 := mul_ne_zero hσx (inv_ne_zero hx)
  have hsq : IsSquare (σ (x : K) * (x : K)⁻¹) := by
    rw [FiniteField.isSquare_iff hodd ha]
    rw [mul_pow, inv_pow, ← map_pow, hsσ]
    exact mul_inv_cancel₀ (pow_ne_zero _ hx)
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by rw [hc]; simp)
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simpa using hc

theorem conjAut_inner_of_multiplier_sq [Finite K] (M : gsp 2 K) (c : Kˣ)
    (hM : multiplier 2 K M = c * c) :
    conjAut 2 K M ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range := by
  have hker : M * scalarGsp c⁻¹ ∈ (multiplier 2 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, hM, multiplier_scalarGsp]
    group
  have h1 : conjAut 2 K M = conjAut 2 K (M * scalarGsp c⁻¹) := by
    rw [map_mul, conjAut_scalarGsp (by norm_num), mul_one]
  rw [h1]
  rw [ker_multiplier, Subgroup.mem_subgroupOf] at hker
  have hC : M * scalarGsp c⁻¹ = ⟨((⟨_, hker⟩ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K),
      statedSp_le_gsp hker⟩ := rfl
  rw [hC, conjAut_statedSp]
  exact ⟨_, rfl⟩

end Mult

section OutAb

theorem comm_group_aux {G : Type*} [CommGroup G] (a b sb ta : G) :
    a * sb * ta⁻¹ * b⁻¹ = (sb * b⁻¹) * (ta * a⁻¹)⁻¹ := by
  simp only [mul_inv_rev, inv_inv, mul_comm, mul_left_comm, mul_assoc]

theorem comm_group_aux₂ {G : Type*} [CommGroup G] (c₁ c₂ : G) :
    c₁ * c₁ * (c₂ * c₂)⁻¹ = (c₁ * c₂⁻¹) * (c₁ * c₂⁻¹) := by
  simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

variable {K : Type} [Field K] [Finite K]

theorem outAbelian_psp4 (hodd : ringChar K ≠ 2) : OutAbelian (StatedProj (StatedSp 2 K)) := by
  intro α β
  obtain ⟨A, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd α
  obtain ⟨B, τ, rfl⟩ := psp4_odd_automorphism_normal_form hodd β
  have hcomm : fieldAut 2 K σ * fieldAut 2 K τ = fieldAut 2 K τ * fieldAut 2 K σ := by
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  set M : gsp 2 K := A * gspFieldMap σ B * (gspFieldMap τ A)⁻¹ * B⁻¹ with hMdef
  have h1 : conjAut 2 K A * fieldAut 2 K σ * (conjAut 2 K B * fieldAut 2 K τ) *
      (conjAut 2 K A * fieldAut 2 K σ)⁻¹ * (conjAut 2 K B * fieldAut 2 K τ)⁻¹ = conjAut 2 K M := by
    have e1 : fieldAut 2 K σ * fieldAut 2 K τ * (fieldAut 2 K σ)⁻¹ = fieldAut 2 K τ := by
      rw [hcomm]; group
    have e2 := fieldAut_mul_conjAut_mul_inv σ B
    have e3 := fieldAut_mul_conjAut_mul_inv τ A
    calc conjAut 2 K A * fieldAut 2 K σ * (conjAut 2 K B * fieldAut 2 K τ) *
          (conjAut 2 K A * fieldAut 2 K σ)⁻¹ * (conjAut 2 K B * fieldAut 2 K τ)⁻¹
        = conjAut 2 K A * (fieldAut 2 K σ * conjAut 2 K B * (fieldAut 2 K σ)⁻¹) *
            (fieldAut 2 K σ * fieldAut 2 K τ * (fieldAut 2 K σ)⁻¹) * (conjAut 2 K A)⁻¹ *
            (fieldAut 2 K τ)⁻¹ * (conjAut 2 K B)⁻¹ := by group
      _ = conjAut 2 K A * conjAut 2 K (gspFieldMap σ B) * fieldAut 2 K τ * (conjAut 2 K A)⁻¹ *
            (fieldAut 2 K τ)⁻¹ * (conjAut 2 K B)⁻¹ := by rw [e1, e2]
      _ = conjAut 2 K A * conjAut 2 K (gspFieldMap σ B) *
            (fieldAut 2 K τ * conjAut 2 K A * (fieldAut 2 K τ)⁻¹)⁻¹ * (conjAut 2 K B)⁻¹ := by group
      _ = conjAut 2 K M := by rw [e3, hMdef]; simp only [map_mul, map_inv]
  rw [h1]
  obtain ⟨c₁, hc₁⟩ := isSquare_ratio hodd σ (multiplier 2 K B)
  obtain ⟨c₂, hc₂⟩ := isSquare_ratio hodd τ (multiplier 2 K A)
  refine conjAut_inner_of_multiplier_sq M (c₁ * c₂⁻¹) ?_
  rw [hMdef]
  simp only [map_mul, map_inv, multiplier_gspFieldMap]
  rw [comm_group_aux, hc₁, hc₂]
  exact comm_group_aux₂ c₁ c₂

end OutAb

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
