module

public import CFSG.ClassicalInvolution.Phan.PhanQ4Wit
public import CFSG.ClassicalInvolution.Phan.PhanQ5Split
import CFSG.ClassicalInvolution.Phan.PhanP19Perp
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.Phan.PhanQ3Fwd

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section Aux

variable {F : Type} [Field F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem polar_planeA_eq_zero (h2 : (2 : F) ≠ 0) {p : V8 F} (hp1 : B8 (vecA1 F) p = 0)
    (hp2 : B8 (jOp ε (vecA1 F)) p = 0) {a : V8 F} (ha : a ∈ planeA ε hε h4) :
    polar (quadPlus 4 F) a p = 0 := by
  obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 ha
  change B8 (α • vecA1 F + β • jOp ε (vecA1 F)) p = 0
  rw [B8_lin_left, hp1, hp2]
  ring

end Aux

section Core

variable {F : Type} [Field F] [Finite F]

theorem exists_normal_core {ε : F} (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F))
    {ρ : spinGroup (quadPlus 4 F)} {Mρ : SL(2, F)}
    (hρM : (frame0 (F := F)).La Mρ = spinAction (quadPlus 4 F) ρ)
    (hρB : ∀ a ∈ planeA ε hε h4, spinAction (quadPlus 4 F) ρ a ∈ planeB ε hε h4)
    {k : spinGroup (quadPlus 4 F)} (hk : ColStd ε k) :
    ∃ y ∈ fixA ε hε h4, ∃ N : Matrix (Fin 2) (Fin 2) F, N.det = 1 ∧
      spinAction (quadPlus 4 F) y⁻¹ (spinAction (quadPlus 4 F) k (vecA1 F)) =
        (frame0 (F := F)).incl N ∧
      spinAction (quadPlus 4 F) y⁻¹ (spinAction (quadPlus 4 F) k (jOp ε (vecA1 F))) =
        (frame0 (F := F)).incl (N * Jm ε) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hk' : ColP ε (z0 ε) (k • z0 ε) := hk
  obtain ⟨P, S, u, v, hwx, hwy, hPS, hxu, hyu, hxv, hyv, hQu, hQv, hBuv⟩ := exists_split h2 hε hk'
  simp only [z0_x, z0_y, NPair.smul_x, NPair.smul_y] at hwx hwy hxu hyu hxv hyv
  set ν : F := 1 - (P ^ 2 + S ^ 2 / ε) / 4 with hνdef
  have hν : ν ≠ 0 := by
    intro h0
    apply hPS
    have h1 : (P ^ 2 + S ^ 2 / ε) / 4 = 1 := by linear_combination -h0
    calc P ^ 2 + S ^ 2 / ε = 4 * ((P ^ 2 + S ^ 2 / ε) / 4) := (mul_div_cancel₀ _ h4).symm
      _ = 4 := by rw [h1]; ring
  obtain ⟨s1, t1, hst⟩ := exists_norm_eq hodd hε ν⁻¹
  obtain ⟨hx'Q, hy'Q, hx'y'⟩ := scale_pair_norms hε s1 t1 hQu hQv hBuv
  rw [hst, inv_mul_cancel₀ hν] at hx'Q
  rw [hst, inv_mul_cancel₀ hν] at hy'Q
  rw [mul_one] at hy'Q
  obtain ⟨g', hg'x, hg'y⟩ := exists_spin_pair h2 hodd hε h4 hx'Q hy'Q hx'y'
  have hx'a : B8 (vecA1 F) (s1 • u + (-(t1 / ε)) • v) = 0 := by
    rw [B8_lin_right, hxu, hxv]
    ring
  have hx'b : B8 (jOp ε (vecA1 F)) (s1 • u + (-(t1 / ε)) • v) = 0 := by
    rw [B8_lin_right, hyu, hyv]
    ring
  have hy'a : B8 (vecA1 F) (t1 • u + s1 • v) = 0 := by
    rw [B8_lin_right, hxu, hxv]
    ring
  have hy'b : B8 (jOp ε (vecA1 F)) (t1 • u + s1 • v) = 0 := by
    rw [B8_lin_right, hyu, hyv]
    ring
  have hg'perp : ∀ a ∈ planeA ε hε h4, ∀ a' ∈ planeA ε hε h4,
      polar (quadPlus 4 F) (spinAction (quadPlus 4 F) g' a) a' = 0 := by
    intro a ha a' ha'
    obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 ha
    rw [map_add, map_smul, map_smul, hg'x, hg'y]
    have e1 : B8 a' (s1 • u + (-(t1 / ε)) • v) = 0 := polar_planeA_eq_zero h2 hx'a hx'b ha'
    have e2 : B8 a' (t1 • u + s1 • v) = 0 := polar_planeA_eq_zero h2 hy'a hy'b ha'
    change B8 (α • (s1 • u + (-(t1 / ε)) • v) + β • (t1 • u + s1 • v)) a' = 0
    rw [B8_lin_left, B8_comm _ a', B8_comm _ a', e1, e2]
    ring
  have hρperp : ∀ a ∈ planeA ε hε h4, ∀ a' ∈ planeA ε hε h4,
      polar (quadPlus 4 F) (spinAction (quadPlus 4 F) ρ a) a' = 0 :=
    fun a ha a' ha' => polar_planeB_planeA h2 ha' (hρB a ha)
  have hQnd := nondegenerate_polarBilin_quadPlus 4 F
  have hAnd := restrict_planeA_nondegenerate h2 hε h4
  have hV : 2 * Module.finrank F (planeA ε hε h4) + 2 ≤ Module.finrank F (V8 F) := by
    rw [finrank_planeA h2 hε h4, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin]
    norm_num
  obtain ⟨y, hy1, hy2⟩ := exists_spin_fix_map hodd hQnd hAnd hV ρ g' hρperp hg'perp
  have ha0 : vecA1 F ∈ planeA ε hε h4 := vecA1_mem_planeA ε hε h4
  have hb0 : jOp ε (vecA1 F) ∈ planeA ε hε h4 := jOp_mem_planeA h2 ha0
  have hinvapp : ∀ z : V8 F, spinAction (quadPlus 4 F) y⁻¹ (spinAction (quadPlus 4 F) y z) = z := by
    intro z
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hyinv : ∀ a ∈ planeA ε hε h4, spinAction (quadPlus 4 F) y⁻¹ a = a := by
    intro a ha
    have := hinvapp a
    rwa [hy1 a ha] at this
  have key1 : spinAction (quadPlus 4 F) y⁻¹ (s1 • u + (-(t1 / ε)) • v) =
      spinAction (quadPlus 4 F) ρ (vecA1 F) := by
    have h := hy2 _ ha0
    rw [hg'x] at h
    rw [← h, hinvapp]
  have key2 : spinAction (quadPlus 4 F) y⁻¹ (t1 • u + s1 • v) =
      spinAction (quadPlus 4 F) ρ (jOp ε (vecA1 F)) := by
    have h := hy2 _ hb0
    rw [hg'y] at h
    rw [← h, hinvapp]
  obtain ⟨hcu, hcv⟩ := scale_pair_inv (ε := ε) s1 t1 u v
  rw [hst] at hcu hcv
  have hu : u = ν • (s1 • (s1 • u + (-(t1 / ε)) • v) + (t1 / ε) • (t1 • u + s1 • v)) := by
    rw [← hcu, smul_smul, mul_inv_cancel₀ hν, one_smul]
  have hv : v = ν • ((-t1) • (s1 • u + (-(t1 / ε)) • v) + s1 • (t1 • u + s1 • v)) := by
    rw [← hcv, smul_smul, mul_inv_cancel₀ hν, one_smul]
  have hyu_ : spinAction (quadPlus 4 F) y⁻¹ u = ν • (s1 • spinAction (quadPlus 4 F) ρ (vecA1 F) +
      (t1 / ε) • spinAction (quadPlus 4 F) ρ (jOp ε (vecA1 F))) := by
    have := congrArg (spinAction (quadPlus 4 F) y⁻¹) hu
    rw [map_smul, map_add, map_smul, map_smul, key1, key2] at this
    exact this
  have hyv_ : spinAction (quadPlus 4 F) y⁻¹ v = ν • ((-t1) • spinAction (quadPlus 4 F) ρ (vecA1 F) +
      s1 • spinAction (quadPlus 4 F) ρ (jOp ε (vecA1 F))) := by
    have := congrArg (spinAction (quadPlus 4 F) y⁻¹) hv
    rw [map_smul, map_add, map_smul, map_smul, key1, key2] at this
    exact this
  obtain ⟨hρx, hρy⟩ := smul_z0_of_La ε hρM
  simp only [NPair.smul_x, NPair.smul_y, z0_x, z0_y] at hρx hρy
  have hJ1 : jOp ε (vecA1 F) = (frame0 (F := F)).incl (Jm ε) := jOp_vecA1 ε
  have h1m : vecA1 F = (frame0 (F := F)).incl 1 := rfl
  set Nw : Matrix (Fin 2) (Fin 2) F := (P / 2) • (1 : Matrix (Fin 2) (Fin 2) F) +
    (S / (2 * ε)) • Jm ε + (ν * s1) • (Mρ : Matrix (Fin 2) (Fin 2) F) +
    (ν * t1 / ε) • ((Mρ : Matrix (Fin 2) (Fin 2) F) * Jm ε) with hNw
  have hψx : spinAction (quadPlus 4 F) y⁻¹ (spinAction (quadPlus 4 F) k (vecA1 F)) =
      (frame0 (F := F)).incl Nw := by
    rw [hwx, map_add, map_add, map_smul, map_smul, hyinv _ ha0, hyinv _ hb0, hyu_, hρx, hρy, hNw]
    rw [hJ1, h1m]
    simp only [map_add, map_smul]
    module
  have hψy : spinAction (quadPlus 4 F) y⁻¹ (spinAction (quadPlus 4 F) k (jOp ε (vecA1 F))) =
      (frame0 (F := F)).incl (Nw * Jm ε) := by
    have hNJ : Nw * Jm ε = (P / 2) • Jm ε + (-(S / 2)) • (1 : Matrix (Fin 2) (Fin 2) F) +
        (ν * s1) • ((Mρ : Matrix (Fin 2) (Fin 2) F) * Jm ε) +
        (-(ν * t1)) • (Mρ : Matrix (Fin 2) (Fin 2) F) := by
      rw [hNw]
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, Jm_mul_Jm,
        Matrix.mul_smul, Matrix.mul_one]
      match_scalars <;> field_simp
    rw [hwy, map_add, map_add, map_smul, map_smul, hyinv _ ha0, hyinv _ hb0, hyv_, hρx, hρy, hNJ]
    rw [hJ1, h1m]
    simp only [map_add, map_smul]
    module
  have hdet : Nw.det = 1 := by
    have h1 := map_spinAction (quadPlus 4 F) y⁻¹ (spinAction (quadPlus 4 F) k (vecA1 F))
    have h2' := map_spinAction (quadPlus 4 F) k (vecA1 F)
    rw [hψx, Frame.Q_incl] at h1
    rw [h1, h2']
    exact Q_vecA1
  exact ⟨y, hy1, Nw, hdet, hψx, hψy⟩

theorem exists_factor_core {ε : F} (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) (R0 : Subgroup (spinGroup (quadPlus 4 F)))
    {ρ : spinGroup (quadPlus 4 F)} {Mρ : SL(2, F)}
    (hρM : (frame0 (F := F)).La Mρ = spinAction (quadPlus 4 F) ρ)
    (hρB : ∀ a ∈ planeA ε hε h4, spinAction (quadPlus 4 F) ρ a ∈ planeB ε hε h4)
    (hLa : ∀ A : SL(2, F), ∃ r ∈ R0, spinAction (quadPlus 4 F) r = (frame0 (F := F)).La A)
    {k : spinGroup (quadPlus 4 F)} (hk : ColStd ε k) :
    ∃ y ∈ fixA ε hε h4, ∃ r ∈ R0, ∃ f ∈ fixA ε hε h4, k = y * r * f := by
  obtain ⟨y, hy1, Nw, hdet, hψx, hψy⟩ := exists_normal_core hε h4 h2 hodd hρM hρB hk
  obtain ⟨r, hrR0, hr⟩ := hLa ⟨Nw, hdet⟩
  obtain ⟨hrx, hry⟩ := smul_z0_of_La ε hr.symm
  simp only [NPair.smul_x, NPair.smul_y, z0_x, z0_y] at hrx hry
  have hpsi : y⁻¹ • (k • z0 ε) = r • z0 ε := by
    ext1
    · rw [NPair.smul_x, NPair.smul_x, NPair.smul_x, z0_x, hrx]
      exact hψx
    · rw [NPair.smul_y, NPair.smul_y, NPair.smul_y, z0_y, hry]
      exact hψy
  have hfz : (r⁻¹ * y⁻¹ * k) • z0 ε = z0 ε := by
    rw [NPair.mul_smul', NPair.mul_smul', hpsi, NPair.inv_smul_smul']
  refine ⟨y, hy1, r, hrR0, r⁻¹ * y⁻¹ * k, ?_, by group⟩
  intro a ha
  obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 ha
  have e1 := congrArg NPair.x hfz
  have e2 := congrArg NPair.y hfz
  simp only [NPair.smul_x, NPair.smul_y, z0_x, z0_y] at e1 e2
  rw [map_add, map_smul, map_smul, e1, e2]

end Core

section NormalWrapper

variable {p e : ℕ} [Fact p.Prime]

theorem exists_normal_pair (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {w : NPair M.ε} (hw : ColP M.ε (z0 M.ε) w) :
    ∃ g : spinGroup (quadPlus 4 (GaloisField p e)), g • z0 M.ε = z0 M.ε ∧
      ∃ N : Matrix (Fin 2) (Fin 2) (GaloisField p e), N.det = 1 ∧
        (g • w).x = (frame0 (F := GaloisField p e)).incl N ∧
        (g • w).y = (frame0 (F := GaloisField p e)).incl (N * Jm M.ε) := by
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  obtain ⟨ρ, hρ, hρB⟩ := exists_rho_perp M.spec h2 hodd
  have hmem : spinAction (quadPlus 4 (GaloisField p e)) ρ ∈
      (stdFrames M.ε M.hε M.h4 0).La.range := by
    rw [← M.spec.map_range 0]
    exact ⟨ρ, hρ, rfl⟩
  obtain ⟨Mρ, hρM⟩ := hmem
  obtain ⟨k, rfl⟩ := exists_smul_z0 h2 hodd M.hε M.h4 w
  obtain ⟨y, hy, N, hN, hx, hy'⟩ := exists_normal_core M.hε M.h4 h2 hodd hρM hρB hw
  refine ⟨y⁻¹, ?_, N, hN, hx, hy'⟩
  have hyinv : y⁻¹ ∈ fixA M.ε M.hε M.h4 := inv_mem hy
  ext1
  · exact hyinv _ (vecA1_mem_planeA M.ε M.hε M.h4)
  · exact hyinv _ (jOp_mem_planeA h2 (vecA1_mem_planeA M.ε M.hε M.h4))

end NormalWrapper

section Wrapper

variable {p e : ℕ} [Fact p.Prime]

theorem exists_factor_of_colStd (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {k : spinGroup (quadPlus 4 (GaloisField p e))} (hk : ColStd M.ε k) :
    ∃ y ∈ parab M.S {1, 2, 3}, ∃ ρ ∈ parab M.S {0}, ∃ z ∈ parab M.S {1, 2, 3},
      k = y * ρ * z := by
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  obtain ⟨ρ, hρ, hρB⟩ := exists_rho_perp M.spec h2 hodd
  have hmem : spinAction (quadPlus 4 (GaloisField p e)) ρ ∈
      (stdFrames M.ε M.hε M.h4 0).La.range := by
    rw [← M.spec.map_range 0]
    exact ⟨ρ, hρ, rfl⟩
  obtain ⟨Mρ, hρM⟩ := hmem
  have hLa : ∀ A : SL(2, GaloisField p e), ∃ r ∈ (M.S.ι 0).range,
      spinAction (quadPlus 4 (GaloisField p e)) r = (frame0 (F := GaloisField p e)).La A := by
    intro A
    have h : (frame0 (F := GaloisField p e)).La A ∈ (stdFrames M.ε M.hε M.h4 0).La.range :=
      ⟨A, rfl⟩
    rw [← M.spec.map_range 0] at h
    obtain ⟨r, hr, hrA⟩ := h
    exact ⟨r, hr, hrA⟩
  obtain ⟨y, hy, r, hr, f, hf, hkyrf⟩ := exists_factor_core M.hε M.h4 h2 hodd (M.S.ι 0).range
    hρM hρB hLa hk
  exact ⟨y, fixA_le_parab M hp2 hq hy, r,
    Lsup_le_parab (S := M.S) {0} (by rw [Lsup_singleton]; exact hr), f,
    fixA_le_parab M hp2 hq hf, hkyrf⟩

end Wrapper

end CFSG.ClassicalInvolution.PhanQ
