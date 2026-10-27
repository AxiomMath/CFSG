module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvLinearModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.LinearInv
open scoped MatrixGroups

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem coord_of_fix (R R₀ : Sylow 2 SL(2, K)) (hR : (R : Subgroup SL(2, K)) = upSub)
    (hR₀ : (R₀ : Subgroup SL(2, K)) = loSub) (γ : MulAut SL(2, K))
    (hγR : γ • R = R) (hγR₀ : γ • R₀ = R₀) :
    ∃ (θ : K →+* K) (lam : K), lam ≠ 0 ∧ ∀ b, γ (up b) = up (lam * θ b) := by
  classical
  have hex : ∀ b : K, ∃ b', γ (up b) = up b' := by
    intro b
    have h := InvInner.apply_mem_of_smul_eq hγR
      (show up b ∈ (R : Subgroup SL(2, K)) by rw [hR]; exact up_mem b)
    rw [hR] at h
    exact mem_upSub.mp h
  choose L hL using hex
  have hLadd : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    apply up_injective
    rw [← hL, ← up_mul, map_mul, hL, hL, up_mul]
  have hL0 : L 0 = 0 := by
    have h := hLadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hex' : ∀ t : Kˣ, ∃ t', γ (dg t) = dg t' := by
    intro t
    have h1 := Omega.mem_normalizer_smul (α := γ) (S := R) (g := dg t)
      (by rw [hR]; exact dg_mem_normalizer_up t)
    have h2 := Omega.mem_normalizer_smul (α := γ) (S := R₀) (g := dg t)
      (by rw [hR₀]; exact dg_mem_normalizer_lo t)
    rw [hγR, hR] at h1
    rw [hγR₀, hR₀] at h2
    exact eq_dg_of_mem_normalizer h1 h2
  choose φ hφ using hex'
  have hLsq : ∀ (t : Kˣ) (b : K), L ((t : K) ^ 2 * b) = (φ t : K) ^ 2 * L b := by
    intro t b
    apply up_injective
    rw [← hL, ← dg_conj_up, map_mul, map_mul, map_inv, hφ, hL, dg_conj_up]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, L 1 = lam := ⟨_, rfl⟩
  have hlam0 : lam ≠ 0 := by
    intro h
    have h1 : γ (up 1) = γ 1 := by rw [hL, hlamdef, h, up_zero, map_one]
    exact one_ne_zero (up_injective ((γ.injective h1).trans up_zero.symm))
  have hLmul : ∀ s b, L (s * b) * lam = L s * L b := by
    intro s b
    by_cases hs : s = 0
    · rw [hs, zero_mul, hL0, zero_mul, zero_mul]
    · obtain ⟨t, ht⟩ := isSquare_of_charTwo' s
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hs (by rw [ht, mul_zero])
      have h1 := hLsq (Units.mk0 t ht0) b
      have h2 := hLsq (Units.mk0 t ht0) 1
      rw [mul_one, hlamdef] at h2
      simp only [Units.val_mk0] at h1 h2
      rw [ht, ← sq, h1, h2]
      ring
  set θ : K → K := fun a => L a * lam⁻¹ with hθdef
  have hLθ : ∀ a, L a = lam * θ a := fun a => by
    simp only [hθdef]
    field_simp
  have hθ1 : θ 1 = 1 := by
    simp only [hθdef, hlamdef]
    exact mul_inv_cancel₀ hlam0
  have hθ0 : θ 0 = 0 := by simp only [hθdef, hL0, zero_mul]
  have hθadd : ∀ a a', θ (a + a') = θ a + θ a' := fun a a' => by
    simp only [hθdef, hLadd]
    ring
  have hθmul : ∀ a a', θ (a * a') = θ a * θ a' := by
    intro a a'
    have h := hLmul a a'
    calc θ (a * a') = (L (a * a') * lam) * lam⁻¹ * lam⁻¹ := by
          simp only [hθdef]
          field_simp
      _ = θ a * θ a' := by
          rw [h]
          simp only [hθdef]
          ring
  let θr : K →+* K :=
    { toFun := θ
      map_one' := hθ1
      map_mul' := hθmul
      map_zero' := hθ0
      map_add' := hθadd }
  exact ⟨θr, lam, hlam0, fun b => by rw [hL, hLθ]; rfl⟩

theorem inner_of_coord_id [IsSimpleGroup SL(2, K)] (R R₀ : Sylow 2 SL(2, K))
    (hR : (R : Subgroup SL(2, K)) = upSub) (hR₀ : (R₀ : Subgroup SL(2, K)) = loSub)
    (hSE : fusionStronglyEmbedded (normalizer ((R : Subgroup SL(2, K)) : Set SL(2, K))))
    (hcard : Nat.card (Sylow 2 SL(2, K)) = Nat.card (R : Subgroup SL(2, K)) + 1)
    (γ : MulAut SL(2, K)) (hγR : γ • R = R) (hγR₀ : γ • R₀ = R₀) {lam : K} (hlam : lam ≠ 0)
    (hγ : ∀ b, γ (up b) = up (lam * b)) : ∃ y, γ = MulAut.conj y := by
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' lam
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hlam (by rw [hμ, mul_zero])
  set t : Kˣ := Units.mk0 μ hμ0 with ht
  have hne : R₀ ≠ R := by
    intro h
    apply upSub_ne_loSub (K := K)
    rw [← hR, ← hR₀, h]
  set γ' := (MulAut.conj (dg t))⁻¹ * γ with hγ'
  have hsmulU : (MulAut.conj (dg t))⁻¹ • R = R := by
    rw [inv_smul_eq_iff, eq_comm, RankTwoBender.conj_smul_eq_iff, hR]
    exact dg_mem_normalizer_up t
  have hsmulV : (MulAut.conj (dg t))⁻¹ • R₀ = R₀ := by
    rw [inv_smul_eq_iff, eq_comm, RankTwoBender.conj_smul_eq_iff, hR₀]
    exact dg_mem_normalizer_lo t
  have h1 : γ' • R = R := by rw [hγ', mul_smul, hγR, hsmulU]
  have h2 : γ' • R₀ = R₀ := by rw [hγ', mul_smul, hγR₀, hsmulV]
  have h3 : ∀ r ∈ (R : Subgroup SL(2, K)), γ' r = r := by
    intro r hr
    rw [hR] at hr
    obtain ⟨b, rfl⟩ := mem_upSub.mp hr
    rw [hγ', MulAut.mul_apply, hγ, MulAut.inv_apply, MulAut.conj_symm_apply]
    have h4 := dg_conj_up t⁻¹ (lam * b)
    rw [dg_inv, inv_inv] at h4
    rw [dg_inv, h4]
    congr 1
    rw [hμ]
    simp only [ht, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  have h5 := Omega.eq_one_of_centralizes hSE hcard hne γ' h1 h2 h3
  refine ⟨dg t, ?_⟩
  rw [hγ'] at h5
  calc γ = MulAut.conj (dg t) * ((MulAut.conj (dg t))⁻¹ * γ) := by group
    _ = MulAut.conj (dg t) := by rw [h5, mul_one]

omit [Finite K] [CharP K 2] in
theorem involutive_of_sq_inner (R R₀ : Sylow 2 SL(2, K)) (hR : (R : Subgroup SL(2, K)) = upSub)
    (hR₀ : (R₀ : Subgroup SL(2, K)) = loSub) (γ : MulAut SL(2, K)) (hγR : γ • R = R)
    (hγR₀ : γ • R₀ = R₀) {θ : K →+* K} {lam : K} (hγ : ∀ b, γ (up b) = up (lam * θ b))
    (hsq : ∃ y, γ * γ = MulAut.conj y) : ∀ b, θ (θ b) = b := by
  obtain ⟨y, hy⟩ := hsq
  have hyU : y ∈ normalizer ((upSub : Subgroup SL(2, K)) : Set SL(2, K)) := by
    rw [← hR, ← RankTwoBender.conj_smul_eq_iff, ← hy, mul_smul, hγR, hγR]
  have hyV : y ∈ normalizer ((loSub : Subgroup SL(2, K)) : Set SL(2, K)) := by
    rw [← hR₀, ← RankTwoBender.conj_smul_eq_iff, ← hy, mul_smul, hγR₀, hγR₀]
  obtain ⟨t, rfl⟩ := eq_dg_of_mem_normalizer hyU hyV
  have key : ∀ b, lam * θ lam * θ (θ b) = (t : K) ^ 2 * b := by
    intro b
    apply up_injective
    have h1 : (γ * γ) (up b) = MulAut.conj (dg t) (up b) := by rw [hy]
    rw [MulAut.mul_apply, hγ, hγ, MulAut.conj_apply, dg_conj_up, map_mul] at h1
    rw [← h1, mul_assoc]
  have h1 := key 1
  rw [map_one, map_one, mul_one, mul_one] at h1
  have ht0 : ((t : K) ^ 2) ≠ 0 := pow_ne_zero 2 t.ne_zero
  intro b
  have h2 := key b
  rw [h1] at h2
  exact mul_left_cancel₀ ht0 h2

omit [Finite K] [CharP K 2] in
theorem sq_conj_mul_conj {γ : MulAut SL(2, K)} {y : SL(2, K)} (hy : γ * γ = MulAut.conj y)
    (a b : SL(2, K)) :
    (MulAut.conj a * γ * MulAut.conj b) * (MulAut.conj a * γ * MulAut.conj b) =
      MulAut.conj (a * γ (b * a) * y * b) := by
  have key : ∀ x, γ (γ x) = y * x * y⁻¹ := fun x => by
    have h := congrArg (fun φ : MulAut SL(2, K) => φ x) hy
    simpa [MulAut.conj_apply] using h
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, key]
  group

end CFSG.ComponentClassification.GMS78
