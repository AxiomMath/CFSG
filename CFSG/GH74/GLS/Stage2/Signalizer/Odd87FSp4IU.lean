module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4X
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4II

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4


section AI

variable {K : Type} [Field K]

theorem ωJ_elim (x₁ x₂ y₁ y₂ : Fin 2 → K) :
    ωJ K (Sum.elim x₁ x₂) (Sum.elim y₁ y₂) = x₁ ⬝ᵥ y₂ - x₂ ⬝ᵥ y₁ := by
  rw [ωJ_apply, formJ, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem bA_kron_bAinv {a : K} (ha : a ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) :
    bA a * kron g 1 * bAinv a =
      Matrix.fromBlocks (g 0 0 • 1) (g 0 1 • dAinv a) (g 1 0 • dA a) (g 1 1 • 1) := by
  rw [bA, bAinv, kron, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [dA_mul_dAinv ha]


theorem G_mulVec {a : K} (ha : a ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) (u u' : Fin 2 → K) :
    (bA a * kron g 1 * bAinv a) *ᵥ Sum.elim u u' =
      Sum.elim (g 0 0 • u + g 0 1 • (dAinv a *ᵥ u')) (g 1 0 • (dA a *ᵥ u) + g 1 1 • u') := by
  rw [bA_kron_bAinv ha, Matrix.fromBlocks_mulVec]
  simp [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem blk_one_neg_one_mulVec (u u' : Fin 2 → K) :
    (blk (1 : Matrix (Fin 2) (Fin 2) K) (-1)) *ᵥ Sum.elim u u' =
      Sum.elim (diag2 (1 : K) (-1) *ᵥ u) (diag2 (1 : K) (-1) *ᵥ u') := by
  rw [← diag_one_neg_one_eq_blk, kron, Matrix.fromBlocks_mulVec]
  simp

theorem dAinv_dA_dotProduct {a : K} (ha : a ≠ 0) (x y : Fin 2 → K) :
    (dAinv a *ᵥ x) ⬝ᵥ (dA a *ᵥ y) = x ⬝ᵥ y := by
  simp [dAinv, dA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp

theorem G_t_sub {a : K} (ha : a ≠ 0) (u u' : Fin 2 → K) :
    (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) *ᵥ Sum.elim u u' - Sum.elim u u' =
      Sum.elim (dAinv a *ᵥ u') (0 : Fin 2 → K) := by
  rw [G_mulVec ha]
  ext (i | i) <;> fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

theorem G_t'_sub {a : K} (ha : a ≠ 0) (u u' : Fin 2 → K) :
    (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) *ᵥ Sum.elim u u' - Sum.elim u u' =
      Sum.elim (0 : Fin 2 → K) (dA a *ᵥ u) := by
  rw [G_mulVec ha]
  ext (i | i) <;> fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

theorem G_J {a : K} (ha : a ≠ 0) (u u' : Fin 2 → K) :
    (bA a * kron !![0, 1; -1, 0] 1 * bAinv a) *ᵥ Sum.elim u u' =
      Sum.elim (dAinv a *ᵥ u') (-(dA a *ᵥ u)) := by
  rw [G_mulVec ha]
  ext (i | i) <;> fin_cases i <;> simp

theorem aI_no_invariant (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0)
    (W : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (hiso : ∀ x ∈ W, ∀ y ∈ W, ωJ K x y = 0)
    (hG : ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∀ w ∈ W, (bA a * kron g 1 * bAinv a) *ᵥ w ∈ W)
    (hT : ∀ w ∈ W, (blk (1 : Matrix (Fin 2) (Fin 2) K) (-1)) *ᵥ w ∈ W) : W = ⊥ := by
  have e1 : ∀ u u' : Fin 2 → K, Sum.elim u u' ∈ W → Sum.elim (dAinv a *ᵥ u') (0 : Fin 2 → K) ∈ W := by
    intro u u' hv
    have h := W.sub_mem (hG !![1, 1; 0, 1] (by simp [Matrix.det_fin_two_of]) _ hv) hv
    rwa [G_t_sub ha] at h
  have e2 : ∀ u u' : Fin 2 → K, Sum.elim u u' ∈ W → Sum.elim (0 : Fin 2 → K) (dA a *ᵥ u) ∈ W := by
    intro u u' hv
    have h := W.sub_mem (hG !![1, 0; 1, 1] (by simp [Matrix.det_fin_two_of]) _ hv) hv
    rwa [G_t'_sub ha] at h
  have e3 : ∀ u u' : Fin 2 → K, Sum.elim u u' ∈ W → Sum.elim (dAinv a *ᵥ u') (-(dA a *ᵥ u)) ∈ W := by
    intro u u' hv
    have h := hG !![0, 1; -1, 0] (by simp [Matrix.det_fin_two_of]) _ hv
    rwa [G_J ha] at h
  have e4 : ∀ u u' : Fin 2 → K, Sum.elim u u' ∈ W →
      Sum.elim (diag2 (1 : K) (-1) *ᵥ u) (diag2 (1 : K) (-1) *ᵥ u') ∈ W := by
    intro u u' hv
    have h := hT _ hv
    rwa [blk_one_neg_one_mulVec] at h
  have R1 : ∀ u₁ u₁' u₂ u₂' : Fin 2 → K, Sum.elim u₁ u₁' ∈ W → Sum.elim u₂ u₂' ∈ W →
      u₁' ⬝ᵥ u₂ = 0 := by
    intro u₁ u₁' u₂ u₂' h1 h2
    have h := hiso _ (e1 _ _ h1) _ (e2 _ _ h2)
    rw [ωJ_elim, dAinv_dA_dotProduct ha] at h
    simpa using h
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  obtain ⟨u, u', rfl⟩ : ∃ u u' : Fin 2 → K, w = Sum.elim u u' :=
    ⟨fun i => w (Sum.inl i), fun i => w (Sum.inr i), (Sum.elim_comp_inl_inr w).symm⟩
  have hA := R1 _ _ _ _ (e3 _ _ hw) hw
  have hB := R1 _ _ _ _ (e3 _ _ hw) (e4 _ _ hw)
  have hC := R1 _ _ _ _ hw (e3 _ _ hw)
  have hD := R1 _ _ _ _ hw (e4 _ _ (e3 _ _ hw))
  simp only [dotProduct, Fin.sum_univ_two, dA, dAinv, diag2, Matrix.mulVec, Pi.neg_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at hA hB hC hD
  have hu0 : u 0 = 0 := by
    have h : (2 : K) * (u 0 * u 0) = 0 := by linear_combination -hA - hB
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2)
  have hu1 : u 1 = 0 := by
    have h : (2 * a) * (u 1 * u 1) = 0 := by linear_combination hA - hB
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 ha))
  have hv0 : u' 0 = 0 := by
    have h : (2 : K) * (u' 0 * u' 0) = 0 := by linear_combination hC + hD
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2)
  have hv1 : u' 1 = 0 := by
    have h : (2 * a⁻¹) * (u' 1 * u' 1) = 0 := by linear_combination hD - hC
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 (inv_ne_zero ha)))
  ext (i | i) <;> fin_cases i <;> simp [hu0, hu1, hv0, hv1]

end AI

section Defining

theorem pairedSympForm_eq_ωJ {F : Type} [Field F] (x y : Fin 2 ⊕ Fin 2 → F) :
    pairedSympForm F 2 x y = ωJ F x y := by
  rw [ωJ_apply, pairedSympForm, Matrix.toBilin'_apply']

theorem aI_defining {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {a : F} (ha : a ≠ 0)
    {p : ℕ} [Fact p.Prime] (hpc : ringChar F = p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (alphaI ha) p X) : False := by
  classical
  have : CharP F p := hpc ▸ ringChar.charP F
  obtain ⟨hXp, hX1, -, hN⟩ := h
  obtain ⟨W, hW0, hWiso, hNW⟩ := exists_isotropic_parabolic hXp hX1
  have h2 := Ring.two_ne_zero hodd
  have hstab : ∀ g : StatedSp 2 F, alphaI ha (proj 2 F g) = proj 2 F g → ∀ w ∈ W,
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W := fun g hg =>
    mulVec_mem_of_proj_mem (hNW (hN (mem_fixSub.mpr hg)))
  have hiso : ∀ x ∈ W, ∀ y ∈ W, ωJ F x y = 0 := fun x hx y hy => by
    rw [← pairedSympForm_eq_ωJ]
    exact hWiso x hx y hy
  refine hW0 (aI_no_invariant h2 ha W hiso ?_ ?_)
  · intro g hg w hw
    have := hstab (gI ha ⟨g, hg⟩) (alphaI_JI ha ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩) w hw
    have e := coe_gI ha (⟨g, hg⟩ : Matrix.SpecialLinearGroup (Fin 2) F)
    rw [e] at this
    exact this
  · intro w hw
    have := hstab (T1 F) (alphaI_u1 ha) w hw
    rwa [coe_T1] at this

end Defining

section Cross

variable {K : Type} [Field K]

theorem exists_sq_of_pGroup {G : Type*} [Group G] {p : ℕ} (hpodd : Odd p) {H : Subgroup G}
    (hH : IsPGroup p H) {z : G} (hz : z ∈ H) : ∃ w ∈ H, w * w = z := by
  obtain ⟨k, hk⟩ := hH ⟨z, hz⟩
  have hk' : z ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := (hpodd.pow : Odd (p ^ k))
  refine ⟨z ^ (m + 1), H.pow_mem hz _, ?_⟩
  rw [← pow_add]
  have h1 : m + 1 + (m + 1) = p ^ k + 1 := by omega
  rw [h1, pow_succ, hk', one_mul]

theorem aI_block {a : K} (ha : a ≠ 0) (Z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hct : Z * (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) = (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) * Z)
    (hct' : Z * (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) = (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) * Z) :
    Z = Matrix.fromBlocks Z.toBlocks₁₁ 0 0 (dA a * Z.toBlocks₁₁ * dAinv a) := by
  have hDD : dA a * dAinv a = 1 := dA_mul_dAinv ha
  have hDD' : dAinv a * dA a = 1 := dAinv_mul_dA ha
  rw [bA_kron_bAinv ha] at hct hct'
  have hZ : Z = Matrix.fromBlocks Z.toBlocks₁₁ Z.toBlocks₁₂ Z.toBlocks₂₁ Z.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Z).symm
  set A := Z.toBlocks₁₁
  set B := Z.toBlocks₁₂
  set C := Z.toBlocks₂₁
  set E := Z.toBlocks₂₂
  rw [hZ] at hct hct'
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.fromBlocks_multiply, one_smul,
    zero_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.fromBlocks_inj] at hct hct'
  obtain ⟨-, h12, h21, h22⟩ := hct
  obtain ⟨h11', h12', h21', -⟩ := hct'
  have hC : C = 0 := by
    have : C * dAinv a = 0 := by
      have := h22
      simpa using this
    calc C = C * dAinv a * dA a := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = 0 := by rw [this, Matrix.zero_mul]
  have hB : B = 0 := by
    have : B * dA a = 0 := by
      have := h11'
      simpa using this
    calc B = B * dA a * dAinv a := by rw [Matrix.mul_assoc, hDD, Matrix.mul_one]
      _ = 0 := by rw [this, Matrix.zero_mul]
  have hE : E = dA a * A * dAinv a := by
    have h1 : A * dAinv a = dAinv a * E := by
      have := h12
      rw [add_comm B] at this
      exact add_right_cancel this
    calc E = (dA a * dAinv a) * E := by rw [hDD, Matrix.one_mul]
      _ = dA a * (dAinv a * E) := by rw [Matrix.mul_assoc]
      _ = dA a * (A * dAinv a) := by rw [h1]
      _ = dA a * A * dAinv a := by rw [Matrix.mul_assoc]
  conv_lhs => rw [hZ, hB, hC, hE]

theorem aI_eq' {a : K} :
    aI a = Matrix.fromBlocks (sA a) 0 0 (dA a * sA a * dAinv a) := by
  rw [aI, bA, bAinv, kron]
  simp [Matrix.fromBlocks_multiply]

theorem aI_orth {a : K} (ha : a ≠ 0) (h : Matrix (Fin 2) (Fin 2) K)
    (hZ : (Matrix.fromBlocks h 0 0 (dA a * h * dAinv a))ᵀ * formJ 2 K *
      Matrix.fromBlocks h 0 0 (dA a * h * dAinv a) = formJ 2 K) :
    hᵀ * dA a * h = dA a := by
  have hDD : dA a * dAinv a = 1 := dA_mul_dAinv ha
  have hDD' : dAinv a * dA a = 1 := dAinv_mul_dA ha
  rw [formJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hZ
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one,
    add_zero, zero_add, Matrix.fromBlocks_inj] at hZ
  obtain ⟨-, h01, -, -⟩ := hZ
  have h1 : hᵀ * (dA a * h * dAinv a) = 1 := by simpa using h01
  calc hᵀ * dA a * h = hᵀ * dA a * h * (dAinv a * dA a) := by rw [hDD', Matrix.mul_one]
    _ = (hᵀ * (dA a * h * dAinv a)) * dA a := by simp only [Matrix.mul_assoc]
    _ = dA a := by rw [h1, Matrix.one_mul]

theorem aI_det_sq {a : K} (ha : a ≠ 0) (h : Matrix (Fin 2) (Fin 2) K) (hh : hᵀ * dA a * h = dA a) :
    h.det * h.det = 1 := by
  have hd : (dA a).det ≠ 0 := by simp [dA, Matrix.det_fin_two_of, ha]
  have := congrArg Matrix.det hh
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
  have h2 : (h.det * h.det - 1) * (dA a).det = 0 := by linear_combination this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hd)

theorem aI_comm_sA {a : K} (h : Matrix (Fin 2) (Fin 2) K) (hh : hᵀ * dA a * h = dA a)
    (hdet : h.det = 1) : h * sA a = sA a * h := by
  have e00 := congrFun (congrFun hh 0) 0
  have e01 := congrFun (congrFun hh 0) 1
  have e11 := congrFun (congrFun hh 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, dA] at e00 e01 e11
  rw [Matrix.det_fin_two] at hdet
  have hs : h 1 1 = h 0 0 := by
    linear_combination (h 0 0) * hdet - (h 1 1) * e00 + (h 1 0) * e01
  have hq : h 0 1 = a * h 1 0 := by
    have h1 : h 0 0 * (h 0 1 - a * h 1 0) = 0 := by linear_combination e01 + (a * h 1 0) * hs
    have h2 : h 1 0 * (h 0 1 - a * h 1 0) = 0 := by linear_combination e00 - hdet + (h 0 0) * hs
    have h3 : h 0 1 - a * h 1 0 = 0 := by
      linear_combination (h 0 0) * h1 - (a * h 1 0) * h2 - (h 0 1 - a * h 1 0) * e00
    linear_combination h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, Matrix.mul_apply, Fin.sum_univ_two, hs, hq] <;> ring

@[expose] def slT (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def slT' (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem slT_pow_three (h3 : (3 : K) = 0) : slT K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slT, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination h3

theorem slT'_pow_three (h3 : (3 : K) = 0) : slT' K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slT', pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination h3

theorem coe_slT : ((slT K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl

theorem coe_slT' : ((slT' K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := rfl

theorem dAinv_mul_dA_mul {a : K} (ha : a ≠ 0) (X : Matrix (Fin 2) (Fin 2) K) :
    dAinv a * (dA a * X) = X := by
  rw [← Matrix.mul_assoc, dAinv_mul_dA ha, Matrix.one_mul]

theorem aI_comm_of {a : K} (ha : a ≠ 0) (Zw Zz : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hZ : Zz = Zw * Zw)
    (hsw : Zwᵀ * formJ 2 K * Zw = formJ 2 K) (hsz : Zzᵀ * formJ 2 K * Zz = formJ 2 K)
    (hw1 : Zw * (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) = (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) * Zw)
    (hw2 : Zw * (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) = (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) * Zw)
    (hz1 : Zz * (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) = (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) * Zz)
    (hz2 : Zz * (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) = (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) * Zz) :
    Zz * aI a = aI a * Zz := by
  obtain ⟨hw, hbw⟩ : ∃ h : Matrix (Fin 2) (Fin 2) K,
      Zw = Matrix.fromBlocks h 0 0 (dA a * h * dAinv a) := ⟨_, aI_block ha Zw hw1 hw2⟩
  obtain ⟨hz, hbz⟩ : ∃ h : Matrix (Fin 2) (Fin 2) K,
      Zz = Matrix.fromBlocks h 0 0 (dA a * h * dAinv a) := ⟨_, aI_block ha Zz hz1 hz2⟩
  subst hbw hbz
  have hzz : hz = hw * hw := by
    rw [Matrix.fromBlocks_multiply] at hZ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.fromBlocks_inj] at hZ
    exact hZ.1
  have horth_w := aI_orth ha hw hsw
  have horth_z := aI_orth ha hz hsz
  have hdetw := aI_det_sq ha hw horth_w
  have hdet : hz.det = 1 := by rw [hzz, Matrix.det_mul]; exact hdetw
  have hcomm := aI_comm_sA hz horth_z hdet
  rw [aI_eq', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_inj]
  refine ⟨hcomm, trivial, trivial, ?_⟩
  calc dA a * hz * dAinv a * (dA a * sA a * dAinv a) = dA a * (hz * sA a) * dAinv a := by
        simp only [Matrix.mul_assoc, dAinv_mul_dA_mul ha]
    _ = dA a * (sA a * hz) * dAinv a := by rw [hcomm]
    _ = dA a * sA a * dAinv a * (dA a * hz * dAinv a) := by
        simp only [Matrix.mul_assoc, dAinv_mul_dA_mul ha]

theorem three_eq_zero_of_card_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) : (3 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h
  exact_mod_cast h

end Cross

section CrossMain

theorem aI_cross {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {a : F} (ha : a ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpl : ringChar F ≠ p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (alphaI ha) p X) : False := by
  classical
  obtain ⟨hXp, hX1, hcomm, hN⟩ := h
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hJN : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F,
      proj 2 F (gI ha k) ∈ normalizer (X : Set (StatedProj (StatedSp 2 F))) := fun k =>
    hN (mem_fixSub.mpr (alphaI_JI ha ⟨_, ⟨k, rfl⟩, rfl⟩))
  obtain ⟨X₀, hX₀p, hmap, hcent⟩ : ∃ X₀ : Subgroup (StatedSp 2 F), IsPGroup p X₀ ∧
      X₀.map (proj 2 F) = X ∧ ∀ z ∈ X₀, gI ha (slT F) * z = z * gI ha (slT F) ∧
        gI ha (slT' F) * z = z * gI ha (slT' F) := by
    by_cases hF3 : Nat.card F = 3
    · have h3 : (3 : F) = 0 := three_eq_zero_of_card_three hF3
      obtain ⟨X₀, hX₀p, hmap, hcard, hnorm⟩ := exists_lift hodd hp2 hXp
      refine ⟨X₀, hX₀p, hmap, fun z hz => ⟨?_, ?_⟩⟩
      · exact three_centralizes hodd hF3 hp2 hpl hX₀p hcard (gI ha (slT F))
          (by rw [← map_pow, slT_pow_three h3, map_one])
          (fun z hz => hnorm _ (hJN _) z hz) z hz
      · exact three_centralizes hodd hF3 hp2 hpl hX₀p hcard (gI ha (slT' F))
          (by rw [← map_pow, slT'_pow_three h3, map_one])
          (fun z hz => hnorm _ (hJN _) z hz) z hz
    · have hcard4 : ∃ s : Finset F, s.card = 4 := by
        have : Fintype F := Fintype.ofFinite F
        have hodd' : Nat.card F % 2 = 1 := by
          rw [Nat.card_eq_fintype_card]
          exact FiniteField.odd_card_of_char_ne_two hodd
        have h1 := Finite.one_lt_card (α := F)
        have hge : 4 ≤ Fintype.card F := by
          rw [← Nat.card_eq_fintype_card]
          omega
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
          (by rw [Finset.card_univ]; exact hge)
        exact ⟨s, hs⟩
      have hperf : Group.IsPerfect (gI ha).range := by
        have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
          CFSG.LinearGroups.special_linear_dimension_two_perfect hcard4
        exact Group.IsPerfect.range (gI ha)
      obtain ⟨X₀, hX₀p, hmap, -, hc⟩ := cross_centralizes hodd hp2 hpl hXp hperf
        (by rintro _ ⟨k, rfl⟩; exact hJN k)
      exact ⟨X₀, hX₀p, hmap, fun z hz => ⟨hc z hz _ ⟨_, rfl⟩, hc z hz _ ⟨_, rfl⟩⟩⟩
  have hmat : ∀ y ∈ X₀,
      ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) =
      (bA a * kron !![1, 1; 0, 1] 1 * bAinv a) *
        ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ∧
      ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) =
      (bA a * kron !![1, 0; 1, 1] 1 * bAinv a) *
        ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hcent y hy
    constructor
    · have := congrArg (fun g : StatedSp 2 F => ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h1
      simp only [Subgroup.coe_mul, Units.val_mul, coe_gI, coe_slT] at this
      exact this.symm
    · have := congrArg (fun g : StatedSp 2 F => ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h2
      simp only [Subgroup.coe_mul, Units.val_mul, coe_gI, coe_slT'] at this
      exact this.symm
  have hfix : ∀ z ∈ X₀, alphaI ha (proj 2 F z) = proj 2 F z := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := exists_sq_of_pGroup hpodd hX₀p hz
    have hZ : ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ((w : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          ((w : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      rw [← hwz]
      rfl
    have hcm := aI_comm_of ha _ _ hZ (symplectic_of_mem w) (symplectic_of_mem z) (hmat w hw).1
      (hmat w hw).2 (hmat z hz).1 (hmat z hz).2
    have hz' : z ∈ fixOf (conjSp 2 F (aIgsp ha)) :=
      mem_fixOf_conjSp_of_comm (aIgsp ha) (by rw [coe_aIgsp]; exact hcm.symm)
    rw [alphaI, conjAut_proj, mem_fixOf.mp hz']
  apply hX1
  rw [← hcomm, eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rw [← hmap] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  simp [hfix z hz]

end CrossMain


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
