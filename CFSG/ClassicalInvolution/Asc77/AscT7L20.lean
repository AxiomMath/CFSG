module

public import CFSG.ClassicalInvolution.Asc77.AscT7L19
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpAlg

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (r0 coe_r0)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat coe_sl2Upper coe_sl2Lower mem_closure_sl2)
open scoped MatrixGroups

namespace T7L

section Core

variable {F : Type} [Field F]

@[expose] def v4 (a0 a1 b0 b1 : F) : Fin 2 ⊕ Fin 2 → F := Sum.elim ![a0, a1] ![b0, b1]

omit [Field F] in
theorem eq_v4 (x : Fin 2 ⊕ Fin 2 → F) :
    x = v4 (x (Sum.inl 0)) (x (Sum.inl 1)) (x (Sum.inr 0)) (x (Sum.inr 1)) := by
  funext a
  rcases a with a | a <;> fin_cases a <;> rfl

theorem spForm_v4 (a0 a1 b0 b1 c0 c1 d0 d1 : F) :
    spForm (v4 a0 a1 b0 b1) (v4 c0 c1 d0 d1) = a0 * d0 - b0 * c0 + a1 * d1 - b1 * c1 := by
  simp [spForm, v4, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.mulVec,
    Matrix.fromBlocks]
  ring

theorem mat_blk_v4 (A B : Matrix.SpecialLinearGroup (Fin 2) F) (a0 a1 b0 b1 : F) :
    mat 2 F (blk F A B) *ᵥ v4 a0 a1 b0 b1 =
      v4 ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * a0 + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * b0)
        ((B : Matrix (Fin 2) (Fin 2) F) 0 0 * a1 + (B : Matrix (Fin 2) (Fin 2) F) 0 1 * b1)
        ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * a0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * b0)
        ((B : Matrix (Fin 2) (Fin 2) F) 1 0 * a1 + (B : Matrix (Fin 2) (Fin 2) F) 1 1 * b1) := by
  rw [mat_blk]
  funext r
  rcases r with r | r <;> fin_cases r <;>
    simp [v4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.diagonal_apply]

theorem mat_x0_v4 (a0 a1 b0 b1 : F) :
    mat 2 F (x0 F) *ᵥ v4 a0 a1 b0 b1 = v4 (-a0) a1 (-b0) b1 := by
  rw [mat_x0]
  funext r
  rcases r with r | r <;> fin_cases r <;> simp [v4, Matrix.mulVec_diagonal, coords]

theorem mat_t0_v4 (a0 a1 b0 b1 : F) :
    mat 2 F (t0 F) *ᵥ v4 a0 a1 b0 b1 = v4 (-b0) b1 a0 (-a1) := by
  rw [t0_eq_blk, mat_blk_v4]
  simp [coe_r0]

theorem blk_comm_x0 (A B : SL(2, F)) : blk F A B * x0 F = x0 F * blk F A B := by
  rw [x0_eq_blk, blk_mul, blk_mul, mul_one, one_mul, neg_one_comm]

theorem mat_shortBlock_v4 (A : SL(2, F)) (a0 a1 b0 b1 : F) :
    mat 2 F (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) A) *ᵥ v4 a0 a1 b0 b1 =
      v4 ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * a0 + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * a1)
        ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * a0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * a1)
        (((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 * b0 +
          ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 * b1)
        (((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 * b0 +
          ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 * b1) := by
  rw [mat_shortBlock]
  funext r
  rcases r with r | r <;> fin_cases r <;>
    simp [v4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, blockMat]

theorem shortBlock_upper_eq (h2 : (2 : F) ≠ 0) (c : F) :
    shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Upper c) =
      tv (v4 1 0 0 1) (-(c / 2)) * tv (v4 1 0 0 (-1)) (c / 2) := by
  apply mat_injective
  apply matrix_ext_of_mulVec
  intro x
  have hinv : ((sl2Upper c)⁻¹ : SL(2, F)) = sl2Upper (-c) := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two]
  rw [eq_v4 x, map_mul, ← Matrix.mulVec_mulVec, mat_tv_mulVec, mat_tv_mulVec, mat_shortBlock_v4,
    hinv]
  simp only [spForm_add_right, spForm_smul_right', spForm_v4, coe_sl2Upper]
  funext r
  rcases r with r | r <;> fin_cases r <;> simp [v4] <;> (field_simp; ring)

theorem shortBlock_lower_eq (h2 : (2 : F) ≠ 0) (c : F) :
    shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Lower c) =
      tv (v4 0 1 1 0) (-(c / 2)) * tv (v4 0 1 (-1) 0) (c / 2) := by
  apply mat_injective
  apply matrix_ext_of_mulVec
  intro x
  have hinv : ((sl2Lower c)⁻¹ : SL(2, F)) = sl2Lower (-c) := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
  rw [eq_v4 x, map_mul, ← Matrix.mulVec_mulVec, mat_tv_mulVec, mat_tv_mulVec, mat_shortBlock_v4,
    hinv]
  simp only [spForm_add_right, spForm_smul_right', spForm_v4, coe_sl2Lower]
  funext r
  rcases r with r | r <;> fin_cases r <;> simp [v4] <;> (field_simp; ring)

theorem top_le_x0_sup_t0 (h2 : (2 : F) ≠ 0) :
    (⊤ : Subgroup (StatedSp 2 F)) ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({t0 F} : Set (StatedSp 2 F)) := by
  set H : Subgroup (StatedSp 2 F) := Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
    Subgroup.centralizer ({t0 F} : Set (StatedSp 2 F)) with hH
  have hx : ∀ g : StatedSp 2 F, g * x0 F = x0 F * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have ht : ∀ g : StatedSp 2 F, g * t0 F = t0 F * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hblk : ∀ A B : SL(2, F), blk F A B ∈ H := fun A B => hx _ (blk_comm_x0 A B)
  set v : Fin 2 ⊕ Fin 2 → F := v4 1 1 0 0 with hv
  set w : Fin 2 ⊕ Fin 2 → F := v4 0 0 1 (-1) with hw
  have hvw : spForm v w = 0 := by rw [hv, hw, spForm_v4]; ring
  have htv : mat 2 F (t0 F) *ᵥ v = w := by rw [hv, hw, mat_t0_v4]; simp
  have htw : mat 2 F (t0 F) *ᵥ w = -v := by
    rw [hv, hw, mat_t0_v4]
    funext r
    rcases r with r | r <;> fin_cases r <;> simp [v4]
  have hA : ∀ κ : F, tv v κ * tv w κ ∈ H := by
    intro κ
    apply ht
    have e1 : t0 F * tv v κ * (t0 F)⁻¹ = tv w κ := by rw [conj_tv, htv]
    have e2 : t0 F * tv w κ * (t0 F)⁻¹ = tv v κ := by rw [conj_tv, htw, tv_neg_vec]
    have e3 : t0 F * (tv v κ * tv w κ) * (t0 F)⁻¹ = tv v κ * tv w κ := by
      calc t0 F * (tv v κ * tv w κ) * (t0 F)⁻¹
          = (t0 F * tv v κ * (t0 F)⁻¹) * (t0 F * tv w κ * (t0 F)⁻¹) := by group
        _ = tv w κ * tv v κ := by rw [e1, e2]
        _ = tv v κ * tv w κ := (tv_comm hvw κ κ).symm
    exact (mul_inv_eq_iff_eq_mul.mp e3).symm
  have hg : ∀ σ κ : F, tv (v4 1 1 (-σ) σ) κ * tv v (-κ) ∈ H := by
    intro σ κ
    set g : StatedSp 2 F := blk F (sl2Lower (-σ)) (sl2Lower σ) with hgdef
    have hgv : mat 2 F g *ᵥ v = v4 1 1 (-σ) σ := by
      rw [hgdef, hv, mat_blk_v4]
      simp [coe_sl2Lower]
    have hgw : mat 2 F g *ᵥ w = w := by
      rw [hgdef, hw, mat_blk_v4]
      simp [coe_sl2Lower]
    have hgH : g ∈ H := hblk _ _
    have hmem := H.mul_mem (H.mul_mem (H.mul_mem hgH (hA κ)) (H.inv_mem hgH))
      (H.inv_mem (hA κ))
    have e : g * (tv v κ * tv w κ) * g⁻¹ * (tv v κ * tv w κ)⁻¹ =
        tv (v4 1 1 (-σ) σ) κ * tv v (-κ) := by
      have hww : tv w κ * tv w (-κ) = 1 := by rw [tv_mul, add_neg_cancel, tv_zero]
      calc g * (tv v κ * tv w κ) * g⁻¹ * (tv v κ * tv w κ)⁻¹
          = (g * tv v κ * g⁻¹) * (g * tv w κ * g⁻¹) * ((tv w κ)⁻¹ * (tv v κ)⁻¹) := by group
        _ = tv (v4 1 1 (-σ) σ) κ * tv w κ * (tv w (-κ) * tv v (-κ)) := by
          rw [conj_tv, conj_tv, hgv, hgw, tv_inv, tv_inv]
        _ = tv (v4 1 1 (-σ) σ) κ * (tv w κ * tv w (-κ)) * tv v (-κ) := by group
        _ = tv (v4 1 1 (-σ) σ) κ * tv v (-κ) := by rw [hww, mul_one]
    rwa [e] at hmem
  have hsub : v - w = v4 1 1 (-1) 1 := by
    funext r
    rcases r with r | r <;> fin_cases r <;> simp [hv, hw, v4]
  have hadd : v + w = v4 1 1 1 (-1) := by
    funext r
    rcases r with r | r <;> fin_cases r <;> simp [hv, hw, v4]
  have hvb : spForm v (v + w) = 0 := by rw [spForm_add_right, spForm_self, hvw, add_zero]
  have hQ : ∀ κ : F, tv w (κ + κ) ∈ H := by
    intro κ
    have h1 := hg 1 κ
    have h2' := hg (-1) κ
    have e : tv (v4 1 1 (-1) 1) κ * tv v (-κ) * (tv (v4 1 1 (-(-1)) (-1)) κ * tv v (-κ)) =
        tv w (κ + κ) := by
      have ea : v4 1 1 (-(1 : F)) 1 = v - w := hsub.symm
      have eb : v4 1 1 (-(-1 : F)) (-1) = v + w := by rw [neg_neg, hadd]
      rw [ea, eb]
      calc tv (v - w) κ * tv v (-κ) * (tv (v + w) κ * tv v (-κ))
          = tv (v - w) κ * (tv v (-κ) * tv (v + w) κ) * tv v (-κ) := by group
        _ = tv (v - w) κ * (tv (v + w) κ * tv v (-κ)) * tv v (-κ) := by rw [tv_comm hvb]
        _ = tv (v - w) κ * tv (v + w) κ * (tv v (-κ) * tv v (-κ)) := by group
        _ = tv (v - w) κ * tv (v + w) κ * tv v (-κ + -κ) := by rw [tv_mul]
        _ = tv w (κ + κ) := tv_three hvw κ
    rw [← e]
    exact H.mul_mem h1 h2'
  have hw_all : ∀ κ : F, tv w κ ∈ H := by
    intro κ
    have := hQ (κ / 2)
    rwa [show κ / 2 + κ / 2 = κ by field_simp; ring] at this
  have hmove : ∀ (A B : SL(2, F)) (u : Fin 2 ⊕ Fin 2 → F), mat 2 F (blk F A B) *ᵥ w = u →
      ∀ κ : F, tv u κ ∈ H := by
    intro A B u hu κ
    have e : blk F A B * tv w κ * (blk F A B)⁻¹ = tv u κ := by rw [conj_tv, hu]
    rw [← e]
    exact H.mul_mem (H.mul_mem (hblk A B) (hw_all κ)) (H.inv_mem (hblk A B))
  have hu1 : ∀ κ : F, tv (v4 1 0 0 1) κ ∈ H := hmove r0 (-1) _
    (by rw [hw, mat_blk_v4]; simp [coe_r0, Matrix.SpecialLinearGroup.coe_neg])
  have hu2 : ∀ κ : F, tv (v4 1 0 0 (-1)) κ ∈ H := hmove r0 1 _
    (by rw [hw, mat_blk_v4]; simp [coe_r0])
  have hu3 : ∀ κ : F, tv (v4 0 1 1 0) κ ∈ H := hmove 1 (-r0) _
    (by rw [hw, mat_blk_v4]; simp [coe_r0, Matrix.SpecialLinearGroup.coe_neg])
  have hu4 : ∀ κ : F, tv (v4 0 1 (-1) 0) κ ∈ H := hmove (-1) (-r0) _
    (by rw [hw, mat_blk_v4]; simp [coe_r0, Matrix.SpecialLinearGroup.coe_neg])
  have hS : (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range ≤ H := by
    rintro _ ⟨A, rfl⟩
    have hcl : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        H.comap (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Upper c) ∈ H
        rw [shortBlock_upper_eq h2]
        exact H.mul_mem (hu1 _) (hu2 _)
      · show shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Lower c) ∈ H
        rw [shortBlock_lower_eq h2]
        exact H.mul_mem (hu3 _) (hu4 _)
    exact hcl (mem_closure_sl2 A)
  have hL : (longBlock F 2 1).range ≤ H := by
    rintro _ ⟨B, rfl⟩
    have e : longBlock F 2 1 B = blk F 1 B := by simp [blk]
    rw [e]
    exact hblk _ _
  intro g _
  have hg' : g ∈ (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range ⊔
      (longBlock F 2 1).range := by
    rw [shortBlock_sup_longBlock_eq_top]
    trivial
  exact sup_le hS hL hg'

end Core

end T7L

end CFSG.ClassicalInvolution.Asc77
