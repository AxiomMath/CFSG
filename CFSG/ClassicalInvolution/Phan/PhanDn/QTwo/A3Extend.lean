module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixLem62
public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair
public import CFSG.ClassicalInvolution.Phan.Phan3TAutB

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan
open CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Phan.Q3G
open CFSG.LieType.BorelTits
open CFSG.StandardType.QTwo
open CFSG.StandardType.QTwo.SixPoint
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoSixExt_diagField_blockEmb (hK : Nat.card K = 4) (D : Fin 4 → Kˣ) (τ : K ≃+* K)
    (i : ℕ) (h : i + 3 ≤ 4) (u : Su K 2 1 3) :
    qTwoSixExt_diagField hK D τ (blockEmb K 2 1 4 3 i h u) =
      blockEmb K 2 1 4 3 i h
        (qTwoSixExt_diagField hK (fun a => D ⟨i + a, by omega⟩) τ u) := by
  refine Subtype.ext (Units.ext ?_)
  rw [qTwoSixExt_diagField_matrix]
  conv_lhs => rw [coe_coe_blockEmb]
  rw [Q3G.autA_map_blockMat]
  conv_rhs => rw [coe_coe_blockEmb]
  rw [qTwoSixExt_diagField_matrix]
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Fin.ext_iff]
  · fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Fin.ext_iff]

theorem qTwoSixExt_diagField_smul (hK : Nat.card K = 4) {n : ℕ} (c : Kˣ) (d : Fin n → Kˣ)
    (τ : K ≃+* K) :
    qTwoSixExt_diagField hK (fun a => c * d a) τ = qTwoSixExt_diagField hK d τ := by
  refine MulEquiv.ext ?_
  intro u
  refine Subtype.ext (Units.ext ?_)
  rw [qTwoSixExt_diagField_matrix, qTwoSixExt_diagField_matrix]
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, map_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

private theorem injective_of_card_range (hK : Nat.card K = 4) {G : Type} [Group G]
    {f : Su K 2 1 3 →* G} (hf : Nat.card f.range = 216) : Function.Injective f := by
  have hker : Nat.card f.ker = 1 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hf, qTwoS34_card_Su_three hK] at h
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have hkle : Nat.card f.ker ≤ 1 := by
      by_contra hcon
      have h2 : 2 ≤ Nat.card f.ker := by omega
      have h3 : 2 * 216 ≤ Nat.card f.ker * 216 := Nat.mul_le_mul_right 216 h2
      omega
    omega
  have hbot : f.ker = ⊥ := Subgroup.eq_bot_of_card_eq (H := f.ker) hker
  exact (MonoidHom.ker_eq_bot_iff f).mp hbot

private theorem a3_entry_11
    {α₁ α₂ : Su K 2 1 3 ≃* Su K 2 1 3}
    (hcompat : ∀ v : Su K 2 1 2,
      blk012 K (α₁ (embSUid (unitaryInvolution K 2 1) 0 v)) =
        blk123 K (α₂ (embSUid (unitaryInvolution K 2 1) 2 v)))
    (v : Su K 2 1 2) :
    (((α₁ (embSUid (unitaryInvolution K 2 1) 0 v) : Su K 2 1 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 1 =
      (((α₂ (embSUid (unitaryInvolution K 2 1) 2 v) : Su K 2 1 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 0 := by
  have h := congrFun (congrFun (congrArg (fun g : Su K 2 1 4 =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) (hcompat v)) 1) 1
  rw [blk012, blk123, coe_coe_blockEmb, coe_coe_blockEmb,
    blockMat_apply, blockMat_apply] at h
  rw [dite_eq_left (by omega), dite_eq_left (by omega)] at h
  exact h

private theorem a3_entry_12
    {α₁ α₂ : Su K 2 1 3 ≃* Su K 2 1 3}
    (hcompat : ∀ v : Su K 2 1 2,
      blk012 K (α₁ (embSUid (unitaryInvolution K 2 1) 0 v)) =
        blk123 K (α₂ (embSUid (unitaryInvolution K 2 1) 2 v)))
    (v : Su K 2 1 2) :
    (((α₁ (embSUid (unitaryInvolution K 2 1) 0 v) : Su K 2 1 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 2 =
      (((α₂ (embSUid (unitaryInvolution K 2 1) 2 v) : Su K 2 1 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 1 := by
  have h := congrFun (congrFun (congrArg (fun g : Su K 2 1 4 =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) (hcompat v)) 1) 2
  rw [blk012, blk123, coe_coe_blockEmb, coe_coe_blockEmb,
    blockMat_apply, blockMat_apply] at h
  rw [dite_eq_left (by omega), dite_eq_left (by omega)] at h
  exact h

private theorem a3_sigma_eq (hK : Nat.card K = 4)
    (d₁ : Fin 3 → Kˣ) (σ₁ : K ≃+* K) (d₂ : Fin 3 → Kˣ) (σ₂ : K ≃+* K)
    {α₁ α₂ : Su K 2 1 3 ≃* Su K 2 1 3}
    (hα₁_eq : α₁ = qTwoSixExt_diagField hK d₁ σ₁)
    (hα₂_eq : α₂ = qTwoSixExt_diagField hK d₂ σ₂)
    (hcompat : ∀ v : Su K 2 1 2,
      blk012 K (α₁ (embSUid (unitaryInvolution K 2 1) 0 v)) =
        blk123 K (α₂ (embSUid (unitaryInvolution K 2 1) 2 v))) :
    σ₁ = σ₂ := by
  apply ringEquiv_eq_of_eq_on_normOne (p := 2) (f := 1) (by simpa using hK)
  intro u
  let v : Su K 2 1 2 := torusTwo (unitaryInvolution K 2 1) u
  have h11 := a3_entry_11 hcompat v
  rw [hα₁_eq, hα₂_eq] at h11
  simp only [qTwoSixExt_diagField_matrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.map_apply] at h11
  rw [embSUid_zero_eq_blockEmb, embSUid_two_eq_blockEmb] at h11
  simp only [coe_coe_blockEmb, blockMat_apply] at h11
  rw [dite_eq_left (by omega), dite_eq_left (by omega)] at h11
  norm_num at h11
  rw [coe_torusTwo] at h11
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero] at h11
  have hd1 : ((d₁ 1 : Kˣ) : K) ≠ 0 := (d₁ 1).ne_zero
  have hd2 : ((d₂ 0 : Kˣ) : K) ≠ 0 := (d₂ 0).ne_zero
  field_simp [hd1, hd2] at h11
  exact h11

private theorem a3_ratio_eq (hK : Nat.card K = 4)
    (d₁ : Fin 3 → Kˣ) (σ₁ : K ≃+* K) (d₂ : Fin 3 → Kˣ) (σ₂ : K ≃+* K)
    {α₁ α₂ : Su K 2 1 3 ≃* Su K 2 1 3}
    (hα₁_eq : α₁ = qTwoSixExt_diagField hK d₁ σ₁)
    (hα₂_eq : α₂ = qTwoSixExt_diagField hK d₂ σ₂)
    (hcompat : ∀ v : Su K 2 1 2,
      blk012 K (α₁ (embSUid (unitaryInvolution K 2 1) 0 v)) =
        blk123 K (α₂ (embSUid (unitaryInvolution K 2 1) 2 v))) :
    d₁ 1 * (d₁ 2)⁻¹ = d₂ 0 * (d₂ 1)⁻¹ := by
  have h12 := a3_entry_12 hcompat (weylElt K 2 1)
  rw [hα₁_eq, hα₂_eq] at h12
  simp only [qTwoSixExt_diagField_matrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.map_apply] at h12
  rw [embSUid_zero_eq_blockEmb, embSUid_two_eq_blockEmb] at h12
  simp only [coe_coe_blockEmb, blockMat_apply] at h12
  rw [dite_eq_left (by omega), dite_eq_left (by omega)] at h12
  norm_num at h12
  rw [autB_weylElt_zero_one] at h12
  simp only [map_one, mul_one] at h12
  refine Units.ext ?_
  simpa using h12

theorem qTwoA3_extend (hK : Nat.card K = 4)
    {G : Type} [Group G] {κ : Su K 2 1 4 →* G}
    (hκ : Function.Injective κ) {θa θb : Su K 2 1 3 →* G}
    (ha : θa.range = (κ.comp (blk012 K)).range)
    (ha1 : (B12 K 2 1).map θa = (B12 K 2 1).map (κ.comp (blk012 K)))
    (ha2 : (B23 K 2 1).map θa = (B23 K 2 1).map (κ.comp (blk012 K)))
    (hb : θb.range = (κ.comp (blk123 K)).range)
    (hb2 : (B23 K 2 1).map θb = (B23 K 2 1).map (κ.comp (blk123 K)))
    (hmid : θa.comp (embSUid (unitaryInvolution K 2 1) 0) =
      θb.comp (embSUid (unitaryInvolution K 2 1) 2)) :
    ∃ κ' : Su K 2 1 4 →* G, κ'.comp (blk012 K) = θa ∧ κ'.comp (blk123 K) = θb := by
  have hκ012_inj : Function.Injective (κ.comp (blk012 K)) :=
    hκ.comp (blockEmb_injective _)
  have hκ123_inj : Function.Injective (κ.comp (blk123 K)) :=
    hκ.comp (blockEmb_injective _)
  have hθa_inj : Function.Injective θa := by
    apply injective_of_card_range hK
    rw [ha, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hκ012_inj,
      Subgroup.card_top, qTwoS34_card_Su_three hK]
  have hθb_inj : Function.Injective θb := by
    apply injective_of_card_range hK
    rw [hb, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hκ123_inj,
      Subgroup.card_top, qTwoS34_card_Su_three hK]
  let eκ : Su K 2 1 3 ≃* (κ.comp (blk012 K)).range := MonoidHom.ofInjective hκ012_inj
  let eθa : Su K 2 1 3 ≃* θa.range := MonoidHom.ofInjective hθa_inj
  let α₁ : Su K 2 1 3 ≃* Su K 2 1 3 :=
    (eθa.trans (MulEquiv.subgroupCongr ha)).trans eκ.symm
  have hα₁ : (κ.comp (blk012 K)).comp α₁.toMonoidHom = θa := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have h1 : α₁ x = eκ.symm (MulEquiv.subgroupCongr ha (eθa x)) := rfl
    rw [h1]
    have h2 : ∀ y : (κ.comp (blk012 K)).range,
        κ (blk012 K (eκ.symm y)) = (y : G) := by
      intro y
      have h := MonoidHom.ofInjective_apply hκ012_inj (x := eκ.symm y)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    rw [h2, MulEquiv.subgroupCongr_apply]
    exact MonoidHom.ofInjective_apply hθa_inj (x := x)
  let eκ123 : Su K 2 1 3 ≃* (κ.comp (blk123 K)).range := MonoidHom.ofInjective hκ123_inj
  let eθb : Su K 2 1 3 ≃* θb.range := MonoidHom.ofInjective hθb_inj
  let α₂ : Su K 2 1 3 ≃* Su K 2 1 3 :=
    (eθb.trans (MulEquiv.subgroupCongr hb)).trans eκ123.symm
  have hα₂ : (κ.comp (blk123 K)).comp α₂.toMonoidHom = θb := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have h1 : α₂ x = eκ123.symm (MulEquiv.subgroupCongr hb (eθb x)) := rfl
    rw [h1]
    have h2 : ∀ y : (κ.comp (blk123 K)).range,
        κ (blk123 K (eκ123.symm y)) = (y : G) := by
      intro y
      have h := MonoidHom.ofInjective_apply hκ123_inj (x := eκ123.symm y)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    rw [h2, MulEquiv.subgroupCongr_apply]
    exact MonoidHom.ofInjective_apply hθb_inj (x := x)
  have hB12α₁ : (B12 K 2 1).map α₁.toMonoidHom = B12 K 2 1 := by
    apply Subgroup.map_injective hκ012_inj
    rw [Subgroup.map_map, hα₁]
    exact ha1
  have hB23α₁ : (B23 K 2 1).map α₁.toMonoidHom = B23 K 2 1 := by
    apply Subgroup.map_injective hκ012_inj
    rw [Subgroup.map_map, hα₁]
    exact ha2
  have hB23α₂ : (B23 K 2 1).map α₂.toMonoidHom = B23 K 2 1 := by
    apply Subgroup.map_injective hκ123_inj
    rw [Subgroup.map_map, hα₂]
    exact hb2
  have hB12α₂ : (B12 K 2 1).map α₂.toMonoidHom = B12 K 2 1 := by
    apply Subgroup.map_injective hκ123_inj
    rw [Subgroup.map_map, hα₂]
    have hB12 : B12 K 2 1 = (embSUid (unitaryInvolution K 2 1) 2).range := rfl
    have hB23 : B23 K 2 1 = (embSUid (unitaryInvolution K 2 1) 0).range := rfl
    calc
      (B12 K 2 1).map θb = ((embSUid (unitaryInvolution K 2 1) 2).range).map θb := by
        rw [hB12]
      _ = (θb.comp (embSUid (unitaryInvolution K 2 1) 2)).range := by
        rw [MonoidHom.map_range]
      _ = (θa.comp (embSUid (unitaryInvolution K 2 1) 0)).range := by rw [hmid]
      _ = ((embSUid (unitaryInvolution K 2 1) 0).range).map θa := by
        rw [← MonoidHom.map_range]
      _ = (B23 K 2 1).map θa := by rw [hB23]
      _ = (B23 K 2 1).map (κ.comp (blk012 K)) := ha2
      _ = ((embSUid (unitaryInvolution K 2 1) 0).range).map (κ.comp (blk012 K)) := by
        rw [hB23]
      _ = ((κ.comp (blk012 K)).comp (embSUid (unitaryInvolution K 2 1) 0)).range := by
        rw [MonoidHom.map_range]
      _ = ((κ.comp (blk123 K)).comp (embSUid (unitaryInvolution K 2 1) 2)).range := by
        rw [MonoidHom.comp_assoc, ← blk123_comp_embSUid_two, ← MonoidHom.comp_assoc]
      _ = ((embSUid (unitaryInvolution K 2 1) 2).range).map (κ.comp (blk123 K)) := by
        rw [← MonoidHom.map_range]
      _ = (B12 K 2 1).map (κ.comp (blk123 K)) := by rw [hB12]
  have hcoord₁01 : (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map α₁.toMonoidHom =
      coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
    rw [← B12_eq_coordBlockSU]
    exact hB12α₁
  have hcoord₁12 : (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map α₁.toMonoidHom =
      coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
    rw [← B23_eq_coordBlockSU]
    exact hB23α₁
  obtain ⟨d₁, σ₁, hd₁⟩ := qTwoSix_lem62 hK α₁ hcoord₁01 hcoord₁12
  have hcoord₂01 : (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map α₂.toMonoidHom =
      coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
    rw [← B12_eq_coordBlockSU]
    exact hB12α₂
  have hcoord₂12 : (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map α₂.toMonoidHom =
      coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
    rw [← B23_eq_coordBlockSU]
    exact hB23α₂
  obtain ⟨d₂, σ₂, hd₂⟩ := qTwoSix_lem62 hK α₂ hcoord₂01 hcoord₂12
  have hα₁_eq : α₁ = qTwoSixExt_diagField hK d₁ σ₁ := by
    refine MulEquiv.ext fun u => Subtype.ext (Units.ext ?_)
    rw [qTwoSixExt_diagField_matrix]
    exact hd₁ u
  have hα₂_eq : α₂ = qTwoSixExt_diagField hK d₂ σ₂ := by
    refine MulEquiv.ext fun u => Subtype.ext (Units.ext ?_)
    rw [qTwoSixExt_diagField_matrix]
    exact hd₂ u
  have hcompat : ∀ v : Su K 2 1 2,
      blk012 K (α₁ (embSUid (unitaryInvolution K 2 1) 0 v)) =
        blk123 K (α₂ (embSUid (unitaryInvolution K 2 1) 2 v)) := by
    intro v
    have h1 : θa (embSUid (unitaryInvolution K 2 1) 0 v) =
        θb (embSUid (unitaryInvolution K 2 1) 2 v) := by
      rw [← MonoidHom.comp_apply, hmid, MonoidHom.comp_apply]
    rw [← hα₁, ← hα₂] at h1
    exact hκ h1
  have hσ_eq : σ₁ = σ₂ := a3_sigma_eq hK d₁ σ₁ d₂ σ₂ hα₁_eq hα₂_eq hcompat
  have hratio : d₁ 1 * (d₁ 2)⁻¹ = d₂ 0 * (d₂ 1)⁻¹ :=
    a3_ratio_eq hK d₁ σ₁ d₂ σ₂ hα₁_eq hα₂_eq hcompat
  let c : Kˣ := d₁ 2 * (d₂ 1)⁻¹
  let D₄ : Fin 4 → Kˣ := ![d₁ 0, d₁ 1, d₁ 2, d₁ 2 * d₂ 2 * (d₂ 1)⁻¹]
  have hc : d₁ 1 = c * d₂ 0 := by
    calc d₁ 1 = (d₁ 1 * (d₁ 2)⁻¹) * d₁ 2 := by group
      _ = (d₂ 0 * (d₂ 1)⁻¹) * d₁ 2 := by rw [hratio]
      _ = d₁ 2 * (d₂ 1)⁻¹ * d₂ 0 := by ac_rfl
      _ = c * d₂ 0 := rfl
  have hD₄_0 : (fun a : Fin 3 => D₄ (Fin.mk (0 + a.val) (by have := a.isLt; omega))) =
      d₁ := by
    funext a
    fin_cases a <;> simp [D₄]
  have hD₄_1 : (fun a : Fin 3 => D₄ (Fin.mk (1 + a.val) (by have := a.isLt; omega))) =
      fun a => c * d₂ a := by
    funext a
    fin_cases a <;> simp [D₄, c, hc]
    ac_rfl
  let β : Su K 2 1 4 ≃* Su K 2 1 4 := qTwoSixExt_diagField hK D₄ σ₁
  let κ' : Su K 2 1 4 →* G := κ.comp β.toMonoidHom
  refine ⟨κ', ?_, ?_⟩
  · ext u
    have hβ := qTwoSixExt_diagField_blockEmb hK D₄ σ₁ 0 (by norm_num) u
    change κ ((qTwoSixExt_diagField hK D₄ σ₁) (blockEmb K 2 1 4 3 0 (by norm_num) u)) =
      θa u
    rw [hβ, hD₄_0]
    rw [← hα₁_eq]
    exact DFunLike.congr_fun hα₁ u
  · ext u
    have hβ := qTwoSixExt_diagField_blockEmb hK D₄ σ₁ 1 (by norm_num) u
    change κ ((qTwoSixExt_diagField hK D₄ σ₁) (blockEmb K 2 1 4 3 1 (by norm_num) u)) =
      θb u
    rw [hβ, hD₄_1]
    rw [qTwoSixExt_diagField_smul hK c d₂ σ₁]
    rw [hσ_eq]
    rw [← hα₂_eq]
    exact DFunLike.congr_fun hα₂ u

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
