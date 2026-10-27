module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutL4
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinDefs
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.GH74.L5U5 Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem sl4_form_one [Finite F] (h2 : (2 : F) ≠ 0) (β : MulAut SL(4, F)) (σ : F ≃+* F)
    {B Bi : Matrix (Fin 4) (Fin 4) F} (hBBi : B * Bi = 1) (hBiB : Bi * B = 1)
    (hA : ∀ g : SL(4, F), (β g : Matrix (Fin 4) (Fin 4) F) =
      B * (g : Matrix (Fin 4) (Fin 4) F).map σ * Bi)
    (hfix : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) → β (slBlk F (a, b)) = slBlk F (a, b)) :
    ∃ c d : F, c ≠ 0 ∧ d ≠ 0 ∧ ∀ g : SL(4, F),
      (β g : Matrix (Fin 4) (Fin 4) F) = blkScalar c d * g * blkScalar c⁻¹ d⁻¹ := by
  have hfixM : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) →
      B * (blk4 (a : Matrix (Fin 2) (Fin 2) F) b).map σ * Bi =
        blk4 (a : Matrix (Fin 2) (Fin 2) F) b := by
    intro a b hab
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (hfix a b hab)
    simpa only [hA, coe_slBlk] using this
  have hσ : ∀ x : F, σ x = x := by
    intro x
    have ht := congrArg Matrix.trace (hfixM (GH74.Generic.companionSL x) 1 (Or.inr rfl))
    rw [Matrix.trace_mul_cycle, hBiB, Matrix.one_mul, Matrix.SpecialLinearGroup.coe_one] at ht
    have e1 : ((GH74.Generic.companionSL x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![x, -1; 1, 0] := rfl
    rw [e1, trace_blk4_one_map, trace_blk4_companion] at ht
    linear_combination ht
  obtain rfl : σ = RingEquiv.refl F := RingEquiv.ext hσ
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F, M.map (RingEquiv.refl F) = M := fun M => by
    ext; simp
  obtain ⟨c, d, hcd⟩ := exists_blkScalar_of_comm h2 (B := B) fun a b hab => by
    have := hfixM a b hab
    rw [hmap] at this
    calc B * blk4 (a : Matrix (Fin 2) (Fin 2) F) b =
        B * blk4 (a : Matrix (Fin 2) (Fin 2) F) b * Bi * B := by
          rw [Matrix.mul_assoc _ Bi, hBiB, Matrix.mul_one]
      _ = blk4 (a : Matrix (Fin 2) (Fin 2) F) b * B := by rw [this]
  obtain ⟨hc, hd, hBi'⟩ := blkScalar_inv_eq (c := c) (d := d) (N := Bi) (by rw [← hcd]; exact hBBi)
  exact ⟨c, d, hc, hd, fun g => by rw [hA, hmap, hcd, hBi']⟩

theorem sl4_form_two [Finite F] (h2 : (2 : F) ≠ 0) (β : MulAut SL(4, F)) (σ : F ≃+* F)
    {B Bi : Matrix (Fin 4) (Fin 4) F} (hBBi : B * Bi = 1) (hBiB : Bi * B = 1)
    (hA : ∀ g : SL(4, F), (β g : Matrix (Fin 4) (Fin 4) F) =
      B * ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).transpose.map σ * Bi)
    (hfix : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) → β (slBlk F (a, b)) = slBlk F (a, b)) :
    β * β = 1 := by
  have hinv : ∀ a b : SL(2, F), (((slBlk F (a, b))⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blk4 (adjugate (a : Matrix (Fin 2) (Fin 2) F)) (adjugate (b : Matrix (Fin 2) (Fin 2) F)) := by
    intro a b
    rw [← map_inv, Prod.inv_mk, coe_slBlk, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_inv]
  have hfixM : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) →
      B * ((blk4 (adjugate (a : Matrix (Fin 2) (Fin 2) F))
        (adjugate (b : Matrix (Fin 2) (Fin 2) F)))ᵀ).map σ * Bi =
        blk4 (a : Matrix (Fin 2) (Fin 2) F) b := by
    intro a b hab
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (hfix a b hab)
    simpa only [hA, hinv, coe_slBlk] using this
  have hσ : ∀ x : F, σ x = x := by
    intro x
    have ht := congrArg Matrix.trace (hfixM (GH74.Generic.companionSL x) 1 (Or.inr rfl))
    rw [Matrix.trace_mul_cycle, hBiB, Matrix.one_mul, blk4_transpose, blk4_map, trace_blk4,
      trace_map_two, trace_map_two, Matrix.trace_transpose, Matrix.trace_transpose,
      trace_adjugate_two, trace_adjugate_two, trace_blk4] at ht
    simp [GH74.Generic.companionSL, trace_fin_two] at ht
    linear_combination ht - map_ofNat σ 2
  obtain rfl : σ = RingEquiv.refl F := RingEquiv.ext hσ
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F, M.map (RingEquiv.refl F) = M := fun M => by
    ext; simp
  set S : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0] with hS
  set Si : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0] with hSi
  have hDiDm : blk4 Si Si * blk4 S S = 1 := by rw [blk4_mul, sInv_mul_sMat, blk4_one]
  have hDmDi : blk4 S S * blk4 Si Si = 1 := by rw [blk4_mul, sMat_mul_sInv, blk4_one]
  have htw : ∀ a b : SL(2, F), (blk4 (adjugate (a : Matrix (Fin 2) (Fin 2) F))
      (adjugate (b : Matrix (Fin 2) (Fin 2) F)))ᵀ =
      blk4 Si Si * blk4 (a : Matrix (Fin 2) (Fin 2) F) b * blk4 S S := by
    intro a b
    rw [blk4_transpose, ← sMat_adjugate, ← sMat_adjugate, blk4_mul, blk4_mul]
  obtain ⟨c, d, hcd⟩ := exists_blkScalar_of_comm h2 (B := B * blk4 Si Si) fun a b hab => by
    have := hfixM a b hab
    rw [hmap, htw] at this
    calc B * blk4 Si Si * blk4 (a : Matrix (Fin 2) (Fin 2) F) b =
        B * (blk4 Si Si * blk4 (a : Matrix (Fin 2) (Fin 2) F) b * blk4 S S) * Bi *
          (B * blk4 Si Si) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Bi B, hBiB, Matrix.one_mul, hDmDi, Matrix.mul_one]
      _ = blk4 (a : Matrix (Fin 2) (Fin 2) F) b * (B * blk4 Si Si) := by rw [this]
  obtain ⟨hc, hd, hCi⟩ := blkScalar_inv_eq (c := c) (d := d) (N := blk4 S S * Bi) (by
    rw [← hcd, Matrix.mul_assoc, ← Matrix.mul_assoc (blk4 Si Si), hDiDm, Matrix.one_mul, hBBi])
  have hBeq : B = blkScalar c d * blk4 S S := by
    rw [← hcd, Matrix.mul_assoc, hDiDm, Matrix.mul_one]
  have hBieq : Bi = blk4 Si Si * blkScalar c⁻¹ d⁻¹ := by
    rw [← hCi, ← Matrix.mul_assoc, hDiDm, Matrix.one_mul]
  have hCC : blkScalar c d * blkScalar c⁻¹ d⁻¹ = 1 := blkScalar_mul_inv hc hd
  have hP1 : B * Biᵀ = -1 := by
    rw [hBeq, hBieq, Matrix.transpose_mul, blkScalar_transpose, blk4_transpose, sInv_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (blk4 S S), ← blkScalar_comm_blk4, Matrix.mul_assoc,
      ← Matrix.mul_assoc (blkScalar c d), hCC, Matrix.one_mul, blk4_mul, sMat_sq, blk4_neg,
      blk4_one]
  have hP2 : Bᵀ * Bi = -1 := by
    rw [hBeq, hBieq, Matrix.transpose_mul, blkScalar_transpose, blk4_transpose, sMat_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (blkScalar c d), blkScalar_comm_blk4,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (blkScalar c d), hCC,
      Matrix.mul_one, blk4_mul, sInv_sq, blk4_neg, blk4_one]
  have hβinv : ∀ g : SL(4, F), ((β g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      B * (g : Matrix (Fin 4) (Fin 4) F)ᵀ * Bi := fun g => by rw [hA, inv_inv, hmap]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  show ((β (β g) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = g
  rw [hA, hmap, ← map_inv, hβinv, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  calc B * (Biᵀ * ((g : Matrix (Fin 4) (Fin 4) F) * Bᵀ)) * Bi =
      (B * Biᵀ) * (g : Matrix (Fin 4) (Fin 4) F) * (Bᵀ * Bi) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [hP1, hP2]; simp

theorem sl4_aut_dichotomy [Finite F] (h2 : (2 : F) ≠ 0) (β : MulAut SL(4, F))
    (hfix : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) → β (slBlk F (a, b)) = slBlk F (a, b)) :
    (∃ c d : F, c ≠ 0 ∧ d ≠ 0 ∧ ∀ g : SL(4, F),
      (β g : Matrix (Fin 4) (Fin 4) F) = blkScalar c d * g * blkScalar c⁻¹ d⁻¹) ∨ β * β = 1 := by
  obtain ⟨A, σ, hA⟩ :=
    RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (by norm_num : 3 ≤ 4) β
  have hBBi : (A : Matrix (Fin 4) (Fin 4) F) * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rcases hA with hA | hA
  · exact Or.inl (sl4_form_one h2 β σ hBBi hBiB hA hfix)
  · exact Or.inr (sl4_form_two h2 β σ hBBi hBiB hA hfix)

theorem sl4FrameOuterQ8Free_holds : SL4FrameOuterQ8Free := by
  intro F _ _ hF
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  set M := ModelData.lin F with hM
  let e : SL(4, F) ≃* ↥M.K4 := Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F
  have he : ∀ g : SL(4, F), (((e g : ↥M.K4) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) := fun g => rfl
  refine frameOuterQ8Free_of_dichotomy (blkTorus M.K4) (blkTorus_comm _) fun α h₂ h₄ => ?_
  let β : MulAut SL(4, F) := MulAut.congr e.symm α
  have hβ : ∀ g, β g = e.symm (α (e g)) := fun g => rfl
  have hfix : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) → β (slBlk F (a, b)) = slBlk F (a, b) := by
    rintro a b (rfl | rfl)
    · rw [hβ, h₄ _ (M.mem_J4.2 ⟨Matrix.SpecialLinearGroup.toGL b, ?_, Units.ext ?_⟩),
        e.symm_apply_apply]
      · show _ ∈ Assembly.LowTwoRank.StatedSL 2 F
        rw [Assembly.LowTwoRank.statedSL_eq_range_toGL]
        exact ⟨b, rfl⟩
      · rw [he, coe_slBlk, blkR_apply, coe_diagGL]
        rfl
    · rw [hβ, h₂ _ (M.mem_J2.2 ⟨Matrix.SpecialLinearGroup.toGL a, ?_, Units.ext ?_⟩),
        e.symm_apply_apply]
      · show _ ∈ Assembly.LowTwoRank.StatedSL 2 F
        rw [Assembly.LowTwoRank.statedSL_eq_range_toGL]
        exact ⟨a, rfl⟩
      · rw [he, coe_slBlk, blkL_apply, coe_diagGL]
        rfl
  rcases sl4_aut_dichotomy h2 β hfix with ⟨c, d, hc, hd, hcd⟩ | hsq
  · refine Or.inl ⟨c, d, hc, hd, fun x => ?_⟩
    have h1 := hcd (e.symm x)
    rw [hβ, e.apply_symm_apply] at h1
    rw [← he (e.symm (α x)), MulEquiv.apply_symm_apply] at h1
    rw [h1, ← he (e.symm x), MulEquiv.apply_symm_apply]
  · refine Or.inr (MulEquiv.ext fun x => ?_)
    have h1 := DFunLike.congr_fun hsq (e.symm x)
    simp only [MulAut.mul_apply, MulAut.one_apply, hβ, MulEquiv.apply_symm_apply] at h1
    rw [MulAut.mul_apply, MulAut.one_apply]
    simpa using congrArg e h1

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
