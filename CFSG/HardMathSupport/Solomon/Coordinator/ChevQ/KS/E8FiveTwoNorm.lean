module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoConjX
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FivePositioning
public import CFSG.Mathlib.GroupTheory.NormalizerLinearCoordinates
public import CFSG.Mathlib.LinearAlgebra.Matrix.SL3FivePointStabilizer

public noncomputable section

open Matrix
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

variable {L : Type} [Field L] [IsAlgClosed L]


section PointAction

open CFSG.GroupTheory.SL3Five

theorem exists_pointStabilizer_action_of_nontoral {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b : ModGL Tag.E8 L} (hamem : a ∈ mulSub L) (hbmem : b ∈ mulSub L)
    (hbasis : CubeBasis (griessZ hζ) a b)
    (hnt : ¬ ∃ x ∈ adjointGroup Tag.E8 L,
      ∀ e ∈ Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)),
        x⁻¹ * e * x ∈ torusGroup Tag.E8 L)
    (g : pointStabilizer) :
    ∃ γ ∈ mulSub L,
      γ * griessZ hζ * γ⁻¹ = griessZ hζ ∧
      γ * a * γ⁻¹ =
        griessZ hζ ^ ((g : SL3) 0 1).val * a ^ ((g : SL3) 1 1).val *
          b ^ ((g : SL3) 2 1).val ∧
      γ * b * γ⁻¹ =
        griessZ hζ ^ ((g : SL3) 0 2).val * a ^ ((g : SL3) 1 2).val *
          b ^ ((g : SL3) 2 2).val := by
  have h5 : (5 : L) ≠ 0 := by
    haveI : NeZero (5 : L) := hζ.neZero'
    exact NeZero.ne (5 : L)
  have hza : griessZ hζ * a = a * griessZ hζ := hbasis.comm_ab.eq
  have hzb : griessZ hζ * b = b * griessZ hζ := hbasis.comm_ac.eq
  have hcomm : a * b = b * a := hbasis.comm_bc.eq
  have ha5 : a ^ 5 = 1 := hbasis.pow_b
  have hb5 : b ^ 5 = 1 := hbasis.pow_c
  obtain ⟨Y, U, Y', U', ha, hb, hYnc⟩ :=
    nc_lifts_of_nontoral h5 hζ hamem hbmem hcomm ha5 hb5 hza hzb hnt
  obtain ⟨A, r, hg_eq⟩ := eq_blockDiag_mul_rowTranslation g.2
  obtain ⟨γSL2, hγSL2mem, hγSL2z, hγSL2a, hγSL2b⟩ :=
    exists_sl2_action_of_noncommuting_A_lifts hζ ha hb hcomm ha5 hb5 hYnc A
  obtain ⟨γb, hγbmem, hγbz, hγba, hγbb⟩ :=
    exists_central_shear_of_noncommuting_A_lifts hζ ha hb hcomm hYnc (r 1).val
  have hYnc' : Y' * Y ≠ Y * Y' := fun h => hYnc h.symm
  obtain ⟨γa, hγamem, hγaz, hγab, hγaa⟩ :=
    exists_central_shear_of_noncommuting_A_lifts hζ
      (a := b) (b := a) (Y := Y') (U := U') (Y' := Y) (U' := U)
      hb ha hcomm.symm hYnc' (r 0).val
  let γrow : ModGL Tag.E8 L := γa * γb
  have hγrowmem : γrow ∈ mulSub L := by
    dsimp only [γrow]
    exact mul_mem hγamem hγbmem
  have hγrowz : γrow * griessZ hζ * γrow⁻¹ = griessZ hζ := by
    dsimp only [γrow]
    calc (γa * γb) * griessZ hζ * (γa * γb)⁻¹
        = γa * (γb * griessZ hζ * γb⁻¹) * γa⁻¹ := by group
      _ = γa * griessZ hζ * γa⁻¹ := by rw [hγbz]
      _ = griessZ hζ := hγaz
  have hγrowa : γrow * a * γrow⁻¹ = griessZ hζ ^ (r 0).val * a := by
    dsimp only [γrow]
    calc (γa * γb) * a * (γa * γb)⁻¹
        = γa * (γb * a * γb⁻¹) * γa⁻¹ := by group
      _ = γa * a * γa⁻¹ := by rw [hγba]
      _ = griessZ hζ ^ (r 0).val * a := hγaa
  have hγa_zpow : γa * griessZ hζ ^ (r 1).val * γa⁻¹ =
      griessZ hζ ^ (r 1).val := by
    rw [← conj_pow, hγaz]
  have hγrowb : γrow * b * γrow⁻¹ = griessZ hζ ^ (r 1).val * b := by
    dsimp only [γrow]
    calc (γa * γb) * b * (γa * γb)⁻¹
        = γa * (γb * b * γb⁻¹) * γa⁻¹ := by group
      _ = γa * (griessZ hζ ^ (r 1).val * b) * γa⁻¹ := by rw [hγbb]
      _ = (γa * griessZ hζ ^ (r 1).val * γa⁻¹) *
            (γa * b * γa⁻¹) := by group
      _ = griessZ hζ ^ (r 1).val * (γa * b * γa⁻¹) := by rw [hγa_zpow]
      _ = griessZ hζ ^ (r 1).val * b := by rw [hγab]
  let γ : ModGL Tag.E8 L := γSL2 * γrow
  have hγmem : γ ∈ mulSub L := by
    dsimp only [γ]
    exact mul_mem hγSL2mem hγrowmem
  have hγz : γ * griessZ hζ * γ⁻¹ = griessZ hζ := by
    dsimp only [γ]
    calc (γSL2 * γrow) * griessZ hζ * (γSL2 * γrow)⁻¹
        = γSL2 * (γrow * griessZ hζ * γrow⁻¹) * γSL2⁻¹ := by group
      _ = γSL2 * griessZ hζ * γSL2⁻¹ := by rw [hγrowz]
      _ = griessZ hζ := hγSL2z
  have hγSL2_zpow_a : γSL2 * griessZ hζ ^ (r 0).val * γSL2⁻¹ =
      griessZ hζ ^ (r 0).val := by
    rw [← conj_pow, hγSL2z]
  have hγa : γ * a * γ⁻¹ =
      griessZ hζ ^ (r 0).val * a ^ (A 0 0).val * b ^ (A 1 0).val := by
    dsimp only [γ]
    calc (γSL2 * γrow) * a * (γSL2 * γrow)⁻¹
        = γSL2 * (γrow * a * γrow⁻¹) * γSL2⁻¹ := by group
      _ = γSL2 * (griessZ hζ ^ (r 0).val * a) * γSL2⁻¹ := by rw [hγrowa]
      _ = (γSL2 * griessZ hζ ^ (r 0).val * γSL2⁻¹) *
            (γSL2 * a * γSL2⁻¹) := by group
      _ = griessZ hζ ^ (r 0).val * (γSL2 * a * γSL2⁻¹) := by rw [hγSL2_zpow_a]
      _ = griessZ hζ ^ (r 0).val * (a ^ (A 0 0).val * b ^ (A 1 0).val) := by
            rw [hγSL2a]
      _ = griessZ hζ ^ (r 0).val * a ^ (A 0 0).val * b ^ (A 1 0).val := by group
  have hγSL2_zpow_b : γSL2 * griessZ hζ ^ (r 1).val * γSL2⁻¹ =
      griessZ hζ ^ (r 1).val := by
    rw [← conj_pow, hγSL2z]
  have hγb : γ * b * γ⁻¹ =
      griessZ hζ ^ (r 1).val * a ^ (A 0 1).val * b ^ (A 1 1).val := by
    dsimp only [γ]
    calc (γSL2 * γrow) * b * (γSL2 * γrow)⁻¹
        = γSL2 * (γrow * b * γrow⁻¹) * γSL2⁻¹ := by group
      _ = γSL2 * (griessZ hζ ^ (r 1).val * b) * γSL2⁻¹ := by rw [hγrowb]
      _ = (γSL2 * griessZ hζ ^ (r 1).val * γSL2⁻¹) *
            (γSL2 * b * γSL2⁻¹) := by group
      _ = griessZ hζ ^ (r 1).val * (γSL2 * b * γSL2⁻¹) := by rw [hγSL2_zpow_b]
      _ = griessZ hζ ^ (r 1).val * (a ^ (A 0 1).val * b ^ (A 1 1).val) := by
            rw [hγSL2b]
      _ = griessZ hζ ^ (r 1).val * a ^ (A 0 1).val * b ^ (A 1 1).val := by group
  have hg01 : ((g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 1 = r 0 := by
    rw [hg_eq]
    simp [blockDiagSL_coe, rowTranslationSL_coe, CFSG.GroupTheory.SL3Five.blockDiag, rowTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ]
  have hg11 : ((g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 = A 0 0 := by
    rw [hg_eq]
    simp [blockDiagSL_coe, rowTranslationSL_coe, CFSG.GroupTheory.SL3Five.blockDiag, rowTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ]
  have hg21 : ((g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1 = A 1 0 := by
    rw [hg_eq]
    simp [blockDiagSL_coe, rowTranslationSL_coe, CFSG.GroupTheory.SL3Five.blockDiag, rowTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ]
  have hg02 : ((g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 2 = r 1 := by
    rw [hg_eq]
    simp [blockDiagSL_coe, rowTranslationSL_coe, CFSG.GroupTheory.SL3Five.blockDiag, rowTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ]
  have hg12 : ((g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 = A 0 1 := by
    rw [hg_eq]
    simp [blockDiagSL_coe, rowTranslationSL_coe, CFSG.GroupTheory.SL3Five.blockDiag, rowTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ]
  have hg22 : ((g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 = A 1 1 := by
    rw [hg_eq]
    simp [blockDiagSL_coe, rowTranslationSL_coe, CFSG.GroupTheory.SL3Five.blockDiag, rowTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨γ, hγmem, hγz, ?_, ?_⟩
  · rw [hγa, hg01, hg11, hg21]
  · rw [hγb, hg02, hg12, hg22]


end PointAction

theorem det_eq_one_of_actual_fix_z
    {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {a b : ModGL Tag.E8 L}
    (ha : a ∈ mulSub L) (hb : b ∈ mulSub L)
    (hbas : CubeBasis (griessZ hζ) a b)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L)
    {γ : ModGL Tag.E8 L} (hγ : γ ∈ adjointGroup Tag.E8 L)
    (hγz : γ * griessZ hζ * γ⁻¹ = griessZ hζ)
    (M : GL (Fin 3) (ZMod 5)) (hMe0 : M • CFSG.GroupTheory.SL3Five.e0 =
      CFSG.GroupTheory.SL3Five.e0)
    (hγa : γ * a * γ⁻¹ = griessZ hζ ^ (M 0 1).val * a ^ (M 1 1).val * b ^ (M 2 1).val)
    (hγb : γ * b * γ⁻¹ = griessZ hζ ^ (M 0 2).val * a ^ (M 1 2).val * b ^ (M 2 2).val) :
    (M : Matrix (Fin 3) (Fin 3) (ZMod 5)).det = 1 := by
  have h5 : (5 : L) ≠ 0 := by
    haveI : NeZero (5 : L) := hζ.neZero'
    exact NeZero.ne (5 : L)
  obtain ⟨Y, U, Y', U', hYa, hYb, hnc⟩ := nc_lifts_of_nontoral h5 hζ ha hb
    hbas.comm_bc.eq hbas.pow_b hbas.pow_c hbas.comm_ab.eq hbas.comm_ac.eq hnt
  have hγmul : γ ∈ mulSub L := centralizer_le_mulSub hζ hγ (by
    have h := congrArg (fun x : ModGL Tag.E8 L => x * γ) hγz
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h)
  have hdet := FixZDet.point_stabilizer_det_eq_one hζ hYa hYb
    hbas.comm_bc.eq hnc hγmul hγa hγb
  simp only [ZMod.natCast_zmod_val] at hdet
  have hcol : ∀ i : Fin 3, M i 0 = (CFSG.GroupTheory.SL3Five.e0 i) := by
    intro i
    have h := congrFun hMe0 i
    simpa [CFSG.GroupTheory.SL3Five.e0, Units.smul_def, Matrix.smul_eq_mulVec,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have h00 : M 0 0 = 1 := by simpa [CFSG.GroupTheory.SL3Five.e0] using hcol 0
  have h10 : M 1 0 = 0 := by simpa [CFSG.GroupTheory.SL3Five.e0] using hcol 1
  have h20 : M 2 0 = 0 := by simpa [CFSG.GroupTheory.SL3Five.e0] using hcol 2
  rw [Matrix.det_fin_three]
  simp only [h00, h10, h20, one_mul, mul_zero, zero_mul, sub_zero, add_zero]
  convert hdet using 1 <;> ring

section LinearImage

open CFSG.GroupTheory.SL3Five CFSG.GroupTheory.NormalizerLinearCoordinates

local notation "F5" => ZMod 5
local notation "V3" => Fin 3 → ZMod 5


theorem actual_cube_normalizer_perfect
    (F : Subgroup (adjointGroup Tag.E8 L))
    (e : F ≃* Multiplicative V3)
    {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b : ModGL Tag.E8 L}
    (hcl : Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) =
      F.map (adjointGroup Tag.E8 L).subtype)
    (hbasis : Two.CubeBasis (griessZ hζ) a b)
    (himage : F.map (adjointGroup Tag.E8 L).subtype ≤ Two.mulSub L)
    (hnt : ¬ ∃ x ∈ adjointGroup Tag.E8 L,
      ∀ y ∈ Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)),
        x⁻¹ * y * x ∈ torusGroup Tag.E8 L)
    (hcoord : ∀ v : V3,
      ((e.symm (Multiplicative.ofAdd v) : F) : ModGL Tag.E8 L) =
        griessZ hζ ^ (v 0).val * a ^ (v 1).val * b ^ (v 2).val)
    (hmove : ∃ n : Subgroup.normalizer (F : Set (adjointGroup Tag.E8 L)),
      ((n : adjointGroup Tag.E8 L) : ModGL Tag.E8 L) * griessZ hζ *
        ((n : adjointGroup Tag.E8 L) : ModGL Tag.E8 L)⁻¹ = a) :
    Group.IsPerfect F.normalizerMonoidHom.range := by
  classical
  let x : Fin 3 → F := fun i => e.symm (Multiplicative.ofAdd (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis i))
  have hx : ∀ i, e (x i) = Multiplicative.ofAdd (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis i) := by
    intro i
    exact e.apply_symm_apply _
  have haxis0 : ((x 0 : F) : ModGL Tag.E8 L) = griessZ hζ := by
    have h0 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (0 : Fin 3) : V3) 0 = 1 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have h1 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (0 : Fin 3) : V3) 1 = 0 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have h2 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (0 : Fin 3) : V3) 2 = 0 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    rw [hcoord (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0), h0, h1, h2]
    norm_num [ZMod.val_one_eq_one_mod]
  have haxis1 : ((x 1 : F) : ModGL Tag.E8 L) = a := by
    have h0 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (1 : Fin 3) : V3) 0 = 0 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have h1 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (1 : Fin 3) : V3) 1 = 1 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have h2 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (1 : Fin 3) : V3) 2 = 0 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    rw [hcoord (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1), h0, h1, h2]
    norm_num [ZMod.val_one_eq_one_mod]
  have haxis2 : ((x 2 : F) : ModGL Tag.E8 L) = b := by
    have h0 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (2 : Fin 3) : V3) 0 = 0 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have h1 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (2 : Fin 3) : V3) 1 = 0 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have h2 : (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis (2 : Fin 3) : V3) 2 = 1 := by simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    rw [hcoord (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 2), h0, h1, h2]
    norm_num [ZMod.val_one_eq_one_mod]
  have hgen : Subgroup.closure (Set.range x) = ⊤ := by
    let φ : F →* ModGL Tag.E8 L := (adjointGroup Tag.E8 L).subtype.comp F.subtype
    have hφ : Function.Injective φ := by
      simpa only [φ, MonoidHom.coe_comp, Function.comp_apply] using
        (Subgroup.subtype_injective (adjointGroup Tag.E8 L)).comp
          (Subgroup.subtype_injective F)
    have hmap : (Subgroup.closure (Set.range x)).map φ =
        Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨i, ⟨j, rfl⟩, rfl⟩
        fin_cases j
        · change φ (x 0) ∈ ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L))
          have h : φ (x 0) = griessZ hζ := by
            simpa only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
              Function.comp_apply, Subgroup.coe_subtype] using haxis0
          rw [h]
          simp
        · change φ (x 1) ∈ ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L))
          have h : φ (x 1) = a := by
            simpa only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
              Function.comp_apply, Subgroup.coe_subtype] using haxis1
          rw [h]
          simp
        · change φ (x 2) ∈ ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L))
          have h : φ (x 2) = b := by
            simpa only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
              Function.comp_apply, Subgroup.coe_subtype] using haxis2
          rw [h]
          simp
      · intro hy
        rcases hy with rfl | rfl | rfl
        · refine ⟨x 0, ⟨0, rfl⟩, ?_⟩
          simpa only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
            Function.comp_apply, Subgroup.coe_subtype] using haxis0
        · refine ⟨x 1, ⟨1, rfl⟩, ?_⟩
          simpa only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
            Function.comp_apply, Subgroup.coe_subtype] using haxis1
        · refine ⟨x 2, ⟨2, rfl⟩, ?_⟩
          simpa only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
            Function.comp_apply, Subgroup.coe_subtype] using haxis2
    have hrange : φ.range = F.map (adjointGroup Tag.E8 L).subtype := by
      dsimp only [φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have htop : (⊤ : Subgroup F).map φ = F.map (adjointGroup Tag.E8 L).subtype := by
      rw [Subgroup.map_top, hrange]
    exact Subgroup.map_injective hφ (hmap.trans (hcl.trans htop.symm))

  have ha : a ∈ Two.mulSub L := by
    apply himage
    rw [← hcl]
    exact Subgroup.subset_closure (by simp)
  have hb : b ∈ Two.mulSub L := by
    apply himage
    rw [← hcl]
    exact Subgroup.subset_closure (by simp)
  have hlower : ∀ g : pointStabilizer,
      Matrix.SpecialLinearGroup.toGL (g : SL3) ∈ H F e := by
    intro g
    obtain ⟨γ, hγmem, hγz, hγa, hγb⟩ :=
      Two.exists_pointStabilizer_action_of_nontoral (L := L) hζ ha hb hbasis hnt g
    let γadj : adjointGroup Tag.E8 L := ⟨γ, Two.mulSub_le_adjointGroup hγmem⟩
    have hfix0 : ((Matrix.SpecialLinearGroup.toGL (g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ
        CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0) =
        CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0 := by
      have hg : (g : SL3) • e0 = e0 :=
        MulAction.mem_stabilizer_iff.mp g.2
      have hg' : ((g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ e0 =
          e0 := by
        simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using hg
      simpa [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis, e0,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hg'
    have hcol1 : ((Matrix.SpecialLinearGroup.toGL (g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ
        CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1) =
        fun j => ((g : SL3) j 1) := by
      ext j
      simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hcol2 : ((Matrix.SpecialLinearGroup.toGL (g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ
        CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 2) =
        fun j => ((g : SL3) j 2) := by
      ext j
      simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hconj : ∀ i : Fin 3,
        γadj * (x i : adjointGroup Tag.E8 L) * γadj⁻¹ =
          ((coordTarget F e (Matrix.SpecialLinearGroup.toGL (g : SL3)) i : F) :
            adjointGroup Tag.E8 L) := by
      intro i
      fin_cases i
      · apply (Subgroup.subtype_injective (adjointGroup Tag.E8 L))
        change γ * ((x 0 : F) : ModGL Tag.E8 L) * γ⁻¹ =
          ((coordTarget F e (Matrix.SpecialLinearGroup.toGL (g : SL3)) 0 : F) :
            ModGL Tag.E8 L)
        rw [haxis0, coordTarget]
        change γ * griessZ hζ * γ⁻¹ =
          ((e.symm (Multiplicative.ofAdd
            ((Matrix.SpecialLinearGroup.toGL (g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ
              CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0)) : F) : ModGL Tag.E8 L)
        rw [hfix0, hcoord (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0)]
        simpa [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis, ZMod.val_one_eq_one_mod] using hγz
      · apply (Subgroup.subtype_injective (adjointGroup Tag.E8 L))
        change γ * ((x 1 : F) : ModGL Tag.E8 L) * γ⁻¹ =
          ((coordTarget F e (Matrix.SpecialLinearGroup.toGL (g : SL3)) 1 : F) :
            ModGL Tag.E8 L)
        rw [haxis1, coordTarget]
        change γ * a * γ⁻¹ =
          ((e.symm (Multiplicative.ofAdd
            ((Matrix.SpecialLinearGroup.toGL (g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ
              CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1)) : F) : ModGL Tag.E8 L)
        rw [hcol1, hcoord (fun j => ((g : SL3) j 1))]
        simpa using hγa
      · apply (Subgroup.subtype_injective (adjointGroup Tag.E8 L))
        change γ * ((x 2 : F) : ModGL Tag.E8 L) * γ⁻¹ =
          ((coordTarget F e (Matrix.SpecialLinearGroup.toGL (g : SL3)) 2 : F) :
            ModGL Tag.E8 L)
        rw [haxis2, coordTarget]
        change γ * b * γ⁻¹ =
          ((e.symm (Multiplicative.ofAdd
            ((Matrix.SpecialLinearGroup.toGL (g : SL3) : Matrix (Fin 3) (Fin 3) F5) *ᵥ
              CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 2)) : F) : ModGL Tag.E8 L)
        rw [hcol2, hcoord (fun j => ((g : SL3) j 2))]
        simpa using hγb
    obtain ⟨hg, hrho⟩ :=
      exists_normalizer_rho_eq_of_conj_generators F e x
        (Matrix.SpecialLinearGroup.toGL (g : SL3)) γadj hx hgen hconj
    change Matrix.SpecialLinearGroup.toGL (g : SL3) ∈ (rho F e).range
    exact ⟨⟨γadj, hg⟩, hrho⟩

  have hupper : ∀ M ∈ H F e, M • e0 = e0 →
      (M : Matrix (Fin 3) (Fin 3) F5).det = 1 := by
    intro M hM hMe0
    change M ∈ (rho F e).range at hM
    obtain ⟨n, hrho⟩ := MonoidHom.mem_range.mp hM
    let γ : ModGL Tag.E8 L := (n : adjointGroup Tag.E8 L)
    have hγ : γ ∈ adjointGroup Tag.E8 L := (n : adjointGroup Tag.E8 L).2
    have hnorm_coe (y : F) :
        ((F.normalizerMonoidHom n y : F) : ModGL Tag.E8 L) =
          γ * ((y : F) : ModGL Tag.E8 L) * γ⁻¹ := rfl
    let v0 : V3 := (M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0
    let v1 : V3 := (M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1
    let v2 : V3 := (M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 2
    have hM0 : v0 = (e (F.normalizerMonoidHom n (x 0))).toAdd := by
      change ((M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0) =
        (e (F.normalizerMonoidHom n (x 0))).toAdd
      have h := rho_mulVec F e n (x 0)
      rw [hx 0, hrho] at h
      simpa only [toAdd_ofAdd] using h
    have hMe0' : v0 = CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0 := by
      change ((M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0) = CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0
      simpa [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis, e0, Units.smul_def, Matrix.smul_eq_mulVec] using hMe0
    have hM0_toAdd : (e (F.normalizerMonoidHom n (x 0))).toAdd = CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0 :=
      hM0.symm.trans hMe0'
    have hn0 : F.normalizerMonoidHom n (x 0) = x 0 := by
      apply e.injective
      have hEq : e (F.normalizerMonoidHom n (x 0)) =
          Multiplicative.ofAdd (CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0) := by
        simpa only [ofAdd_toAdd] using congrArg Multiplicative.ofAdd hM0_toAdd
      rw [hEq, hx 0]
    have hγz : γ * griessZ hζ * γ⁻¹ = griessZ hζ := by
      have h := hnorm_coe (x 0)
      rw [hn0, haxis0] at h
      exact h.symm
    have hcolM1 : v1 = fun j => ((M : Matrix (Fin 3) (Fin 3) F5) j 1) := by
      change ((M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1) =
        fun j => ((M : Matrix (Fin 3) (Fin 3) F5) j 1)
      ext j
      simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have hcolM2 : v2 = fun j => ((M : Matrix (Fin 3) (Fin 3) F5) j 2) := by
      change ((M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 2) =
        fun j => ((M : Matrix (Fin 3) (Fin 3) F5) j 2)
      ext j
      simp [CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis]
    have hM1 : v1 = (e (F.normalizerMonoidHom n (x 1))).toAdd := by
      change ((M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1) =
        (e (F.normalizerMonoidHom n (x 1))).toAdd
      have h := rho_mulVec F e n (x 1)
      rw [hx 1, hrho] at h
      simpa only [toAdd_ofAdd] using h
    have hn1 : F.normalizerMonoidHom n (x 1) =
        e.symm (Multiplicative.ofAdd v1) := by
      have hEq : e (F.normalizerMonoidHom n (x 1)) =
          Multiplicative.ofAdd v1 := by
        simpa only [ofAdd_toAdd] using (congrArg Multiplicative.ofAdd hM1).symm
      simpa only [MulEquiv.symm_apply_apply] using congrArg e.symm hEq
    have hn1_actual : ((F.normalizerMonoidHom n (x 1) : F) : ModGL Tag.E8 L) =
        γ * a * γ⁻¹ := by
      rw [hnorm_coe (x 1), haxis1]
    have hγa : γ * a * γ⁻¹ =
        griessZ hζ ^ ((M : Matrix (Fin 3) (Fin 3) F5) 0 1).val *
          a ^ ((M : Matrix (Fin 3) (Fin 3) F5) 1 1).val *
          b ^ ((M : Matrix (Fin 3) (Fin 3) F5) 2 1).val := by
      rw [← hn1_actual]
      calc ((F.normalizerMonoidHom n (x 1) : F) : ModGL Tag.E8 L)
          = ((e.symm (Multiplicative.ofAdd v1) : F) : ModGL Tag.E8 L) := by rw [hn1]
        _ = griessZ hζ ^ (v1 0).val * a ^ (v1 1).val * b ^ (v1 2).val := hcoord v1
        _ = griessZ hζ ^ ((M : Matrix (Fin 3) (Fin 3) F5) 0 1).val *
              a ^ ((M : Matrix (Fin 3) (Fin 3) F5) 1 1).val *
              b ^ ((M : Matrix (Fin 3) (Fin 3) F5) 2 1).val := by
            rw [hcolM1]
    have hM2 : v2 = (e (F.normalizerMonoidHom n (x 2))).toAdd := by
      change ((M : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 2) =
        (e (F.normalizerMonoidHom n (x 2))).toAdd
      have h := rho_mulVec F e n (x 2)
      rw [hx 2, hrho] at h
      simpa only [toAdd_ofAdd] using h
    have hn2 : F.normalizerMonoidHom n (x 2) =
        e.symm (Multiplicative.ofAdd v2) := by
      have hEq : e (F.normalizerMonoidHom n (x 2)) =
          Multiplicative.ofAdd v2 := by
        simpa only [ofAdd_toAdd] using (congrArg Multiplicative.ofAdd hM2).symm
      simpa only [MulEquiv.symm_apply_apply] using congrArg e.symm hEq
    have hn2_actual : ((F.normalizerMonoidHom n (x 2) : F) : ModGL Tag.E8 L) =
        γ * b * γ⁻¹ := by
      rw [hnorm_coe (x 2), haxis2]
    have hγb : γ * b * γ⁻¹ =
        griessZ hζ ^ ((M : Matrix (Fin 3) (Fin 3) F5) 0 2).val *
          a ^ ((M : Matrix (Fin 3) (Fin 3) F5) 1 2).val *
          b ^ ((M : Matrix (Fin 3) (Fin 3) F5) 2 2).val := by
      rw [← hn2_actual]
      calc ((F.normalizerMonoidHom n (x 2) : F) : ModGL Tag.E8 L)
          = ((e.symm (Multiplicative.ofAdd v2) : F) : ModGL Tag.E8 L) := by rw [hn2]
        _ = griessZ hζ ^ (v2 0).val * a ^ (v2 1).val * b ^ (v2 2).val := hcoord v2
        _ = griessZ hζ ^ ((M : Matrix (Fin 3) (Fin 3) F5) 0 2).val *
              a ^ ((M : Matrix (Fin 3) (Fin 3) F5) 1 2).val *
              b ^ ((M : Matrix (Fin 3) (Fin 3) F5) 2 2).val := by
            rw [hcolM2]
    exact Two.det_eq_one_of_actual_fix_z (L := L) hζ ha hb hbasis hnt
      (γ := γ) hγ hγz M hMe0 hγa hγb

  have hφinj : Function.Injective (fun y : F => ((y : F) : ModGL Tag.E8 L)) := by
    intro u v huv
    apply Subtype.ext
    apply (Subgroup.subtype_injective (adjointGroup Tag.E8 L))
    exact huv
  have hmoveH : ∃ m ∈ H F e, m • e0 = e1 := by
    rcases hmove with ⟨n, hn⟩
    let m : GL (Fin 3) F5 := rho F e n
    have hnorm_coe0 : ((F.normalizerMonoidHom n (x 0) : F) : ModGL Tag.E8 L) =
        ((n : adjointGroup Tag.E8 L) : ModGL Tag.E8 L) * ((x 0 : F) : ModGL Tag.E8 L) *
          ((n : adjointGroup Tag.E8 L) : ModGL Tag.E8 L)⁻¹ := rfl
    have hn_coe : ((F.normalizerMonoidHom n (x 0) : F) : ModGL Tag.E8 L) = a := by
      rw [hnorm_coe0, haxis0]
      exact hn
    have hnx0 : F.normalizerMonoidHom n (x 0) = x 1 :=
      hφinj (hn_coe.trans haxis1.symm)
    have hcoord_nx0 : (e (F.normalizerMonoidHom n (x 0))).toAdd = CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1 := by
      rw [hnx0, hx 1]
      simp
    have hmat : ((m : GL (Fin 3) F5) : Matrix (Fin 3) (Fin 3) F5) *ᵥ CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 0 =
        CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis 1 := by
      have h := rho_mulVec F e n (x 0)
      rw [hx 0] at h
      rw [hcoord_nx0] at h
      simpa only [toAdd_ofAdd] using h
    refine ⟨m, ?_, ?_⟩
    · change m ∈ (rho F e).range
      exact ⟨n, rfl⟩
    · simpa [m, CFSG.GroupTheory.NormalizerLinearCoordinates.stdBasis, e0, e1, Units.smul_def, Matrix.smul_eq_mulVec] using hmat
  have htrans : ∀ v : V3, v ≠ 0 → ∃ g ∈ H F e, g • e0 = v :=
    transitive_of_pointStabilizer_of_move (H F e) hlower hmoveH
  have hHperf : Group.IsPerfect (H F e) :=
    isPerfect_of_linear_image (H F e) hlower hupper htrans
  exact isPerfect_normalizer_range_of_isPerfect_H F e hHperf


end LinearImage

theorem isPerfect_normalizerRange_of_nontoral_cube
    (F : Subgroup (adjointGroup Tag.E8 L)) [Finite F]
    (hF : CFSG.Open.IsElemAbelian 5 F)
    (hNT : ¬ CFSG.StandardType.ExcFramesHalf.IsToralSubgroup Tag.E8 L
      (F.map (adjointGroup Tag.E8 L).subtype))
    {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {a b : ModGL Tag.E8 L}
    (himage : F.map (adjointGroup Tag.E8 L).subtype ≤ Two.mulSub L)
    (hbasis : Two.CubeBasis (griessZ hζ) a b)
    (hcl : Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) =
      F.map (adjointGroup Tag.E8 L).subtype) :
    Group.IsPerfect F.normalizerMonoidHom.range := by
  have h5 : (5 : L) ≠ 0 := by
    haveI : NeZero (5 : L) := hζ.neZero'
    exact NeZero.ne (5 : L)
  let e := Two.CubeCoordinates.cubeCoordEquivOfMap F (adjointGroup Tag.E8 L).subtype
    (adjointGroup Tag.E8 L).subtype_injective hbasis hcl
  have hcoord (v : Fin 3 → ZMod 5) :
      ((e.symm (Multiplicative.ofAdd v) : F) : ModGL Tag.E8 L) =
        griessZ hζ ^ (v 0).val * a ^ (v 1).val * b ^ (v 2).val :=
    Two.CubeCoordinates.cubeCoordEquivOfMap_symm_apply F
      (adjointGroup Tag.E8 L).subtype (adjointGroup Tag.E8 L).subtype_injective hbasis hcl v
  obtain ⟨γ, hγ, hγmap, hγz⟩ :=
    exists_normalizer_mover_of_cube
      h5 hζ himage (hF.map (adjointGroup Tag.E8 L).subtype) hbasis hcl.symm hNT
  have hγnorm : (⟨γ, hγ⟩ : adjointGroup Tag.E8 L) ∈
      Subgroup.normalizer (F : Set (adjointGroup Tag.E8 L)) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change F.map (MulAut.conj (⟨γ, hγ⟩ : adjointGroup Tag.E8 L)).toMonoidHom = F
    apply Subgroup.map_injective (adjointGroup Tag.E8 L).subtype_injective
    rw [Subgroup.map_map]
    have hcomp : (adjointGroup Tag.E8 L).subtype.comp
        (MulAut.conj (⟨γ, hγ⟩ : adjointGroup Tag.E8 L)).toMonoidHom =
        (MulAut.conj γ).toMonoidHom.comp (adjointGroup Tag.E8 L).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hγmap]
  exact actual_cube_normalizer_perfect F e hζ
    hcl hbasis himage (by rwa [hcl]) hcoord ⟨⟨⟨γ, hγ⟩, hγnorm⟩, hγz⟩


end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {L : Type} [Field L] [IsAlgClosed L]


theorem universal_nonToral_normalizer_isPerfect
    [CharP L 2]
    (E : Subgroup (adjointGroup Tag.E8 L)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    (hNT : ¬ CFSG.StandardType.ExcFramesHalf.IsToralSubgroup Tag.E8 L
      (E.map (adjointGroup Tag.E8 L).subtype))
    (hcard : 5 ^ 3 ≤ Nat.card E) :
    Group.IsPerfect E.normalizerMonoidHom.range := by
  apply universal_perfect_normalizer_transfer ?_ E hE hNT hcard
  intro F _ hF hFNT ζ hζ a b himage hbasis hcl
  exact Two.isPerfect_normalizerRange_of_nontoral_cube F hF hFNT hζ himage hbasis hcl


end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
