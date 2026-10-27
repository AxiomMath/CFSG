module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521Sig
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.E1521

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open scoped MatrixGroups

namespace D

theorem sigmaFixGen_conj {W : Type} [Group W] (K : Subgroup W) (σ β : MulAut W)
    (hβ : ∀ x ∈ K, β x = x) :
    sigmaFixGen K (β * σ * β⁻¹) = (sigmaFixGen K σ).map β.toMonoidHom := by
  have hβK : ∀ g : W, (Generic.conjSub g K).map β.toMonoidHom = Generic.conjSub (β g) K := by
    intro g
    ext y
    simp only [Generic.conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [MulAut.conj_apply, hβ k hk]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨g * k * g⁻¹, ⟨k, hk, rfl⟩, by simp [MulAut.conj_apply, hβ k hk]⟩
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨⟨g, rfl⟩, hfix⟩ := hM
    have e : Generic.conjSub g K = (Generic.conjSub (β⁻¹ g) K).map β.toMonoidHom := by
      rw [hβK, MulAut.apply_inv_self]
    show Generic.conjSub g K ≤ _
    rw [e]
    refine Subgroup.map_mono (le_iSup₂ (f := fun (M : Subgroup W)
      (_ : M ∈ {M : Subgroup W | M ∈ CoreAssembly.conjClass K ∧ ∀ x ∈ M, σ x = x}) => M)
      (Generic.conjSub (β⁻¹ g) K) ⟨⟨_, rfl⟩, fun x hx => ?_⟩)
    have hbx : β x ∈ Generic.conjSub g K := by
      rw [e]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h1 := hfix (β x) hbx
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    exact β.injective h1
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨⟨g, rfl⟩, hfix⟩ := hM
    show Generic.conjSub g K ≤ _
    rw [← Subgroup.map_le_iff_le_comap, hβK]
    refine le_iSup₂ (f := fun (M : Subgroup W)
      (_ : M ∈ {M : Subgroup W | M ∈ CoreAssembly.conjClass K ∧ ∀ x ∈ M, (β * σ * β⁻¹) x = x}) =>
        M) (Generic.conjSub (β g) K) ⟨⟨β g, rfl⟩, fun y hy => ?_⟩
    rw [← hβK] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hfix x hx]

variable {F : Type} [Field F]

theorem zero_add_three_le_four : 0 + 3 ≤ 4 := by norm_num

abbrev blk3 (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, A 0 2, 0; A 1 0, A 1 1, A 1 2, 0; A 2 0, A 2 1, A 2 2, 0; 0, 0, 0, 1]

theorem coe_blockSL_four_three (A : SL(3, F)) :
    ((blockSL F 4 3 0 zero_add_three_le_four A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blk3 A := by
  rw [WeakCT.coe_blockSL]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Phan.blockMat_apply]

theorem blk3_apply (A : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    blk3 A i.castSucc j.castSucc = A i j := by
  fin_cases i <;> fin_cases j <;> rfl

noncomputable abbrev iota3 (F : Type) [Field F] : SL(3, F) →* projectiveSL 4 F :=
  (proj 4 F).comp (blockSL F 4 3 0 zero_add_three_le_four)

noncomputable abbrev blockL (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  (iota3 F).range

theorem iota3_injective : Function.Injective (iota3 F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hA
  obtain ⟨c, -, hc⟩ := hA
  rw [coe_blockSL_four_three] at hc
  have hc33 : (c : F) = 1 := by simpa using (congrFun (congrFun hc 3) 3).symm
  rw [hc33, map_one] at hc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  have h := congrFun (congrFun hc i.castSucc) j.castSucc
  rw [blk3_apply] at h
  rw [h]
  simp [Matrix.one_apply, Fin.castSucc_inj]

theorem scalars_three_eq_bot [Finite F] (hF : Nat.card F = 3) : scalars 3 F = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc3, hcA⟩ := mem_scalars.mp hA
  have hc2 : (c : F) * c = 1 := card3_mul_self hF c.ne_zero
  have hc1 : (c : F) = 1 := by
    have h3 : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    calc (c : F) = c * (c * c) := by rw [hc2, mul_one]
      _ = c ^ 3 := by ring
      _ = 1 := h3
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hcA, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

noncomputable def projectiveSL3Equiv [Finite F] (hF : Nat.card F = 3) :
    projectiveSL 3 F ≃* SL(3, F) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_three_eq_bot hF)).trans QuotientGroup.quotientBot

noncomputable def blockLEquiv [Finite F] (hF : Nat.card F = 3) : ↥(blockL F) ≃* projectiveSL 3 F :=
  (MonoidHom.ofInjective iota3_injective).symm.trans (projectiveSL3Equiv hF).symm

theorem lieModel_blockL [Finite F] (hF : Nat.card F = 3) : LieModel ↥(blockL F) .PSL 3 3 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by norm_num, by simp, by simp⟩, F, inferInstance,
    inferInstance, hF.trans (pow_one 3).symm,
    ⟨(blockLEquiv hF).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F).symm.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F))⟩⟩

theorem isSimpleGroup_blockL [Finite F] (hF : Nat.card F = 3) : IsSimpleGroup ↥(blockL F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega)
      (Or.inl le_rfl)).2.1
  exact ((blockLEquiv hF).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      3 F).symm).isSimpleGroup

theorem d_mul_blk3 (A : Matrix (Fin 3) (Fin 3) F) :
    blk (1 : F) 1 0 0 (-1) * blk3 A = blk3 A * blk (1 : F) 1 0 0 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem conjAut_d_iota3 (A : SL(3, F)) : conjAut 4 F (dGL F) (iota3 F A) = iota3 F A := by
  show conjAut 4 F (dGL F) (proj 4 F (blockSL F 4 3 0 zero_add_three_le_four A)) =
    proj 4 F (blockSL F 4 3 0 zero_add_three_le_four A)
  refine conjAut_proj_eq_of_comm _ _ ?_
  rw [coe_dGL, coe_blockSL_four_three]
  exact d_mul_blk3 _

theorem conjAut_d_of_mem_blockL {y : projectiveSL 4 F} (hy : y ∈ blockL F) :
    conjAut 4 F (dGL F) y = y := by
  obtain ⟨A, rfl⟩ := hy
  exact conjAut_d_iota3 A

theorem dmd_apply (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4) :
    (blk (1 : F) 1 0 0 (-1) * M * blk (1 : F) 1 0 0 (-1)) i j =
      (if i = 3 then -1 else 1) * M i j * (if j = 3 then -1 else 1) := by
  have hd : blk (1 : F) 1 0 0 (-1) = Matrix.diagonal fun k => if k = 3 then -1 else 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem det_corner (a00 a01 a02 a10 a11 a12 a20 a21 a22 l : F) :
    (!![a00, a01, a02, 0; a10, a11, a12, 0; a20, a21, a22, 0; 0, 0, 0, l] :
      Matrix (Fin 4) (Fin 4) F).det =
      (!![a00, a01, a02; a10, a11, a12; a20, a21, a22] : Matrix (Fin 3) (Fin 3) F).det * l := by
  rw [Matrix.det_succ_row_zero, Matrix.det_fin_three]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem det_anti (u0 u1 u2 v0 v1 v2 : F) :
    (!![0, 0, 0, u0; 0, 0, 0, u1; 0, 0, 0, u2; v0, v1, v2, 0] :
      Matrix (Fin 4) (Fin 4) F).det = 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem mem_blockL_of_fix [Finite F] (hF : Nat.card F = 3) {x : projectiveSL 4 F}
    (hx : conjAut 4 F (dGL F) x = x) : x ∈ blockL F := by
  have h2 := card3_two_ne_zero hF
  obtain ⟨g, rfl⟩ := proj_surjective 4 F x
  rw [conjAut_proj] at hx
  obtain ⟨c, -, hcm⟩ := proj_eq_exists hx
  have hdinv : (((dGL F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blk (1 : F) 1 0 0 (-1) := rfl
  rw [coe_slConjugation, coe_dGL, hdinv] at hcm
  set M := (g : Matrix (Fin 4) (Fin 4) F) with hM
  have e : ∀ i j, M i j =
      (c : F) * ((if i = 3 then -1 else 1) * M i j * (if j = 3 then -1 else 1)) := fun i j => by
    have h := congrFun (congrFun hcm i) j
    rw [Matrix.smul_apply, smul_eq_mul, dmd_apply] at h
    exact h
  have hdet : M.det = 1 := g.2
  have hc : (c : F) = 1 ∨ (c : F) = -1 := by
    have h := card3_mul_self hF c.ne_zero
    have h' : ((c : F) - 1) * ((c : F) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  have zc : ∀ i j : Fin 4,
      (c : F) * ((if i = 3 then (-1 : F) else 1) * (if j = 3 then -1 else 1)) = -1 →
        M i j = 0 := by
    intro i j hij
    have h := e i j
    have h' : M i j = -M i j := by linear_combination h + M i j * hij
    exact eq_zero_of_eq_neg h2 rfl h'
  rcases hc with hc1 | hc1
  ·
    have hMf : M = !![M 0 0, M 0 1, M 0 2, 0; M 1 0, M 1 1, M 1 2, 0; M 2 0, M 2 1, M 2 2, 0;
        0, 0, 0, M 3 3] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> exact zc _ _ (by simp [hc1])
    set A3 : Matrix (Fin 3) (Fin 3) F :=
      !![M 0 0, M 0 1, M 0 2; M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2] with hA3
    have hdA : A3.det * M 3 3 = 1 := by
      have h := congrArg Matrix.det hMf
      rw [det_corner, hdet] at h
      exact h.symm
    have hl0 : M 3 3 ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hdA
      exact zero_ne_one hdA
    have hl : M 3 3 = 1 ∨ M 3 3 = -1 := by
      have h := card3_mul_self hF hl0
      have h' : (M 3 3 - 1) * (M 3 3 + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    rcases hl with hl1 | hl1
    · have hdA1 : A3.det = 1 := by rw [hl1, mul_one] at hdA; exact hdA
      refine ⟨⟨A3, hdA1⟩, ?_⟩
      show proj 4 F (blockSL F 4 3 0 zero_add_three_le_four ⟨A3, hdA1⟩) = proj 4 F g
      congr 1
      apply Subtype.ext
      refine (coe_blockSL_four_three ⟨A3, hdA1⟩).trans ?_
      show blk3 A3 = M
      rw [hMf, hl1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA3]
    · have hdA1 : (-A3).det = 1 := by
        rw [Matrix.det_neg, Fintype.card_fin]
        rw [hl1] at hdA
        linear_combination hdA
      have hgX : g = scalarElement (-1 : Fˣ) (by norm_num) *
          blockSL F 4 3 0 zero_add_three_le_four ⟨-A3, hdA1⟩ := by
        apply Subtype.ext
        show M = ((scalarElement (-1 : Fˣ) (by norm_num) *
          blockSL F 4 3 0 zero_add_three_le_four ⟨-A3, hdA1⟩ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
        rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement,
          coe_blockSL_four_three (F := F) ⟨-A3, hdA1⟩]
        show M = Matrix.scalar (Fin 4) ((-1 : Fˣ) : F) * blk3 (-A3)
        rw [hMf, hl1]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hA3]
      refine ⟨⟨-A3, hdA1⟩, ?_⟩
      show proj 4 F (blockSL F 4 3 0 zero_add_three_le_four ⟨-A3, hdA1⟩) = proj 4 F g
      rw [hgX, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars _ _), one_mul]
  ·
    have hMf : M = !![0, 0, 0, M 0 3; 0, 0, 0, M 1 3; 0, 0, 0, M 2 3; M 3 0, M 3 1, M 3 2, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> exact zc _ _ (by simp [hc1])
    exfalso
    rw [hMf, det_anti] at hdet
    exact zero_ne_one hdet

theorem blockQ0_le_blockL : blockQ0 F ≤ blockL F := by
  rintro _ ⟨c, -, rfl⟩
  refine ⟨blockSL F 3 2 0 (by norm_num) c, ?_⟩
  show proj 4 F (blockSL F 4 3 0 zero_add_three_le_four (blockSL F 3 2 0 (by norm_num) c)) =
    proj 4 F (blockSL F 4 2 0 (by norm_num) c)
  congr 1
  apply Subtype.ext
  rw [coe_blockSL_four_three, coe_blockSL_three_zero, WeakCT.coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockQ0_ne_bot [Finite F] (hF : Nat.card F = 3) : blockQ0 F ≠ ⊥ := by
  intro h
  have hm := mem_blockQ0 (qI_mem hF)
  rw [h, Subgroup.mem_bot, proj_eq_one_iff, mem_scalars] at hm
  obtain ⟨c, -, hc⟩ := hm
  rw [coe_block_qI] at hc
  have h00 : (0 : F) = c := by simpa using congrFun (congrFun hc 0) 0
  exact c.ne_zero h00.symm

theorem sigmaFixGen_d_eq [Finite F] (hF : Nat.card F = 3) :
    sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F)) = blockL F := by
  have hSL : sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F)) ≤ blockL F :=
    iSup₂_le fun M hM => fun x hx => mem_blockL_of_fix hF (hM.2 x hx)
  refine le_antisymm hSL ?_
  have hgen : ∀ M : Subgroup (projectiveSL 4 F), M ∈ CoreAssembly.conjClass (blockQ0 F) →
      M ≤ blockL F → M ≤ sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F)) := fun M hM hML =>
    le_iSup₂ (f := fun (M : Subgroup (projectiveSL 4 F))
      (_ : M ∈ {M : Subgroup (projectiveSL 4 F) | M ∈ CoreAssembly.conjClass (blockQ0 F) ∧
        ∀ x ∈ M, conjAut 4 F (dGL F) x = x}) => M) M
      ⟨hM, fun x hx => conjAut_d_of_mem_blockL (hML hx)⟩
  have hconj : ∀ l ∈ blockL F, Generic.conjSub l (sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F))) ≤
      sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F)) := by
    intro l hl
    show (sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F))).map (MulAut.conj l).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨⟨g, rfl⟩, hfix⟩ := hM
    rw [← Subgroup.map_le_iff_le_comap]
    refine hgen _ ⟨l * g, conjSub_mul l g _⟩ ?_
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    show l * y * l⁻¹ ∈ blockL F
    exact (blockL F).mul_mem ((blockL F).mul_mem hl (mem_blockL_of_fix hF (hfix y hy)))
      ((blockL F).inv_mem hl)
  have hN : ((sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F))).subgroupOf (blockL F)).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj l l.2 ⟨n, hn, rfl⟩
  have := isSimpleGroup_blockL hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F))).subgroupOf (blockL F)) with hb | ht
  · exfalso
    apply blockQ0_ne_bot hF
    rw [eq_bot_iff]
    intro q hq
    have hqS : (⟨q, blockQ0_le_blockL hq⟩ : ↥(blockL F)) ∈
        (sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F))).subgroupOf (blockL F) :=
      hgen _ (CoreAssembly.mem_conjClass_self _) blockQ0_le_blockL hq
    rw [hb, Subgroup.mem_bot] at hqS
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hqS)
  · intro l hl
    have h1 : (⟨l, hl⟩ : ↥(blockL F)) ∈
        (sigmaFixGen (blockQ0 F) (conjAut 4 F (dGL F))).subgroupOf (blockL F) := by
      rw [ht]
      exact Subgroup.mem_top _
    exact h1

end D

theorem lieModel_sigmaFixGen_psl4 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}
    (hB : ∀ x ∈ blockQ0 F, conjAut 4 F B x = x)
    (hα : α = conjAut 4 F B * conjAut 4 F (dGL F) * (conjAut 4 F B)⁻¹) :
    LieModel ↥(sigmaFixGen (blockQ0 F) α) .PSL 3 3 1 := by
  rw [hα, D.sigmaFixGen_conj _ _ _ hB, D.sigmaFixGen_d_eq hF]
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (Subgroup.equivMapOfInjective _ (conjAut 4 F B).toMonoidHom (conjAut 4 F B).injective)
    (D.lieModel_blockL hF)

end CFSG.ClassicalInvolution.Q3.TL4.E1521
