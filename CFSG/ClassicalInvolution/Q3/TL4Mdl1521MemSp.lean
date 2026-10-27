module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521Mem
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521Sp
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSp4SL4

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.E1521

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem det_mat_sp (g : StatedSp 2 F) : (mat 2 F g).det = 1 :=
  CFSG.ComponentClassification.CatLeafProof.det_mat_statedSp_two g

@[expose] noncomputable def spToSL (F : Type) [Field F] : StatedSp 2 F →* SL(4, F) where
  toFun g := ⟨spMat (mat 2 F g), by rw [Matrix.det_reindex_self]; exact det_mat_sp g⟩
  map_one' := Subtype.ext (by
    show spMat (mat 2 F 1) = 1
    rw [map_one, spMat_one])
  map_mul' g h := Subtype.ext (by
    show spMat (mat 2 F (g * h)) = spMat (mat 2 F g) * spMat (mat 2 F h)
    rw [map_mul, spMat_mul])

theorem coe_spToSL (g : StatedSp 2 F) :
    ((spToSL F g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = spMat (mat 2 F g) :=
  rfl

theorem spScalars_le_comap [Finite F] (hF : Nat.card F = 3) :
    SymplecticHigher.spScalars 2 F ≤ (LinearFlag.scalars 4 F).comap (spToSL F) := by
  intro z hz
  have hz' := Subgroup.mem_subgroupOf.mp hz
  rw [StatedScalars, MonoidHom.mem_range] at hz'
  obtain ⟨c, hc⟩ := hz'
  rw [Subgroup.mem_comap, LinearFlag.mem_scalars]
  refine ⟨c, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one,
      show (c : F) ^ 4 = ((c : F) * c) * ((c : F) * c) by ring, card3_mul_self hF c.ne_zero,
      one_mul]
  · rw [coe_spToSL, mat_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp only [spMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]

@[expose] noncomputable def spProjToPSL [Finite F] (hF : Nat.card F = 3) :
    StatedProj (StatedSp 2 F) →* LinearFlag.projectiveSL 4 F :=
  QuotientGroup.map _ _ (spToSL F) (spScalars_le_comap hF)

theorem spProjToPSL_proj [Finite F] (hF : Nat.card F = 3) (g : StatedSp 2 F) :
    spProjToPSL hF (SymplecticFlag.proj 2 F g) = LinearFlag.proj 4 F (spToSL F g) :=
  rfl

theorem spProjToPSL_injective [Finite F] (hF : Nat.card F = 3) :
    Function.Injective (spProjToPSL hF) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := 2) (K := F) x
  rw [spProjToPSL_proj, ← MonoidHom.mem_ker, LinearFlag.ker_proj, LinearFlag.mem_scalars] at hx
  obtain ⟨c, -, hc⟩ := hx
  rw [← MonoidHom.mem_ker, SymplecticHigher.ker_proj]
  refine Subgroup.mem_subgroupOf.mpr ⟨c, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, ← mat_apply]
  apply spMat_injective
  rw [← coe_spToSL, hc]
  ext i j
  simp only [spMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]

theorem spMat_longBlock_one (X : SL(2, F)) :
    spMat (mat 2 F (longBlock F 2 1 X)) =
      !![1, 0, 0, 0; 0, 1, 0, 0;
        0, 0, (X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
        0, 0, (X : Matrix (Fin 2) (Fin 2) F) 1 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  rw [mat_longBlock]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spMat, spIdx, CFSG.LieType.Steinberg.Sp.blockMat]

theorem spToSL_longBlock_zero (X : SL(2, F)) :
    spToSL F (longBlock F 2 0 X) = blockSL F 4 2 0 (by norm_num) X := by
  apply Subtype.ext
  rw [coe_spToSL, spMat_longBlock, WeakCT.coe_blockSL, blockMat_four_zero]

theorem spToSL_longBlock_one (X : SL(2, F)) :
    spToSL F (longBlock F 2 1 X) = blockSL F 4 2 2 (by norm_num) X := by
  apply Subtype.ext
  rw [coe_spToSL, spMat_longBlock_one, WeakCT.coe_blockSL, blockMat_four_two]

@[expose] noncomputable def blockQ2Sp (F : Type) [Field F] :
    Subgroup (StatedProj (StatedSp 2 F)) :=
  (commutator SL(2, F)).map ((SymplecticFlag.proj 2 F).comp (longBlock F 2 1))

theorem map_blockQ0Sp [Finite F] (hF : Nat.card F = 3) :
    (blockQ0Sp F).map (spProjToPSL hF) = blockQ0 F := by
  rw [blockQ0Sp, blockQ0, Subgroup.map_map]
  congr 1
  ext X
  show spProjToPSL hF (SymplecticFlag.proj 2 F (longBlock F 2 0 X)) = _
  rw [spProjToPSL_proj, spToSL_longBlock_zero]
  rfl

theorem map_blockQ2Sp [Finite F] (hF : Nat.card F = 3) :
    (blockQ2Sp F).map (spProjToPSL hF) = blockQ2 F := by
  rw [blockQ2Sp, blockQ2, Subgroup.map_map]
  congr 1
  ext X
  show spProjToPSL hF (SymplecticFlag.proj 2 F (longBlock F 2 1 X)) = _
  rw [spProjToPSL_proj, spToSL_longBlock_one]
  rfl

theorem mem_blockQ0Sp_iff [Finite F] (hF : Nat.card F = 3) {x : StatedProj (StatedSp 2 F)} :
    x ∈ blockQ0Sp F ↔ spProjToPSL hF x ∈ blockQ0 F := by
  rw [← map_blockQ0Sp hF, Subgroup.mem_map_iff_mem (spProjToPSL_injective hF)]

theorem mem_blockQ2Sp_iff [Finite F] (hF : Nat.card F = 3) {x : StatedProj (StatedSp 2 F)} :
    x ∈ blockQ2Sp F ↔ spProjToPSL hF x ∈ blockQ2 F := by
  rw [← map_blockQ2Sp hF, Subgroup.mem_map_iff_mem (spProjToPSL_injective hF)]

theorem card_blockQ0Sp [Finite F] (hF : Nat.card F = 3) : Nat.card (blockQ0Sp F) = 8 := by
  rw [← Subgroup.card_map_of_injective (spProjToPSL_injective hF), map_blockQ0Sp hF,
    card_blockQ0 hF]

theorem card_blockQ2Sp [Finite F] (hF : Nat.card F = 3) : Nat.card (blockQ2Sp F) = 8 := by
  rw [← Subgroup.card_map_of_injective (spProjToPSL_injective hF), map_blockQ2Sp hF,
    card_blockQ2 hF]

theorem spScalars_mul_self [Finite F] (hF : Nat.card F = 3) {z : StatedSp 2 F}
    (hz : z ∈ SymplecticHigher.spScalars 2 F) : z * z = 1 := by
  have h1 : spToSL F z * spToSL F z = 1 :=
    scalars_mul_self hF (spScalars_le_comap hF hz)
  apply mat_injective
  apply spMat_injective
  rw [map_mul, map_one, spMat_mul, spMat_one, ← coe_spToSL, ← Matrix.SpecialLinearGroup.coe_mul,
    h1, Matrix.SpecialLinearGroup.coe_one]

theorem spScalars_le_center : SymplecticHigher.spScalars 2 F ≤ Subgroup.center (StatedSp 2 F) := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq]

theorem spProjToPSL_stdInv [Finite F] (hF : Nat.card F = 3) (S : Finset (Fin 2))
    (hne : SymplecticFlag.proj 2 F (ModelFacts.stdInv F S) ≠ 1) :
    spProjToPSL hF (SymplecticFlag.proj 2 F (ModelFacts.stdInv F S)) =
      LinearFlag.proj 4 F (tSL F) := by
  have h2 := card3_two_ne_zero hF
  set σ₀ : F := if (0 : Fin 2) ∈ S then -1 else 1 with hσ₀
  set σ₁ : F := if (1 : Fin 2) ∈ S then -1 else 1 with hσ₁
  have hσ0 : σ₀ = 1 ∨ σ₀ = -1 := by rw [hσ₀]; split_ifs <;> simp
  have hσ1 : σ₁ = 1 ∨ σ₁ = -1 := by rw [hσ₁]; split_ifs <;> simp
  have hmat : spMat (mat 2 F (ModelFacts.stdInv F S)) = blk σ₀ σ₁ 0 0 σ₁ := by
    rw [ModelFacts.mat_stdInv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spMat, spIdx, ModelFacts.stdSign, hσ₀, hσ₁]
  have hne' : σ₁ = -σ₀ := by
    by_contra h
    apply hne
    have hσ : σ₁ = σ₀ := by
      rcases hσ0 with h0 | h0 <;> rcases hσ1 with h1 | h1 <;> rw [h0, h1] at h ⊢ <;>
        first | rfl | (exfalso; exact h (by norm_num))
    rw [← MonoidHom.mem_ker, SymplecticHigher.ker_proj]
    have hσu : σ₀ ≠ 0 := by rcases hσ0 with h0 | h0 <;> rw [h0] <;> norm_num
    refine Subgroup.mem_subgroupOf.mpr ⟨Units.mk0 σ₀ hσu, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, ← mat_apply]
    apply spMat_injective
    rw [hmat, hσ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spMat, spIdx, Matrix.scalar_apply]
  have hσu : σ₀ ≠ 0 := by rcases hσ0 with h0 | h0 <;> rw [h0] <;> norm_num
  have hσ2 : σ₀ * σ₀ = 1 := by rcases hσ0 with h0 | h0 <;> rw [h0] <;> norm_num
  rw [spProjToPSL_proj]
  refine proj_eq_of_eq_smul (Units.mk0 σ₀ hσu) ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
      show σ₀ ^ 4 = (σ₀ * σ₀) * (σ₀ * σ₀) by ring, hσ2, one_mul]
  · rw [coe_spToSL, hmat, Units.val_mk0, hne']
    show _ = σ₀ • blk 1 (-1) 0 0 (-1)
    rw [smul_blk]
    exact blk_congr (by ring) (by ring) (by ring) (by ring) (by ring)

theorem mem_blockQ0_or_blockQ2_of_sq [Finite F] (hF : Nat.card F = 3)
    {x : LinearFlag.projectiveSL 4 F} (hx : x * x = LinearFlag.proj 4 F (tSL F)) :
    x ∈ blockQ0 F ∨ x ∈ blockQ2 F := by
  obtain ⟨k, rfl⟩ := LinearFlag.proj_surjective 4 F x
  rw [← map_mul] at hx
  obtain ⟨c, -, hc⟩ := proj_eq_exists hx.symm
  exact mem_blockQ0_or_blockQ2 hF k (card3_mul_self hF c.ne_zero)
    (by rw [← Matrix.SpecialLinearGroup.coe_mul]; exact hc)

theorem spMat_weylD : spMat (mat 2 F (SymplecticCoverFour.weylD F)) = mW F := by
  rw [mat_apply, SymplecticCoverFour.weylD, SymplecticTorusWeyl.coe_leviSp]
  have hinv : (((SymplecticCoverFour.swapGL F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spMat, spIdx, SymplecticCoverFour.swapGL]

theorem map_blockQ2Sp_swap [Finite F] (hF : Nat.card F = 3) :
    (blockQ2Sp F).map
        (MulAut.conj (SymplecticFlag.proj 2 F (SymplecticCoverFour.weylD F))).toMonoidHom =
      blockQ0Sp F := by
  apply Subgroup.map_injective (spProjToPSL_injective hF)
  rw [map_blockQ0Sp hF, ← map_blockQ2_swap, ← map_blockQ2Sp hF, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext g
  show spProjToPSL hF (SymplecticFlag.proj 2 F (SymplecticCoverFour.weylD F) *
    SymplecticFlag.proj 2 F g * (SymplecticFlag.proj 2 F (SymplecticCoverFour.weylD F))⁻¹) =
      LinearFlag.conjAut 4 F (wGL F) (spProjToPSL hF (SymplecticFlag.proj 2 F g))
  rw [← map_inv, ← map_mul, ← map_mul, spProjToPSL_proj, spProjToPSL_proj,
    LinearFlag.conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_spToSL, coe_spToSL, map_mul, map_mul, spMat_mul,
    spMat_mul, spMat_weylD]
  have hinv : spMat (mat 2 F (SymplecticCoverFour.weylD F)⁻¹) = mW F := by
    have h1 : spMat (mat 2 F (SymplecticCoverFour.weylD F)⁻¹) * mW F = 1 := by
      rw [← spMat_weylD, ← spMat_mul, ← map_mul, inv_mul_cancel, map_one, spMat_one]
    calc spMat (mat 2 F (SymplecticCoverFour.weylD F)⁻¹) =
        spMat (mat 2 F (SymplecticCoverFour.weylD F)⁻¹) * (mW F * mW F) := by
          rw [mW_mul_self, Matrix.mul_one]
      _ = mW F := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hinv]
  rfl

theorem exists_aut_blockQ0Sp [Finite F] (hF : Nat.card F = 3)
    {A : Subgroup (StatedProj (StatedSp 2 F))} (hA : Nonempty (↥A ≃* QuaternionGroup 2)) :
    ∃ φ : MulAut (StatedProj (StatedSp 2 F)), A.map φ.toMonoidHom = blockQ0Sp F := by
  have h2 := card3_two_ne_zero hF
  obtain ⟨z, a, b, ha, hb, hz1, -, haz, hbz, hab, hall⟩ := quat_rel hA
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := 2) (K := F) a
  obtain ⟨g', rfl⟩ := SymplecticHigher.proj_surjective (r := 2) (K := F) b
  have hz₁ : (g * g)⁻¹ * (g' * g') ∈ SymplecticHigher.spScalars 2 F := by
    rw [← SymplecticHigher.ker_proj, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, haz, hbz, inv_mul_cancel]
  have hz₂ : g' * (g * g' * g⁻¹) ∈ SymplecticHigher.spScalars 2 F := by
    rw [← SymplecticHigher.ker_proj, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hab, mul_inv_cancel]
  have hh := quat_lift_sq (g := g) (g' := g') spScalars_le_center
    (fun _ hz => spScalars_mul_self hF hz) hz₁ hz₂ (by group) (by group)
  have hzg : SymplecticFlag.proj 2 F (g' * g') = z := by rw [map_mul, hbz]
  obtain ⟨S, k, hk⟩ := ModelFacts.exists_mul_eq_stdInv h2 hh
  set c : MulAut (StatedProj (StatedSp 2 F)) := MulAut.conj (SymplecticFlag.proj 2 F k)⁻¹
  have hcz : c z = SymplecticFlag.proj 2 F (ModelFacts.stdInv F S) := by
    rw [← hzg, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_assoc, hk]
    group
  have hne : SymplecticFlag.proj 2 F (ModelFacts.stdInv F S) ≠ 1 := by
    rw [← hcz]
    exact fun h => hz1 (c.injective (by rw [h, map_one]))
  have hι := spProjToPSL_stdInv hF S hne
  rw [← hcz] at hι
  have hsq : ∀ x : StatedProj (StatedSp 2 F), x * x = c z → x ∈ blockQ0Sp F ∨ x ∈ blockQ2Sp F := by
    intro x hx
    rw [mem_blockQ0Sp_iff hF, mem_blockQ2Sp_iff hF]
    exact mem_blockQ0_or_blockQ2_of_sq hF (by rw [← map_mul, hx, hι])
  have hall₂ : ∀ x ∈ A.map c.toMonoidHom, x ∈ blockQ0Sp F ∨ x ∈ blockQ2Sp F := by
    rintro _ ⟨y, hy, rfl⟩
    show c y ∈ blockQ0Sp F ∨ c y ∈ blockQ2Sp F
    have ha₂ : c (SymplecticFlag.proj 2 F g) * c (SymplecticFlag.proj 2 F g) = c z := by
      rw [← map_mul, haz]
    rcases hall y hy with hy1 | hy1 | hy2
    · rw [hy1, map_one]
      exact Or.inl (one_mem _)
    · rw [hy1, ← ha₂]
      rcases hsq _ ha₂ with h | h
      · exact Or.inl (mul_mem h h)
      · exact Or.inr (mul_mem h h)
    · exact hsq _ (by rw [← map_mul, hy2])
  have hcard : Nat.card (A.map c.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (f := c.toMonoidHom) c.injective, card_of_quat hA]
  rcases le_or_le_of_forall_mem hall₂ with hle | hle
  · exact ⟨c, Subgroup.eq_of_le_of_card_ge hle (by rw [card_blockQ0Sp hF, hcard])⟩
  · have hA2 := Subgroup.eq_of_le_of_card_ge hle (by rw [card_blockQ2Sp hF, hcard])
    refine ⟨MulAut.conj (SymplecticFlag.proj 2 F (SymplecticCoverFour.weylD F)) * c, ?_⟩
    rw [show (MulAut.conj (SymplecticFlag.proj 2 F (SymplecticCoverFour.weylD F)) * c).toMonoidHom =
      (MulAut.conj (SymplecticFlag.proj 2 F (SymplecticCoverFour.weylD F))).toMonoidHom.comp
        c.toMonoidHom from rfl, ← Subgroup.map_map, hA2, map_blockQ2Sp_swap hF]

theorem exists_mulEquiv_blockQ0Sp [Finite F] (hF : Nat.card F = 3) {S : Type} [Group S]
    (e₀ : S ≃* StatedProj (StatedSp 2 F)) {A : Subgroup S}
    (hA : Nonempty (↥A ≃* QuaternionGroup 2)) :
    ∃ e : S ≃* StatedProj (StatedSp 2 F), A.map e.toMonoidHom = blockQ0Sp F := by
  obtain ⟨e⟩ := hA
  obtain ⟨φ, hφ⟩ := exists_aut_blockQ0Sp hF (A := A.map e₀.toMonoidHom)
    ⟨(A.equivMapOfInjective _ e₀.injective).symm.trans e⟩
  refine ⟨e₀.trans φ, ?_⟩
  rw [← hφ, Subgroup.map_map]
  rfl

theorem blockQ0Sp_comm_blockQ2Sp [Finite F] (hF : Nat.card F = 3)
    {x y : StatedProj (StatedSp 2 F)} (hx : x ∈ blockQ0Sp F) (hy : y ∈ blockQ2Sp F) :
    x * y = y * x := by
  apply spProjToPSL_injective hF
  rw [map_mul, map_mul]
  exact blockQ0_comm_blockQ2 ((mem_blockQ0Sp_iff hF).mp hx) ((mem_blockQ2Sp_iff hF).mp hy)

theorem eq_blockQ2Sp_of_comm [Finite F] (hF : Nat.card F = 3)
    {B : Subgroup (StatedProj (StatedSp 2 F))} (hB : Nonempty (↥B ≃* QuaternionGroup 2))
    (hc : ∀ x ∈ B, ∀ y ∈ blockQ0Sp F, x * y = y * x) : B = blockQ2Sp F := by
  obtain ⟨e⟩ := hB
  apply Subgroup.map_injective (spProjToPSL_injective hF)
  rw [map_blockQ2Sp hF]
  refine eq_blockQ2_of_comm hF ⟨(B.equivMapOfInjective _ (spProjToPSL_injective hF)).symm.trans e⟩
    ?_
  rintro _ ⟨x, hx, rfl⟩ _ hy
  rw [← map_blockQ0Sp hF] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  rw [← map_mul, ← map_mul, hc x hx y hy]

theorem mul_self_eq_one_of_comm_blockQ2 [Finite F] (hF : Nat.card F = 3)
    {w : LinearFlag.projectiveSL 4 F} (hw : w ∈ blockQ2 F)
    (hc : ∀ x ∈ blockQ2 F, w * x = x * w) : w * w = 1 := by
  have h2 := card3_two_ne_zero hF
  have h3 := card3_three_eq_zero hF
  obtain ⟨W, -, rfl⟩ := hw
  set Wb : SL(4, F) := blockSL F 4 2 2 (by norm_num) W with hWb
  have hc' : ∀ x ∈ blockQ2 F, LinearFlag.proj 4 F Wb * x = x * LinearFlag.proj 4 F Wb := hc
  have key : ∀ X : SL(2, F), X ∈ commutator SL(2, F) →
      LinearFlag.conjAut 4 F (Matrix.SpecialLinearGroup.toGL Wb)
        (LinearFlag.proj 4 F (blockSL F 4 2 2 (by norm_num) X)) =
        LinearFlag.proj 4 F (blockSL F 4 2 2 (by norm_num) X) := fun X hX => by
    rw [LinearFlag.conjAut_toGL, MulAut.conj_apply]
    rw [hc' _ (mem_blockQ2 hX), mul_inv_cancel_right]
  have hI := comm_of_conjAut_fix _ (key _ (qI_mem hF))
    (by rw [coe_block2_qI]; exact trace_mI2 h2)
  have hJ := comm_of_conjAut_fix _ (key _ (qJ_mem hF h3))
    (by rw [coe_block2_qJ]; exact trace_mJ2 h2)
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_block2_qI, hWb, WeakCT.coe_blockSL,
    blockMat_four_two] at hI
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_block2_qJ, hWb, WeakCT.coe_blockSL,
    blockMat_four_two] at hJ
  have i22 := congrFun (congrFun hI 2) 2
  have i23 := congrFun (congrFun hI 2) 3
  have j22 := congrFun (congrFun hJ 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at i22 i23 j22
  set p := (W : Matrix (Fin 2) (Fin 2) F) 0 0
  set q := (W : Matrix (Fin 2) (Fin 2) F) 0 1
  set r := (W : Matrix (Fin 2) (Fin 2) F) 1 0
  set s := (W : Matrix (Fin 2) (Fin 2) F) 1 1
  have hr : r = -q := by linear_combination -i22
  have hq : q = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination j22 + hr)
  have hs : s = p := by linear_combination -i23
  rw [hq, neg_zero] at hr
  have hdet : p * s - q * r = 1 := by
    have := W.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hp2 : p * p = 1 := by rw [hq, hr, hs] at hdet; linear_combination hdet
  show LinearFlag.proj 4 F Wb * LinearFlag.proj 4 F Wb = 1
  rw [← map_mul, ← MonoidHom.mem_ker, LinearFlag.ker_proj]
  have hWW : Wb * Wb = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hWb, WeakCT.coe_blockSL, blockMat_four_two,
      Matrix.SpecialLinearGroup.coe_one]
    have hW : (W : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, s] := Matrix.eta_fin_two _
    rw [hW, hq, hr, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hp2]
  rw [hWW]
  exact one_mem _

theorem no_sigma_blockQSp [Finite F] (hF : Nat.card F = 3) (α : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ a ∈ blockQ0Sp F, α a = a)
    (hw : ∃ w ∈ blockQ2Sp F, orderOf w = 4 ∧ ∀ b ∈ blockQ2Sp F, α b = w * b * w⁻¹) :
    α * α ≠ 1 := by
  obtain ⟨w, hw2, hwo, hact⟩ := hw
  intro hα2
  refine sig_psp4_false hF α hα2 hfix ?_
  by_contra hno
  push Not at hno
  have hcomm : ∀ x ∈ blockQ2 F, spProjToPSL hF w * x = x * spProjToPSL hF w := by
    intro x hx
    rw [← map_blockQ2Sp hF] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := hno y (fun z hz => (blockQ0Sp_comm_blockQ2Sp hF hz hy).symm)
    rw [hact y hy] at h1
    rw [← map_mul, ← map_mul]
    congr 1
    calc w * y = w * y * w⁻¹ * w := by group
      _ = y * w := by rw [h1]
  have hww := mul_self_eq_one_of_comm_blockQ2 hF ((mem_blockQ2Sp_iff hF).mp hw2) hcomm
  rw [← map_mul] at hww
  have hw1 : w * w = 1 := spProjToPSL_injective hF (by rw [hww, map_one])
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hw1])
  rw [hwo] at h2
  exact absurd h2 (by norm_num)

end CFSG.ClassicalInvolution.Q3.TL4.E1521
