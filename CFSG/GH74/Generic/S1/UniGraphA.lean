module

public import CFSG.GH74.Generic.S1.UniClassA
public import CFSG.GH74.Generic.S1.UniDescent

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem map_blk4 (σ : F →+* F) (A B : Matrix (Fin 2) (Fin 2) F) :
    (blk4 A B).map σ = blk4 (A.map σ) (B.map σ) := by
  simp only [blk4_eq_reindex, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero σ)]

theorem levi_bar_fixed (h : UnitaryFieldData p f F) (Y : SpecialLinearGroup (Fin 2) F)
    (hY : (Y : Matrix (Fin 2) (Fin 2) F).map h.bar = Y) :
    ((leviHom h Y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map h.bar =
      ((leviHom h Y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [levi_val, map_blk4]
  set Xi : Matrix (Fin 2) (Fin 2) F :=
    (((SpecialLinearGroup.toGL Y)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hXi
  have h1 : Xi * (Y : Matrix (Fin 2) (Fin 2) F) = 1 := by simp [hXi]
  have h2 : (Y : Matrix (Fin 2) (Fin 2) F) * Xi = 1 := by simp [hXi]
  have hXib : Xi.map h.bar = Xi := by
    have e : Xi.map h.bar * (Y : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M.map h.bar) h1
      simp only [Matrix.map_mul, hY] at this
      rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at this
      exact this
    calc Xi.map h.bar = Xi.map h.bar * ((Y : Matrix (Fin 2) (Fin 2) F) * Xi) := by rw [h2, Matrix.mul_one]
      _ = (Xi.map h.bar * (Y : Matrix (Fin 2) (Fin 2) F)) * Xi := by rw [Matrix.mul_assoc]
      _ = Xi := by rw [e, Matrix.one_mul]
  have hc : (cT h Xi).map h.bar = cT h Xi := by
    rw [cT_def, hXib, Matrix.transpose_map, hXib]
  rw [hY, hc]


theorem blk4_comm_levi (h : UnitaryFieldData p f F) (ε : F) (Y : SpecialLinearGroup (Fin 2) F) :
    blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1) * ((leviHom h Y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((leviHom h Y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1) := by
  rw [levi_val, blk4_mul, blk4_mul]
  simp

theorem iotaHom_of_neg_one (h : UnitaryFieldData p f F) {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat)
    (Y : SpecialLinearGroup (Fin 2) F) (hY : (Y : Matrix (Fin 2) (Fin 2) F) = -1) :
    ((iotaHom h hP Y : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = xGL F := by
  have hneg : ((SpecialLinearGroup.toGL Y)⁻¹ : GL (Fin 2) F) = SpecialLinearGroup.toGL Y := by
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    show (Y : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) = 1
    rw [hY, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul]
  have hlev : leviHom h Y = xGL F := by
    apply Units.ext
    rw [levi_val, hneg, xGL_eq_neg_one]
    change blk4 (Y : Matrix (Fin 2) (Fin 2) F) (cT h (Y : Matrix (Fin 2) (Fin 2) F)) = -1
    rw [hY, cT_neg, cT_one, blk4_neg, blk4_one]
  rw [iotaHom_val, hlev, ← xGL_comm P, mul_inv_cancel_right]

theorem goodFixedCentral_of_adapted (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (hq4 : p ^ f % 4 = 1) (α : MulAut ↥(StatedSU 4 (p ^ f) F)) {g : GL (Fin 4) F} {ε s : F}
    (hε : ε = 1 ∨ ε = -1) (hs : s ≠ 0)
    (hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g⁻¹)
    {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat)
    (hgP : (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F).map h.bar =
      s • ((P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1))) :
    GoodFixedCentral False α := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  let K₀ := h.fixedField
  let ι : K₀ →+* F := K₀.subtype
  let ι₂ : SpecialLinearGroup (Fin 2) K₀ →* ↥(StatedSU 4 (p ^ f) F) :=
    (iotaHom h hP).comp (SpecialLinearGroup.map ι)
  have hεε : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  let D : Matrix (Fin 4) (Fin 4) F := blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1)
  have hDD : D * D = 1 := by
    simp only [D]
    rw [blk4_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hεε,
      one_smul, blk4_one]
  let Dgl : GL (Fin 4) F := ⟨D, D, hDD, hDD⟩
  let sc : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 s hs)
  have hgPGL : g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P = sc * (P * Dgl) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    change (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F).map h.bar = _
    rw [hgP, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rfl
  have hq3 : 3 ≤ p ^ f := le_trans (by have := h.prime.two_le; omega)
    (Nat.le_self_pow (by have := h.one_le; omega) p)
  refine ⟨ι₂.range, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨X, rfl⟩
    let Y : SpecialLinearGroup (Fin 2) F := SpecialLinearGroup.map ι X
    have hY : (Y : Matrix (Fin 2) (Fin 2) F).map h.bar = Y := by
      have : (Y : Matrix (Fin 2) (Fin 2) F) = (X : Matrix (Fin 2) (Fin 2) K₀).map ι := rfl
      rw [this]
      exact map_fixedField_bar h _
    have hLbar := levi_bar_fixed h Y hY
    have hLb : Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (leviHom h Y) = leviHom h Y :=
      Units.ext hLbar
    apply Subtype.ext
    rw [hαg]
    change g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (P * leviHom h Y * P⁻¹) * g⁻¹ =
      P * leviHom h Y * P⁻¹
    rw [map_mul, map_mul, map_inv, hLb]
    have e1 : g * (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P * leviHom h Y *
        (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P)⁻¹) * g⁻¹ =
        (g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P) * leviHom h Y *
          (g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P)⁻¹ := by group
    rw [e1, hgPGL]
    have hDL : Dgl * leviHom h Y = leviHom h Y * Dgl := Units.ext (blk4_comm_levi h ε Y)
    have e2 : (sc * (P * Dgl)) * leviHom h Y * (sc * (P * Dgl))⁻¹ =
        sc * (P * (Dgl * leviHom h Y * Dgl⁻¹) * P⁻¹) * sc⁻¹ := by group
    have e3 : Dgl * leviHom h Y * Dgl⁻¹ = leviHom h Y := by rw [hDL, mul_inv_cancel_right]
    rw [e2, e3, Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 s hs) _, mul_inv_cancel_right]
  · intro z hz
    have hz' := (mem_center_statedSU_four_iff hF hq4 z).1 hz
    rcases hz' with h1 | h1
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      show ((iotaHom h hP (SpecialLinearGroup.map ι 1) : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = z
      rw [map_one, iotaHom_val, map_one, mul_one, mul_inv_cancel, h1]
    · let negOne₀ : SpecialLinearGroup (Fin 2) K₀ :=
        ⟨-1, by rw [Matrix.det_neg, Matrix.det_one]; norm_num⟩
      refine ⟨negOne₀, ?_⟩
      apply Subtype.ext
      rw [h1]
      show ((iotaHom h hP (SpecialLinearGroup.map ι negOne₀) : ↥(StatedSU 4 (p ^ f) F)) :
        GL (Fin 4) F) = xGL F
      apply iotaHom_of_neg_one h hP
      show (-1 : Matrix (Fin 2) (Fin 2) K₀).map ι = -1
      ext i j
      simp [Matrix.one_apply]
  · have h4 : 4 ≤ Nat.card K₀ := by
      show 4 ≤ Nat.card h.fixedField
      rw [h.card_fixedField]
      omega
    have hSL : Group.IsPerfect (SpecialLinearGroup (Fin 2) K₀) :=
      CFSG.ClassicalInvolution.sl2_isPerfect h4
    exact Or.inl (Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι₂))

end CFSG.GH74.Generic.S1.Uni
