module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4QAlg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCInner

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

theorem fix_commutator {G : Type*} [Group G] {Z : Subgroup G} (hZ : Z ≤ center G) (θ : G →* G)
    {g h : G} (hg : θ g * g⁻¹ ∈ Z) (hh : θ h * h⁻¹ ∈ Z) : θ ⁅g, h⁆ = ⁅g, h⁆ := by
  set zg := θ g * g⁻¹
  set zh := θ h * h⁻¹
  have hθg : θ g = zg * g := by simp [zg]
  have hθh : θ h = zh * h := by simp [zh]
  have hcg := mem_center_iff.mp (hZ hg)
  have hch := mem_center_iff.mp (hZ hh)
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hθg, hθh]
  have hc1 : ∀ X : G, zg * X * zg⁻¹ = X := fun X => by rw [← hcg X, mul_inv_cancel_right]
  have hc2 : ∀ X : G, zh * X * zh⁻¹ = X := fun X => by rw [← hch X, mul_inv_cancel_right]
  have hgz : g * zh = zh * g := hch g
  calc zg * g * (zh * h) * (zg * g)⁻¹ * (zh * h)⁻¹ =
      zg * (g * zh * h * g⁻¹) * zg⁻¹ * (h⁻¹ * zh⁻¹) := by group
    _ = g * zh * h * g⁻¹ * (h⁻¹ * zh⁻¹) := by rw [hc1]
    _ = zh * (g * h * g⁻¹ * h⁻¹) * zh⁻¹ := by rw [hgz]; group
    _ = g * h * g⁻¹ * h⁻¹ := hc2 _

variable {K : Type} [Field K]

theorem perfect_le_map_eqLocus (A : gsp 2 K) {N : Subgroup (StatedProj (StatedSp 2 K))}
    (hN : ∀ x ∈ N, conjAut 2 K A x = x) (hperf : ⁅N, N⁆ = N) :
    N ≤ (MonoidHom.eqLocus (conjSp 2 K A).toMonoidHom (MonoidHom.id _)).map (proj 2 K) := by
  have hfix : ∀ x ∈ N, ∃ g, proj 2 K g = x ∧ conjSp 2 K A g * g⁻¹ ∈ spScalars 2 K := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, rfl, ?_⟩
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← conjAut_proj, hN _ hx,
      mul_inv_cancel]
  rw [← hperf, commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl, hg⟩ := hfix x hx
  obtain ⟨h, rfl, hh⟩ := hfix y hy
  refine ⟨⁅g, h⁆, ?_, map_commutatorElement _ _ _⟩
  exact fix_commutator (fun z hz => mem_center_of_mem_spScalars hz)
    (conjSp 2 K A).toMonoidHom hg hh

variable (a : K)

@[expose] def bA : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 1 0 0 (dA a)

@[expose] def bAinv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 1 0 0 (dAinv a)

variable {a}

theorem bA_mul_bAinv (ha : a ≠ 0) : bA a * bAinv a = 1 := by
  rw [bA, bAinv, fromBlocks_multiply, dA_mul_dAinv ha, ← fromBlocks_one]
  simp

theorem bAinv_mul_bA (ha : a ≠ 0) : bAinv a * bA a = 1 := by
  rw [bA, bAinv, fromBlocks_multiply, dAinv_mul_dA ha, ← fromBlocks_one]
  simp

theorem dA_transpose : (dA a)ᵀ = dA a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dA]

theorem dAinv_transpose : (dAinv a)ᵀ = dAinv a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dAinv]

theorem bA_transpose_formJ_bA : (bA a)ᵀ * formJ 2 K * bA a = kron J₁ (dA a) := by
  simp only [bA, formJ, fromBlocks_transpose, fromBlocks_multiply, kron, J₁, transpose_one,
    transpose_zero, dA_transpose]
  simp

theorem bAinv_transpose_kron_bAinv (ha : a ≠ 0) :
    (bAinv a)ᵀ * kron J₁ (dA a) * bAinv a = formJ 2 K := by
  rw [← bA_transpose_formJ_bA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul,
    bA_mul_bAinv ha, transpose_one, Matrix.one_mul, Matrix.mul_assoc, bA_mul_bAinv ha,
    Matrix.mul_one]

theorem bA_conj_symplectic (ha : a ≠ 0) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX : Xᵀ * kron J₁ (dA a) * X = kron J₁ (dA a)) :
    (bA a * X * bAinv a)ᵀ * formJ 2 K * (bA a * X * bAinv a) = formJ 2 K := by
  have : (bA a * X * bAinv a)ᵀ * formJ 2 K * (bA a * X * bAinv a) =
      (bAinv a)ᵀ * (Xᵀ * ((bA a)ᵀ * formJ 2 K * bA a) * X) * bAinv a := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [this, bA_transpose_formJ_bA, hX, bAinv_transpose_kron_bAinv ha]

theorem kron_smul_right' (g h : Matrix (Fin 2) (Fin 2) K) (c : K) :
    kron g (c • h) = c • kron g h := by
  simp only [kron, fromBlocks_smul, smul_smul, mul_comm c]

theorem sA_transpose_dA_sA : (sA a)ᵀ * dA a * sA a = (-a) • dA a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, dA, Matrix.mul_apply, Fin.sum_univ_two]

theorem kron_one_sA_twisted :
    (kron 1 (sA a))ᵀ * kron J₁ (dA a) * kron 1 (sA a) = (-a) • kron J₁ (dA a) := by
  rw [kron_transpose, kron_mul, kron_mul, transpose_one, Matrix.one_mul, Matrix.mul_one,
    sA_transpose_dA_sA, kron_smul_right']

variable (a) in
@[expose] def aI : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := bA a * kron 1 (sA a) * bAinv a

theorem aI_symplectic (ha : a ≠ 0) :
    (aI a)ᵀ * formJ 2 K * aI a = (-a) • formJ 2 K := by
  have : (aI a)ᵀ * formJ 2 K * aI a =
      (bAinv a)ᵀ * ((kron 1 (sA a))ᵀ * ((bA a)ᵀ * formJ 2 K * bA a) * kron 1 (sA a)) *
        bAinv a := by
    simp only [aI, transpose_mul, Matrix.mul_assoc]
  rw [this, bA_transpose_formJ_bA, kron_one_sA_twisted, Matrix.mul_smul, Matrix.smul_mul,
    bAinv_transpose_kron_bAinv ha]

theorem aI_mul_aI (ha : a ≠ 0) : aI a * aI a = a • 1 := by
  have hs : sA a * sA a = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [sA_mul_sA, zero_smul, add_zero]
  calc aI a * aI a = bA a * (kron 1 (sA a) * (bAinv a * bA a) * kron 1 (sA a)) * bAinv a := by
        simp only [aI, Matrix.mul_assoc]
    _ = a • 1 := by
        rw [bAinv_mul_bA ha, Matrix.mul_one, kron_mul, Matrix.one_mul, hs, kron_smul_right',
          kron_one_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, bA_mul_bAinv ha]

theorem isUnit_det_aI (ha : a ≠ 0) : IsUnit (aI a).det := by
  have h := congrArg Matrix.det (aI_mul_aI ha)
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_sum, Fintype.card_fin] at h
  exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, mul_zero] at h; exact pow_ne_zero _ ha h.symm)

@[expose] def aIgsp (ha : a ≠ 0) : gsp 2 K :=
  ⟨nonsingInvUnit (aI a) (isUnit_det_aI ha), ⟨Units.mk0 (-a) (neg_ne_zero.mpr ha), by
    rw [Units.val_mk0]
    exact aI_symplectic ha⟩⟩

theorem coe_aIgsp (ha : a ≠ 0) :
    (((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      aI a := rfl

@[expose] def alphaI (ha : a ≠ 0) : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K (aIgsp ha)

theorem kron_sl_twisted (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    (kron (k : Matrix (Fin 2) (Fin 2) K) 1)ᵀ * kron J₁ (dA a) * kron k 1 = kron J₁ (dA a) := by
  rw [kron_transpose, kron_mul, kron_mul, transpose_one, Matrix.one_mul, Matrix.mul_one,
    show (k : Matrix (Fin 2) (Fin 2) K)ᵀ * J₁ * (k : Matrix (Fin 2) (Fin 2) K) =
      (k : Matrix (Fin 2) (Fin 2) K).det • J₁ from transpose_mul_J₁_mul _, k.2, one_smul]

@[expose] def gI (ha : a ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K where
  toFun k := toSp (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a)
    (bA_conj_symplectic ha (kron_sl_twisted k))
  map_one' := sp_ext (by
    rw [coe_toSp, Matrix.SpecialLinearGroup.coe_one, kron_one_one, Matrix.mul_one,
      bA_mul_bAinv ha]
    rfl)
  map_mul' k l := sp_ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_toSp, coe_toSp, coe_toSp,
      Matrix.SpecialLinearGroup.coe_mul]
    calc bA a * kron ((k : Matrix (Fin 2) (Fin 2) K) * (l : Matrix (Fin 2) (Fin 2) K)) 1 *
          bAinv a =
        bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * (bAinv a * bA a) * kron
          (l : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a := by
          rw [bAinv_mul_bA ha, Matrix.mul_one, Matrix.mul_assoc (bA a)
            (kron (k : Matrix (Fin 2) (Fin 2) K) 1), kron_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc])

theorem coe_gI (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((gI ha k : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 *
        bAinv a := rfl

@[expose] def JI (ha : a ≠ 0) : Subgroup (StatedProj (StatedSp 2 K)) :=
  (gI ha).range.map (proj 2 K)

theorem bA_eq_blk : bA a = blk 1 (dA a) := by
  simp only [bA, blk, dA, diag2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem bAinv_eq_blk : bAinv a = blk 1 (dAinv a) := by
  simp only [bAinv, blk, dAinv, diag2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem kron_one_sA_mul_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    kron 1 (sA a) * blk g h = blk h g * kron 1 (sA a) := by
  simp only [kron, blk, diag2, sA, fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem diag_one_neg_one_eq_blk : kron 1 (diag2 (1 : K) (-1)) = blk 1 (-1) := by
  simp only [kron, blk, diag2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem aI_mul_T1 : aI a * kron 1 (diag2 1 (-1)) = -(kron 1 (diag2 1 (-1)) * aI a) := by
  have h1 : bAinv a * kron 1 (diag2 1 (-1)) = kron 1 (diag2 1 (-1)) * bAinv a := by
    rw [bAinv_eq_blk, diag_one_neg_one_eq_blk, blk_mul, blk_mul]
    simp
  have h2 : bA a * kron 1 (diag2 1 (-1)) = kron 1 (diag2 1 (-1)) * bA a := by
    rw [bA_eq_blk, diag_one_neg_one_eq_blk, blk_mul, blk_mul]
    simp
  have h3 : kron 1 (sA a) * kron 1 (diag2 1 (-1)) = -(kron 1 (diag2 1 (-1)) * kron 1 (sA a)) := by
    rw [kron_mul, kron_mul, ← kron_neg_right]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sA, diag2]
  calc aI a * kron 1 (diag2 1 (-1)) = bA a * (kron 1 (sA a) * kron 1 (diag2 1 (-1))) * bAinv a := by
        rw [aI, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (bA a)]
    _ = -(kron 1 (diag2 1 (-1)) * aI a) := by
        rw [h3, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, h2, aI]
        simp only [Matrix.mul_assoc]

theorem alphaI_u1 (ha : a ≠ 0) : alphaI ha (u1 K) = u1 K := by
  rw [alphaI, u1, conjAut_proj]
  symm
  apply proj_eq_of_eq_or_neg
  right
  set A : GL (Fin 2 ⊕ Fin 2) K := ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = aI a := rfl
  rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA, coe_T1', aI_mul_T1,
    Matrix.neg_mul, Matrix.mul_assoc, ← hA, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem T1mat_comm_bA : kron 1 (diag2 (1 : K) (-1)) * bA a = bA a * kron 1 (diag2 1 (-1)) := by
  rw [bA_eq_blk, diag_one_neg_one_eq_blk, blk_mul, blk_mul]
  simp

theorem T1mat_comm_bAinv :
    kron 1 (diag2 (1 : K) (-1)) * bAinv a = bAinv a * kron 1 (diag2 1 (-1)) := by
  rw [bAinv_eq_blk, diag_one_neg_one_eq_blk, blk_mul, blk_mul]
  simp

theorem T1mat_comm_gI (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    kron 1 (diag2 (1 : K) (-1)) * (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) =
      (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) * kron 1 (diag2 1 (-1)) := by
  have hk : kron 1 (diag2 (1 : K) (-1)) * kron (k : Matrix (Fin 2) (Fin 2) K) 1 =
      kron (k : Matrix (Fin 2) (Fin 2) K) 1 * kron 1 (diag2 1 (-1)) := by
    rw [kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  calc kron 1 (diag2 (1 : K) (-1)) * (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) =
      bA a * (kron 1 (diag2 1 (-1)) * kron (k : Matrix (Fin 2) (Fin 2) K) 1) * bAinv a := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, T1mat_comm_bA, Matrix.mul_assoc (bA a)]
    _ = _ := by
        rw [hk, Matrix.mul_assoc, Matrix.mul_assoc, T1mat_comm_bAinv]
        simp only [Matrix.mul_assoc]

theorem u1_commute_JI (ha : a ≠ 0) {l : StatedProj (StatedSp 2 K)} (hl : l ∈ JI ha) :
    u1 K * l = l * u1 K := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hl
  rw [u1, ← map_mul, ← map_mul]
  congr 1
  apply sp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T1', coe_gI,
    T1mat_comm_gI]

theorem JI_le_X0 (ha : a ≠ 0) : JI ha ≤ X0 K := by
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  refine ⟨gI ha k, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  apply sp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T1', coe_gI,
    T1mat_comm_gI]

theorem JI_le_E1_sup_E2 (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) : JI ha ≤ E1 K ⊔ E2 K := by
  intro x hx
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := exists_mul_of_mem_X0 h2 (JI_le_X0 ha hx)
  exact mul_mem (mem_sup_left he₁) (mem_sup_right he₂)

theorem aI_comm_gI (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    aI a * (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) =
      (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) * aI a := by
  have hk : kron 1 (sA a) * kron (k : Matrix (Fin 2) (Fin 2) K) 1 =
      kron (k : Matrix (Fin 2) (Fin 2) K) 1 * kron 1 (sA a) := by
    rw [kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  calc aI a * (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) =
      bA a * (kron 1 (sA a) * kron (k : Matrix (Fin 2) (Fin 2) K) 1) * bAinv a := by
        simp only [aI, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]
    _ = (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) * aI a := by
        rw [hk]
        simp only [aI, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]

theorem alphaI_JI (ha : a ≠ 0) {l : StatedProj (StatedSp 2 K)} (hl : l ∈ JI ha) :
    alphaI ha l = l := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hl
  rw [alphaI, conjAut_proj]
  congr 1
  apply sp_ext
  set A : GL (Fin 2 ⊕ Fin 2) K := ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = aI a := rfl
  rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA, coe_gI, aI_comm_gI ha,
    Matrix.mul_assoc, ← hA, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

@[expose] def conjD (ha : a ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨dA a * g * dAinv a, by
    rw [det_mul, det_mul, g.2, mul_one, ← det_mul, dA_mul_dAinv ha, det_one]⟩

theorem aI_mul_blk (ha : a ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) :
    aI a * blk g 1 = blk 1 (dA a * g * dAinv a) * aI a := by
  have hl : aI a * blk g 1 = blk (dAinv a) (dA a * g) * kron 1 (sA a) := by
    rw [aI, bA_eq_blk, bAinv_eq_blk, Matrix.mul_assoc, blk_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, kron_one_sA_mul_blk, ← Matrix.mul_assoc, blk_mul, Matrix.one_mul]
  have hr : blk 1 (dA a * g * dAinv a) * aI a = blk (dAinv a) (dA a * g) * kron 1 (sA a) := by
    rw [aI, bA_eq_blk, bAinv_eq_blk, ← Matrix.mul_assoc, ← Matrix.mul_assoc, blk_mul,
      Matrix.one_mul, Matrix.mul_assoc (dA a * g), dAinv_mul_dA ha, Matrix.mul_one,
      Matrix.mul_assoc, kron_one_sA_mul_blk, ← Matrix.mul_assoc, blk_mul, Matrix.one_mul,
      Matrix.mul_one]
  rw [hl, hr]

theorem alphaI_blkSL (ha : a ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    alphaI ha (proj 2 K (blkSL K (g, 1))) = proj 2 K (blkSL K (1, conjD ha g)) := by
  rw [alphaI, conjAut_proj]
  congr 1
  apply sp_ext
  set A : GL (Fin 2 ⊕ Fin 2) K := ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = aI a := rfl
  rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA, coe_blkSL, coe_blkSL,
    Matrix.SpecialLinearGroup.coe_one, aI_mul_blk ha, Matrix.mul_assoc, ← hA, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rfl

@[expose] def conjDinv (ha : a ≠ 0) (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨dAinv a * h * dA a, by
    rw [det_mul, det_mul, h.2, mul_one, ← det_mul, dAinv_mul_dA ha, det_one]⟩

theorem conjD_conjDinv (ha : a ≠ 0) (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjD ha (conjDinv ha h) = h := by
  ext i j
  change (dA a * (dAinv a * (h : Matrix (Fin 2) (Fin 2) K) * dA a) * dAinv a) i j = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dA_mul_dAinv ha, Matrix.one_mul, Matrix.mul_assoc,
    dA_mul_dAinv ha, Matrix.mul_one]

theorem E2_le_map_E1_alphaI (ha : a ≠ 0) :
    E2 K ≤ (E1 K).map (alphaI ha).toMonoidHom := by
  intro y hy
  obtain ⟨h, rfl⟩ := mem_E2.mp hy
  refine ⟨proj 2 K (blkSL K (conjDinv ha h, 1)), mem_E1.mpr ⟨_, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom]
  rw [alphaI_blkSL, conjD_conjDinv]

theorem map_E1_alphaI_ne (ha : a ≠ 0) : (E1 K).map (alphaI ha).toMonoidHom ≠ E1 K := by
  intro h
  set g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  have hy : proj 2 K (blkSL K (1, g)) ∈ E1 K := h ▸ E2_le_map_E1_alphaI ha (mem_E2.mpr ⟨g, rfl⟩)
  obtain ⟨g', hg'⟩ := mem_E1.mp hy
  rcases eq_or_eq_neg_of_proj_eq hg' with e | e <;>
    simp only [coe_blkSL, Matrix.SpecialLinearGroup.coe_one] at e
  · obtain ⟨-, e2⟩ := blk_injective _ _ _ _ e
    have := congrFun (congrFun e2 0) 1
    simp [g] at this
  · rw [blk_neg] at e
    obtain ⟨-, e2⟩ := blk_injective _ _ _ _ e
    have := congrFun (congrFun e2 0) 1
    simp [g] at this

theorem tcWitness_alphaI [Finite K] (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    TCWitness (alphaI ha) (JI ha) :=
  ⟨u1 K, u1_mul_u1, u1_ne_one h2, alphaI_u1 ha, fun _ hj => u1_commute_JI ha hj, E1 K,
    E1_le_centralizer_u1 h2, isComponent_E1 h2 h4, map_E1_alphaI_ne ha,
    (JI_le_E1_sup_E2 ha h2).trans (sup_le_sup_left (E2_le_map_E1_alphaI ha) _)⟩

variable (a) in
abbrev fixI (ha : a ≠ 0) : Subgroup (StatedSp 2 K) :=
  MonoidHom.eqLocus (conjSp 2 K (aIgsp ha)).toMonoidHom (MonoidHom.id _)

theorem commute_aI_of_mem_fixI (ha : a ≠ 0) {g : StatedSp 2 K} (hg : g ∈ fixI a ha) :
    aI a * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * aI a := by
  have h : conjSp 2 K (aIgsp ha) g = g := hg
  have h' := congrArg (fun x : StatedSp 2 K =>
    ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  set A : GL (Fin 2 ⊕ Fin 2) K := ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = aI a := rfl
  rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA] at h'
  calc aI a * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      aI a * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * A) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * aI a := by
        rw [← Matrix.mul_assoc, h', hA]

theorem bAinv_mul_commute (ha : a ≠ 0) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX : aI a * X = X * aI a) :
    bAinv a * X * bA a * kron 1 (sA a) = kron 1 (sA a) * (bAinv a * X * bA a) := by
  have hk : kron 1 (sA a) = bAinv a * aI a * bA a := by
    rw [aI, ← Matrix.mul_assoc, ← Matrix.mul_assoc, bAinv_mul_bA ha, Matrix.one_mul,
      Matrix.mul_assoc, bAinv_mul_bA ha, Matrix.mul_one]
  rw [hk]
  calc bAinv a * X * bA a * (bAinv a * aI a * bA a) =
      bAinv a * (X * aI a) * bA a := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bA a) (bAinv a), bA_mul_bAinv ha, Matrix.one_mul]
    _ = bAinv a * (aI a * X) * bA a := by rw [hX]
    _ = bAinv a * aI a * bA a * (bAinv a * X * bA a) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bA a) (bAinv a), bA_mul_bAinv ha, Matrix.one_mul]

theorem bAinv_conj_twisted (ha : a ≠ 0) (g : StatedSp 2 K) :
    (bAinv a * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      bA a)ᵀ * kron J₁ (dA a) * (bAinv a * ((g : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * bA a) = kron J₁ (dA a) := by
  have hg := symplectic_of_mem g
  have : (bAinv a * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      bA a)ᵀ * kron J₁ (dA a) * (bAinv a * ((g : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * bA a) =
      (bA a)ᵀ * (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
        ((bAinv a)ᵀ * kron J₁ (dA a) * bAinv a) * ((g : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * bA a := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [this, bAinv_transpose_kron_bAinv ha, hg, bA_transpose_formJ_bA]

@[expose] def blocksI (ha : a ≠ 0) (g : fixI a ha) :
    Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0) :=
  (exists_qBlock_of_commute a (bAinv_mul_commute ha (commute_aI_of_mem_fixI ha g.2))).choose

theorem qBlock_blocksI (ha : a ≠ 0) (g : fixI a ha) :
    qBlock a (blocksI ha g) = bAinv a * (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * bA a :=
  (exists_qBlock_of_commute a (bAinv_mul_commute ha (commute_aI_of_mem_fixI ha g.2))).choose_spec

theorem blocksI_mul (ha : a ≠ 0) (g h : fixI a ha) :
    blocksI ha (g * h) = blocksI ha g * blocksI ha h := by
  apply qBlock_injective a
  rw [qBlock_mul, qBlock_blocksI, qBlock_blocksI, qBlock_blocksI]
  change bAinv a * ((((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) *
    ((h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * bA a = _
  rw [Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bA a) (bAinv a), bA_mul_bAinv ha, Matrix.one_mul]

theorem blocksI_one (ha : a ≠ 0) : blocksI ha 1 = 1 := by
  apply qBlock_injective a
  rw [qBlock_blocksI, qBlock_one]
  change bAinv a * (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * bA a = 1
  rw [Matrix.mul_one, bAinv_mul_bA ha]

@[expose] def detI (ha : a ≠ 0) : fixI a ha →* QuadraticAlgebra K a 0 where
  toFun g := (blocksI ha g).det
  map_one' := by rw [blocksI_one, det_one]
  map_mul' g h := by rw [blocksI_mul, det_mul]

theorem mem_range_gI_of_detI (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (g : fixI a ha)
    (h : detI ha g = 1) : (g : StatedSp 2 K) ∈ (gI ha).range := by
  have hsym : (blocksI ha g)ᴴ * jE a * blocksI ha g = jE a := by
    rw [← qBlock_symplectic_iff ha, qBlock_blocksI]
    exact bAinv_conj_twisted ha g
  obtain ⟨k, hk, hZ⟩ := exists_map_of_det_eq_one_qAlg h2 hsym h
  refine ⟨(⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) K), sp_ext ?_⟩
  have h1 := qBlock_blocksI ha g
  rw [hZ, qBlock_map] at h1
  change bA a * kron k 1 * bAinv a = _
  rw [h1]
  simp only [Matrix.mul_assoc]
  rw [bA_mul_bAinv ha, Matrix.mul_one, ← Matrix.mul_assoc, bA_mul_bAinv ha, Matrix.one_mul]

theorem commutator_fixI_le (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    ⁅fixI a ha, fixI a ha⁆ ≤ (gI ha).range := by
  rw [commutator_le]
  intro x hx y hy
  have h1 : detI ha ⁅(⟨x, hx⟩ : fixI a ha), ⟨y, hy⟩⁆ = 1 := by
    have h := map_commutatorElement (detI ha).toHomUnits ⟨x, hx⟩ ⟨y, hy⟩
    have h' : ⁅(detI ha).toHomUnits ⟨x, hx⟩, (detI ha).toHomUnits ⟨y, hy⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    exact congrArg Units.val (h.trans h')
  exact mem_range_gI_of_detI ha h2 _ h1

theorem perfect_le_JI (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) {N : Subgroup (StatedProj (StatedSp 2 K))}
    (hN : ∀ x ∈ N, alphaI ha x = x) (hperf : ⁅N, N⁆ = N) : N ≤ JI ha := by
  have h1 := perfect_le_map_eqLocus (aIgsp ha) hN hperf
  rw [← hperf]
  calc ⁅N, N⁆ ≤ ⁅(fixI a ha).map (proj 2 K), (fixI a ha).map (proj 2 K)⁆ :=
        commutator_mono h1 h1
    _ = ⁅fixI a ha, fixI a ha⁆.map (proj 2 K) := (Subgroup.map_commutator _ _ _).symm
    _ ≤ JI ha := map_mono (commutator_fixI_le ha h2)

theorem bA_conj_eq_iff (ha : a ≠ 0) {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : bA a * X * bAinv a = bA a * Y * bAinv a) : X = Y := by
  have h1 := congrArg (fun M => bAinv a * M * bA a) h
  simp only [Matrix.mul_assoc] at h1
  rwa [bAinv_mul_bA ha, Matrix.mul_one, ← Matrix.mul_assoc, bAinv_mul_bA ha,
    Matrix.one_mul, ← Matrix.mul_assoc, bAinv_mul_bA ha, Matrix.one_mul, Matrix.mul_one] at h1

theorem ker_proj_comp_gI (ha : a ≠ 0) :
    ((proj 2 K).comp (gI ha)).ker = center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff,
    coe_gI, Matrix.SpecialLinearGroup.mem_center_iff]
  have h1 : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = bA a * 1 * bAinv a := by
    rw [Matrix.mul_one, bA_mul_bAinv ha]
  have hm : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = bA a * (-1) * bAinv a := by
    rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, bA_mul_bAinv ha]
  constructor
  · rintro (h | h)
    · rw [h1] at h
      have h' := bA_conj_eq_iff ha h
      rw [← kron_one_one] at h'
      refine ⟨1, one_pow _, ?_⟩
      rw [kron_one_injective h']
      simp
    · rw [hm] at h
      have h' := bA_conj_eq_iff ha h
      rw [← kron_neg_one_one] at h'
      refine ⟨-1, by simp, ?_⟩
      rw [kron_one_injective h']
      ext i j
      by_cases hij : i = j <;> simp [hij, one_apply]
  · rintro ⟨r, hr, hg⟩
    rw [Fintype.card_fin, pow_two] at hr
    rw [← hg]
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl
    · left
      rw [map_one, kron_one_one, Matrix.mul_one, bA_mul_bAinv ha]
    · right
      rw [map_neg, map_one, kron_neg_one_one, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
        bA_mul_bAinv ha]

@[expose] def JIEquiv (ha : a ≠ 0) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* JI ha :=
  (QuotientGroup.quotientMulEquivOfEq (ker_proj_comp_gI ha).symm).trans
    ((QuotientGroup.quotientKerEquivRange ((proj 2 K).comp (gI ha))).trans
      (MulEquiv.subgroupCongr (MonoidHom.range_comp _ _)))

theorem isSimpleGroup_JI [Finite K] (ha : a ≠ 0) (h4 : 4 ≤ Nat.card K) : IsSimpleGroup (JI ha) :=
  (JIEquiv ha).isSimpleGroup_congr.mp (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)

abbrev fixAlphaI (ha : a ≠ 0) : Subgroup (StatedProj (StatedSp 2 K)) :=
  MonoidHom.eqLocus (alphaI ha).toMonoidHom (MonoidHom.id _)

theorem JI_le_fix (ha : a ≠ 0) : JI ha ≤ fixAlphaI ha := fun _ hl => alphaI_JI ha hl

theorem pComponent_fix_alphaI [Finite K] (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMX : M ≤ fixAlphaI ha)
    (hM : CFSG.IsPComponent 2 (M.subgroupOf (fixAlphaI ha))) : M = JI ha := by
  have hperf := commutator_eq_of_isPComponent hMX hM
  have hne := ne_bot_of_isPComponent hM
  have hML := perfect_le_JI ha h2 (fun x hx => hMX hx) hperf
  set X := fixAlphaI ha
  have hLX : JI ha ≤ X := JI_le_fix ha
  have : IsSimpleGroup (JI ha) := isSimpleGroup_JI ha h4
  have hsimp : IsSimpleGroup ((JI ha).subgroupOf X) :=
    (Subgroup.subgroupOfEquivOfLe hLX).isSimpleGroup_congr.mpr inferInstance
  have hsub : ((M.subgroupOf X).subgroupOf ((JI ha).subgroupOf X)).IsSubnormal :=
    hM.choose_spec.2.1.subgroupOf
  rcases hsub.eq_bot_or_top_of_isSimpleGroup hsimp with hbot | htop
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    apply hne
    have hle : M.subgroupOf X ≤ (JI ha).subgroupOf X := Subgroup.subgroupOf_mono _ hML
    have hMb : M.subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact hbot.le_bot ⟨hx, hle hx⟩
    rw [eq_bot_iff]
    intro m hm
    have : (⟨m, hMX hm⟩ : X) ∈ M.subgroupOf X := hm
    rw [hMb] at this
    exact congrArg Subtype.val this
  · rw [Subgroup.subgroupOf_eq_top] at htop
    refine le_antisymm hML fun l hl => ?_
    exact htop (show (⟨l, hLX hl⟩ : X) ∈ (JI ha).subgroupOf X from hl)

end CFSG.ComponentClassification.CatFactsSp4
