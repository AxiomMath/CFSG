module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.RankThree.PartOne.S11c.G2Pgl
public import CFSG.RankThree.PartOne.S11c.G2Transport

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open Subgroup CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
open scoped MatrixGroups

section Native

variable {F : Type} [Field F]

@[expose] def a₀ (F : Type) [Field F] : Fin Tag.G2.rank → Fˣ := ![1, -1]

theorem a₀_sign (i : Fin Tag.G2.rank) : (a₀ F) i = 1 ∨ (a₀ F) i = -1 := by
  fin_cases i
  · left; rfl
  · right; rfl

theorem hpair : G2SignPair (g2v 1 0) (g2v 1 2) := Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem HSL_neg_one_eq_neg_one : (HSL (-1 : Fˣ) : SL(2, F)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem exists_unit_sq {u : Fˣ} (h : IsSquare (u : F)) : ∃ lam : Fˣ, u = lam ^ 2 := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, sq])⟩

theorem det_toGL_one (B : SL(2, F)) :
    Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL B) = 1 :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.det_coe, Units.val_one])

theorem WSL_mul_WSL : (WSL : SL(2, F)) * WSL = HSL (-1) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [WSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjSL_eq_conjSLAut (M : GL (Fin 2) F) (A : SL(2, F)) :
    conjSL M A = conjSLAut M A :=
  Subtype.ext (by rw [coe_conjSL, conjSLAut_coe])

theorem g2a_eq : CFSG.ComponentClassification.UnbalancedCatalog.g2a = g2v 1 0 := rfl

theorem g2v_eq : CFSG.ComponentClassification.UnbalancedCatalog.g2v = g2v 1 2 := rfl

@[expose] def cν (ν : Fˣ) : Fin Tag.G2.rank → Fˣ := ![ν, 1]

theorem rootChar_cν_α (ν : Fˣ) : rootChar (cν ν) (g2v 1 0) = ν := by
  change (∏ i : Fin 2, (cν ν) i ^ (g2v 1 0) i) = ν
  simp [cν, Fin.prod_univ_two]

theorem rootChar_cν_β (ν : Fˣ) : rootChar (cν ν) (g2v 1 2) = ν := by
  change (∏ i : Fin 2, (cν ν) i ^ (g2v 1 2) i) = ν
  simp [cν, Fin.prod_univ_two]

variable (F) in
noncomputable abbrev gν (ν : Fˣ) : GL (Fin 2) F :=
  diagUnitOne ν * Matrix.SpecialLinearGroup.toGL (WSL : SL(2, F))

theorem det_gν (ν : Fˣ) : Matrix.GeneralLinearGroup.det (gν F ν) = ν := by
  rw [map_mul, det_diagUnitOne, det_toGL_one, mul_one]

section Certified


theorem isRoot_α : IsRoot Tag.G2 (g2v 1 0) := (g2_pair_isRoot hpair).1

theorem isRoot_β : IsRoot Tag.G2 (g2v 1 2) := (g2_pair_isRoot hpair).2

variable (F) in
abbrev rhoA : SL(2, F) →* ModGL .G2 F := rootSL2 .G2 F (g2v 1 0)

variable (F) in
abbrev rhoB : SL(2, F) →* ModGL .G2 F := rootSL2 .G2 F (g2v 1 2)

theorem rhoA_injective : Function.Injective (rhoA F) := rootSL2_injective_of_field _

theorem rhoB_injective : Function.Injective (rhoB F) := rootSL2_injective_of_field _

theorem rhoA_rhoB_comm (A B : SL(2, F)) : rhoA F A * rhoB F B = rhoB F B * rhoA F A :=
  (g2_pair_commute hpair A B).eq

theorem rhoA_mem (A : SL(2, F)) : rhoA F A ∈ adjointGroup .G2 F :=
  (exceptional_Lang_root_rank_one_data .G2 F (g2v 1 0)).2.2.2.2.1 A

theorem rhoB_mem (A : SL(2, F)) : rhoB F A ∈ adjointGroup .G2 F :=
  (exceptional_Lang_root_rank_one_data .G2 F (g2v 1 2)).2.2.2.2.1 A

variable (F) in
abbrev dsign : ModGL .G2 F := rootDiagUnit .G2 (a₀ F)

theorem rhoA_neg_one : rhoA F (HSL (-1)) = dsign F := by
  rw [rootSL2_HSL_eq_rootDiagUnit isRoot_α (g2v 2 (-1)) g2_hm_10 (-1)]
  congr 1
  funext i
  fin_cases i
  · show (-1 : Fˣ) ^ (2 : ℤ) = 1
    norm_num
  · show (-1 : Fˣ) ^ (-1 : ℤ) = -1
    norm_num

theorem rhoB_neg_one : rhoB F (HSL (-1)) = dsign F :=
  (g2_pair_HSL_neg_one hpair).symm.trans rhoA_neg_one

theorem dsign_mem : dsign F ∈ adjointGroup .G2 F := by
  rw [← rhoA_neg_one]; exact rhoA_mem _

theorem dsign_sq : dsign F * dsign F = 1 := by
  rw [← rhoA_neg_one]; exact rootSL2_neg_one_sq _

theorem rootDiagUnit_mem_torus (b : Fin Tag.G2.rank → Fˣ) :
    rootDiagUnit .G2 b ∈ torusGroup .G2 F := by
  have c00 : Tag.G2.cartan 0 0 = 2 := by decide
  have c01 : Tag.G2.cartan 0 1 = -1 := by decide
  have c10 : Tag.G2.cartan 1 0 = -3 := by decide
  have c11 : Tag.G2.cartan 1 1 = 2 := by decide
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1 : Fˣ, b = ![b0, b1] :=
    ⟨b 0, b 1, funext fun i => by fin_cases i <;> rfl⟩
  have h : rootDiagUnit .G2 (![b0, b1] : Fin Tag.G2.rank → Fˣ) =
      torusElt .G2 F 0 (b0 ^ 2 * b1 ^ 3) * torusElt .G2 F 1 (b0 * b1 ^ 2) := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext j
    fin_cases j
    · show b0 = (b0 ^ 2 * b1 ^ 3) ^ Tag.G2.cartan 0 0 * (b0 * b1 ^ 2) ^ Tag.G2.cartan 1 0
      rw [c00, c10]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      have := b0.ne_zero
      have := b1.ne_zero
      field_simp
    · show b1 = (b0 ^ 2 * b1 ^ 3) ^ Tag.G2.cartan 0 1 * (b0 * b1 ^ 2) ^ Tag.G2.cartan 1 1
      rw [c01, c11]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      have := b0.ne_zero
      have := b1.ne_zero
      field_simp
  rw [h]
  exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem rootDiagUnit_mem_adjoint (b : Fin Tag.G2.rank → Fˣ) :
    rootDiagUnit .G2 b ∈ adjointGroup .G2 F :=
  (torusGroup_le_toralCentralizer (a₀ F) (rootDiagUnit_mem_torus b)).1

theorem rhoA_comm_dsign (A : SL(2, F)) : rhoA F A * dsign F = dsign F * rhoA F A := by
  rw [← rhoB_neg_one]
  exact rhoA_rhoB_comm A _

theorem rhoB_comm_dsign (B : SL(2, F)) : rhoB F B * dsign F = dsign F * rhoB F B := by
  rw [← rhoA_neg_one]
  exact (rhoA_rhoB_comm _ B).symm

theorem rhoA_neg_one' : rhoA F (-1) = dsign F := by
  rw [← HSL_neg_one_eq_neg_one]
  exact rhoA_neg_one

theorem rhoB_neg_one' : rhoB F (-1) = dsign F := by
  rw [← HSL_neg_one_eq_neg_one]
  exact rhoB_neg_one

variable (F) in
abbrev G2g : Type := ↥(adjointGroup .G2 F)

variable (F) in
abbrev z₀ : G2g F := ⟨dsign F, dsign_mem⟩

variable (F) in
abbrev Yg : Type := ↥(Subgroup.centralizer ({z₀ F} : Set (G2g F)))

variable (F) in
@[expose] def toMod : Yg F →* ModGL .G2 F :=
  (adjointGroup .G2 F).subtype.comp (Subgroup.centralizer ({z₀ F} : Set (G2g F))).subtype

theorem toMod_apply (y : Yg F) : toMod F y = ((y : G2g F) : ModGL .G2 F) := rfl

theorem toMod_injective : Function.Injective (toMod F) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toMod_mem_toralCentralizer (y : Yg F) :
    toMod F y ∈ toralCentralizer .G2 F (a₀ F) := by
  refine mem_toralCentralizer.2 ⟨y.1.2, ?_⟩
  have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  exact mul_inv_eq_iff_eq_mul.2 h.symm

variable (F) in
@[expose] def chartA : SL(2, F) →* Yg F :=
  ((rhoA F).codRestrict (adjointGroup .G2 F) rhoA_mem).codRestrict _ fun A => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (rhoA_comm_dsign A)

variable (F) in
@[expose] def chartB : SL(2, F) →* Yg F :=
  ((rhoB F).codRestrict (adjointGroup .G2 F) rhoB_mem).codRestrict _ fun A => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (rhoB_comm_dsign A)

theorem toMod_chartA (A : SL(2, F)) : toMod F (chartA F A) = rhoA F A := rfl

theorem toMod_chartB (A : SL(2, F)) : toMod F (chartB F A) = rhoB F A := rfl

theorem chartA_injective : Function.Injective (chartA F) := fun _ _ h =>
  rhoA_injective (congrArg (toMod F) h)

theorem chartB_injective : Function.Injective (chartB F) := fun _ _ h =>
  rhoB_injective (congrArg (toMod F) h)

theorem chart_comm (A B : SL(2, F)) : chartA F A * chartB F B = chartB F B * chartA F A :=
  toMod_injective (by rw [map_mul, map_mul, toMod_chartA, toMod_chartB]; exact rhoA_rhoB_comm A B)

variable (F) in
@[expose] def zY : Yg F := ⟨z₀ F, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem toMod_zY : toMod F (zY F) = dsign F := rfl

theorem chartA_neg_one : chartA F (-1) = zY F :=
  toMod_injective (by rw [toMod_chartA, toMod_zY]; exact rhoA_neg_one')

theorem chartB_neg_one : chartB F (-1) = zY F :=
  toMod_injective (by rw [toMod_chartB, toMod_zY]; exact rhoB_neg_one')

theorem zY_mul_self : zY F * zY F = 1 :=
  toMod_injective (by rw [map_mul, toMod_zY, map_one]; exact dsign_sq)

theorem zY_ne_one (hK : ringChar F ≠ 2) : zY F ≠ 1 := by
  intro h
  have h1 : (-1 : SL(2, F)) = 1 :=
    chartA_injective (by rw [chartA_neg_one, h, map_one])
  have h2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h2
  exact Ring.neg_one_ne_one_of_char_ne_two hK h2

theorem z₀_ne_one (hK : ringChar F ≠ 2) : z₀ F ≠ 1 := fun h =>
  zY_ne_one hK (Subtype.ext h)

theorem orderOf_z₀ (hK : ringChar F ≠ 2) : orderOf (z₀ F) = 2 :=
  orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using dsign_sq)) (z₀_ne_one hK)

theorem chart_inter (A B : SL(2, F)) (h : chartA F A = chartB F B) :
    chartA F A = 1 ∨ chartA F A = zY F := by
  have h1 : rhoA F A = rhoB F B := congrArg (toMod F) h
  have hker : (A, B⁻¹) ∈ (g2Mul hpair F).ker := by
    rw [MonoidHom.mem_ker, g2Mul_apply, map_inv, ← h1, mul_inv_cancel]
  have hc := (ker_g2Mul_central hpair _ hker).1
  rcases rootSL2_of_mem_center (τ := .G2) (g2v 1 0) hc with h2 | h2
  · left
    exact toMod_injective (by rw [toMod_chartA, map_one]; exact h2)
  · right
    exact toMod_injective (by rw [toMod_chartA, toMod_zY, ← rhoA_neg_one]; exact h2)

variable (F) in
abbrev mzero : ModGL .G2 F := rhoA F WSL * rhoB F WSL

theorem mzero_mem : mzero F ∈ adjointGroup .G2 F := mul_mem (rhoA_mem _) (rhoB_mem _)

theorem mzero_comm_dsign : mzero F * dsign F = dsign F * mzero F := by
  rw [mul_assoc, rhoB_comm_dsign, ← mul_assoc, rhoA_comm_dsign, mul_assoc]

theorem mzero_sq : mzero F * mzero F = 1 := by
  have hc : Commute (rhoB F WSL) (rhoA F WSL) := (rhoA_rhoB_comm WSL WSL).symm
  rw [hc.mul_mul_mul_comm (rhoA F WSL) (rhoB F WSL), ← map_mul, ← map_mul, WSL_mul_WSL,
    rhoA_neg_one, rhoB_neg_one, dsign_sq]

theorem mzero_eq : mzero F = rootWeylSL2 .G2 F CFSG.ComponentClassification.UnbalancedCatalog.g2a 1 *
    rootWeylSL2 .G2 F CFSG.ComponentClassification.UnbalancedCatalog.g2v 1 := by
  simp only [rootWeylSL2, nSL_one, g2a_eq, g2v_eq]

theorem mzero_conj_torus (b : Fin Tag.G2.rank → Fˣ) :
    mzero F * rootDiagUnit .G2 b * (mzero F)⁻¹ = rootDiagUnit .G2 b⁻¹ := by
  obtain ⟨hz, hw⟩ := rootWeylSL2_pair_mem_monomial (1 : Fˣ)
  rw [mzero_eq]
  exact conj_rootDiagUnit_of_smul_eq_neg hz hw b

variable (F) in
abbrev xmod (ν : Fˣ) : ModGL .G2 F := rootDiagUnit .G2 (cν ν) * mzero F

theorem xmod_mem (ν : Fˣ) : xmod F ν ∈ adjointGroup .G2 F :=
  mul_mem (rootDiagUnit_mem_adjoint _) mzero_mem

theorem xmod_comm_dsign (ν : Fˣ) : xmod F ν * dsign F = dsign F * xmod F ν := by
  have h := rootDiagUnit_mul_comm_of_mem_torusGroup (K := F) (a₀ F)
    (h := rootDiagUnit .G2 (cν ν)) (rootDiagUnit_mem_torus _)
  rw [mul_assoc, mzero_comm_dsign, ← mul_assoc, ← h, mul_assoc]

theorem xmod_sq (ν : Fˣ) : xmod F ν * xmod F ν = 1 := by
  have h1 : mzero F * rootDiagUnit .G2 (cν ν) =
      (rootDiagUnit .G2 (cν ν))⁻¹ * mzero F := by
    have := mzero_conj_torus (F := F) (cν ν)
    rw [mul_inv_eq_iff_eq_mul, ← rootDiagUnit_inv] at this
    exact this
  calc xmod F ν * xmod F ν
      = rootDiagUnit .G2 (cν ν) *
        (mzero F * rootDiagUnit .G2 (cν ν)) * mzero F := by
        simp only [mul_assoc]
    _ = mzero F * mzero F := by rw [h1]; group
    _ = 1 := mzero_sq

variable (F) in
@[expose] def xel (ν : Fˣ) : Yg F :=
  ⟨⟨xmod F ν, xmod_mem ν⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (xmod_comm_dsign ν)⟩

theorem toMod_xel (ν : Fˣ) : toMod F (xel F ν) = xmod F ν := rfl

theorem xel_sq (ν : Fˣ) : xel F ν * xel F ν = 1 :=
  toMod_injective (by rw [map_mul, toMod_xel, map_one]; exact xmod_sq ν)

theorem xmod_conj_rhoA (ν : Fˣ) (A : SL(2, F)) :
    xmod F ν * rhoA F A * (xmod F ν)⁻¹ = rhoA F (conjSLAut (gν F ν) A) := by
  have h := conj_rootSL2_decomp (K := F) isRoot_α (fun A B => g2_pair_commute hpair A B)
    (cν ν) WSL WSL A
  rw [rootChar_cν_α, conjSL_eq_conjSLAut] at h
  exact h

theorem xmod_conj_rhoB (ν : Fˣ) (B : SL(2, F)) :
    xmod F ν * rhoB F B * (xmod F ν)⁻¹ = rhoB F (conjSLAut (gν F ν) B) := by
  have h := conj_rootSL2_decomp (K := F) isRoot_β
    (fun A' B' => (g2_pair_commute hpair B' A').symm)
    (cν ν) WSL WSL B
  rw [rootChar_cν_β, conjSL_eq_conjSLAut, ← (g2_pair_commute hpair (WSL : SL(2, F)) WSL).eq] at h
  exact h

theorem xel_conj_chartA (ν : Fˣ) (A : SL(2, F)) :
    xel F ν * chartA F A * (xel F ν)⁻¹ = chartA F (conjSLAut (gν F ν) A) :=
  toMod_injective (by
    rw [map_mul, map_mul, map_inv, toMod_xel, toMod_chartA, toMod_chartA]
    exact xmod_conj_rhoA ν A)

theorem xel_conj_chartB (ν : Fˣ) (B : SL(2, F)) :
    xel F ν * chartB F B * (xel F ν)⁻¹ = chartB F (conjSLAut (gν F ν) B) :=
  toMod_injective (by
    rw [map_mul, map_mul, map_inv, toMod_xel, toMod_chartB, toMod_chartB]
    exact xmod_conj_rhoB ν B)

theorem rho_mul_rho (A₁ A₂ B₁ B₂ : SL(2, F)) :
    rhoA F A₁ * rhoB F B₁ * (rhoA F A₂ * rhoB F B₂) = rhoA F (A₁ * A₂) * rhoB F (B₁ * B₂) := by
  rw [map_mul, map_mul]
  exact (show Commute (rhoB F B₁) (rhoA F A₂) from (rhoA_rhoB_comm A₂ B₁).symm).mul_mul_mul_comm
    _ _

section FiniteOdd

variable [Finite F]

theorem g2Mul_range (hodd : Odd (Nat.card F)) :
    (g2Mul hpair F).range = rootSpan .G2 F (rootCharKernel (a₀ F)) := by
  obtain ⟨-, -, -, hp, -⟩ := odd_G2_toral_involution_fixed_p_components F hodd (a₀ F) a₀_sign
  have h := (hp ![1, 0] ![1, 2] (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))).2.2.1
  rw [h, g2Mul, MonoidHom.noncommCoprod_range, range_rootSL2_of_isRoot isRoot_α,
    range_rootSL2_of_isRoot isRoot_β]

theorem exists_decomp_Y (hodd : Odd (Nat.card F)) (y : Yg F) :
    ∃ (c : Fin Tag.G2.rank → Fˣ) (A B : SL(2, F)),
      toMod F y = rootDiagUnit .G2 c * (rhoA F A * rhoB F B) :=
  exists_decomp (ringChar_ne_two_of_odd_card hodd) a₀_sign hpair (g2Mul_range hodd)
    (toMod_mem_toralCentralizer y)

theorem gen_Y (hodd : Odd (Nat.card F)) {ν : Fˣ} (hν : ¬ IsSquare (ν : F)) :
    (chartA F).range ⊔ (chartB F).range ⊔ Subgroup.zpowers (xel F ν) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hSA : ∀ A, chartA F A ∈ (chartA F).range ⊔ (chartB F).range ⊔ Subgroup.zpowers (xel F ν) :=
    fun A => Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨A, rfl⟩)
  have hSB : ∀ B, chartB F B ∈ (chartA F).range ⊔ (chartB F).range ⊔ Subgroup.zpowers (xel F ν) :=
    fun B => Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨B, rfl⟩)
  have hSx : xel F ν ∈ (chartA F).range ⊔ (chartB F).range ⊔ Subgroup.zpowers (xel F ν) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hSab : ∀ A B, chartA F A * chartB F B ∈
      (chartA F).range ⊔ (chartB F).range ⊔ Subgroup.zpowers (xel F ν) :=
    fun A B => mul_mem (hSA A) (hSB B)
  obtain ⟨c, A, B, hdec⟩ := exists_decomp_Y hodd y
  by_cases hsq : IsSquare ((rootChar c (g2v 1 0) : Fˣ) : F)
  · obtain ⟨lam, hlam⟩ := exists_unit_sq hsq
    obtain ⟨c₁, c₂, hc⟩ := g2_pair_rootDiagUnit hpair c lam hlam
    have key : y = chartA F (HSL c₁ * A) * chartB F (HSL c₂ * B) := by
      apply toMod_injective
      rw [hdec, hc, map_mul, toMod_chartA, toMod_chartB]
      exact rho_mul_rho _ _ _ _
    rw [key]
    exact hSab _ _
  · obtain ⟨c', hc'⟩ : ∃ c', c = c' * cν ν := ⟨c * (cν ν)⁻¹, (inv_mul_cancel_right c (cν ν)).symm⟩
    obtain ⟨u, hu0, hu⟩ := exists_mul_sq_of_not_isSquare hν hsq
    have h1 : rootChar c (g2v 1 0) = rootChar c' (g2v 1 0) * ν := by
      rw [hc', rootChar_mul', rootChar_cν_α]
    have h2 : rootChar c' (g2v 1 0) = (Units.mk0 u hu0) ^ 2 := by
      apply Units.ext
      have h3 : ((rootChar c' (g2v 1 0) : Fˣ) : F) * ν = u ^ 2 * ν := by
        rw [← hu, h1, Units.val_mul]
      simpa using mul_right_cancel₀ ν.ne_zero h3
    obtain ⟨c₁, c₂, hc⟩ := g2_pair_rootDiagUnit hpair c' (Units.mk0 u hu0) h2
    have key : y = (chartA F (HSL c₁) * chartB F (HSL c₂)) * xel F ν *
        (chartA F WSL * chartB F WSL)⁻¹ * (chartA F A * chartB F B) := by
      apply toMod_injective
      simp only [map_mul, map_inv, toMod_chartA, toMod_chartB, toMod_xel]
      rw [hdec, hc', rootDiagUnit_mul, hc]
      group
    rw [key]
    exact mul_mem (mul_mem (mul_mem (hSab _ _) hSx) (inv_mem (hSab _ _))) (hSab _ _)

theorem exists_native_shape (hodd : Odd (Nat.card F)) : ∃ S : Shape (Yg F) F F, S.z = zY F := by
  have hK : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hK
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hν : ¬ IsSquare ((Units.mk0 a ha0 : Fˣ) : F) := ha
  exact ⟨Shape.ofCharts (chartA F) (chartB F) chartA_injective chartB_injective chart_comm (zY F)
    chartA_neg_one chartB_neg_one zY_mul_self (zY_ne_one hK) chart_inter (xel F (Units.mk0 a ha0))
    (xel_sq _) (gen_Y hodd hν) (gν F (Units.mk0 a ha0)) (gν F (Units.mk0 a ha0))
    (by rw [det_gν]; exact hν) (by rw [det_gν]; exact hν)
    (xel_conj_chartA _) (xel_conj_chartB _), rfl⟩

end FiniteOdd

end Certified

end Native

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
