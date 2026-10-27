module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12SpMono
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.Open
open scoped MatrixGroups

section Diag

variable {K : Type} [Field K]

@[expose] def dMat (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (g 0 0 • (1 : Matrix (Fin 2) (Fin 2) K)) (g 0 1 • 1) (g 1 0 • 1) (g 1 1 • 1)

theorem dMat_mul (g h : Matrix (Fin 2) (Fin 2) K) : dMat (g * h) = dMat g * dMat h := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

theorem dMat_one : dMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [dMat]

theorem dMat_symp (g : Matrix (Fin 2) (Fin 2) K) (hg : g.det = 1) :
    (dMat g)ᵀ * Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 * dMat g =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 := by
  rw [Matrix.det_fin_two] at hg
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    first | ring1 | linear_combination hg | linear_combination (-1 : K) * hg

@[expose] def dKron : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun := dMat
  map_one' := dMat_one
  map_mul' := dMat_mul

@[expose] def dGL : SL(2, K) →* GL (Fin 2 ⊕ Fin 2) K :=
  (Units.map dKron).comp Matrix.SpecialLinearGroup.toGL

theorem coe_dGL (g : SL(2, K)) :
    ((dGL g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      dMat (g : Matrix (Fin 2) (Fin 2) K) := rfl

theorem dGL_mem (g : SL(2, K)) : dGL g ∈ StatedSp 2 K :=
  Subgroup.subset_closure (by
    show ((dGL g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 * _ = _
    rw [coe_dGL]
    exact dMat_symp _ g.2)

@[expose] def dSp : SL(2, K) →* StatedSp 2 K := dGL.codRestrict (StatedSp 2 K) dGL_mem

@[expose] def dP : SL(2, K) →* StatedProj (StatedSp 2 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))).comp dSp

theorem dGL_mem_scalars {g : SL(2, K)}
    (h : (dGL g : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K) :
    g ∈ Subgroup.center SL(2, K) := by
  obtain ⟨c, hc⟩ := h
  have hc' : ((Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = dMat (g : Matrix (Fin 2) (Fin 2) K) := by
    rw [hc]
    rfl
  have h00 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inl 0)
  have h01 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inr 0)
  have h10 := congrFun (congrFun hc' (Sum.inr 0)) (Sum.inl 0)
  have h11 := congrFun (congrFun hc' (Sum.inr 0)) (Sum.inr 0)
  simp [dMat, Matrix.scalar_apply] at h00 h01 h10 h11
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨c, ?_, ?_⟩
  · have hdet := g.2
    rw [Matrix.det_fin_two, ← h00, ← h01, ← h10, ← h11] at hdet
    simpa [Fintype.card_fin, pow_two] using (by linear_combination hdet : (c : K) ^ 2 = 1)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← h00, ← h01, ← h10, ← h11]

end Diag

section FourGroup

variable {K : Type} [Field K]

@[expose] def spaS : StatedSp 2 K := ⟨monoGLS 0 spEa spEa_pm, monoGLS_a_mem⟩

@[expose] def spsS : StatedSp 2 K := ⟨monoGLS 1 spEs spEs_pm, monoGLS_s_mem⟩

theorem coe_spaS : (((spaS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = monoS (kpermS 0) spEa := rfl

theorem coe_spsS : (((spsS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = monoS (kpermS 1) spEs := rfl

theorem spaS_mul_self : (spaS : StatedSp 2 K) * spaS = 1 := by
  apply Subtype.ext
  apply Units.ext
  show monoS (kpermS 0) spEa * monoS (kpermS 0) spEa = 1
  rw [monoS_mul, kpermS_sq, ← monoS_one_eq]
  congr 1
  funext k
  exact pm_mul_self (spEa_pm k)

theorem spsS_mul_self : (spsS : StatedSp 2 K) * spsS = 1 := by
  apply Subtype.ext
  apply Units.ext
  show monoS (kpermS 1) spEs * monoS (kpermS 1) spEs = 1
  rw [monoS_mul, kpermS_sq, ← monoS_one_eq]
  congr 1
  funext k
  exact pm_mul_self (spEs_pm k)

theorem spaS_inv : (spaS : StatedSp 2 K)⁻¹ = spaS := inv_eq_of_mul_eq_one_right spaS_mul_self

theorem spsS_inv : (spsS : StatedSp 2 K)⁻¹ = spsS := inv_eq_of_mul_eq_one_right spsS_mul_self

theorem mk_eq_one_iff_statedSp {g : StatedSp 2 K} :
    (QuotientGroup.mk g : StatedProj (StatedSp 2 K)) = 1 ↔
      (g : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk_eq_mk_iff_statedSp {g h : StatedSp 2 K} :
    (QuotientGroup.mk g : StatedProj (StatedSp 2 K)) = QuotientGroup.mk h ↔
      ((g⁻¹ * h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]

theorem scalar_entry {M : GL (Fin 2 ⊕ Fin 2) K}
    (h : M ∈ StatedScalars (Fin 2 ⊕ Fin 2) K) :
    ∃ c : K, (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Matrix.scalar (Fin 2 ⊕ Fin 2) c := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← hc]; rfl⟩

theorem spaS_notMem_scalars (h2 : (2 : K) ≠ 0) :
    ((spaS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∉ StatedScalars (Fin 2 ⊕ Fin 2) K := by
  intro h
  obtain ⟨c, hc⟩ := scalar_entry h
  have h1 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 0)
  have h2' := congrFun (congrFun hc (Sum.inl 1)) (Sum.inl 1)
  simp [coe_spaS, Matrix.scalar_apply, monoS, kpermS, spEa] at h1 h2'
  apply h2
  linear_combination h1 - h2'

theorem spsS_notMem_scalars :
    ((spsS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∉ StatedScalars (Fin 2 ⊕ Fin 2) K := by
  intro h
  obtain ⟨c, hc⟩ := scalar_entry h
  have h1 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 1)
  simp [coe_spsS, Matrix.scalar_apply, monoS, kpermS, spEs, Equiv.swap_apply_def] at h1

theorem spaS_mul_spsS_notMem_scalars :
    (((spaS : StatedSp 2 K)⁻¹ * spsS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∉
      StatedScalars (Fin 2 ⊕ Fin 2) K := by
  intro h
  obtain ⟨c, hc⟩ := scalar_entry h
  rw [spaS_inv] at hc
  have h1 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 1)
  simp [Subgroup.coe_mul, Units.val_mul, coe_spaS, coe_spsS, Matrix.scalar_apply, Matrix.mul_apply,
    monoS, kpermS, spEa, spEs, Equiv.swap_apply_def] at h1

theorem dMat_mul_monoS_a (G : Matrix (Fin 2) (Fin 2) K) :
    dMat G * monoS (kpermS 0) spEa = monoS (kpermS 0) spEa * dMat G := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [dMat, monoS, kpermS, spEa, Matrix.mul_apply, Fintype.sum_sum_type]

theorem dMat_mul_monoS_s (G : Matrix (Fin 2) (Fin 2) K) :
    dMat G * monoS (kpermS 1) spEs = monoS (kpermS 1) spEs * dMat G := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [dMat, monoS, kpermS, spEs, Matrix.mul_apply, Fintype.sum_sum_type,
      Equiv.swap_apply_def]

theorem dGL_mul_spaS (g : SL(2, K)) :
    dGL g * ((spaS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      ((spaS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * dGL g := by
  apply Units.ext
  simp only [Units.val_mul, coe_dGL, coe_spaS]
  exact dMat_mul_monoS_a _

theorem dGL_mul_spsS (g : SL(2, K)) :
    dGL g * ((spsS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      ((spsS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * dGL g := by
  apply Units.ext
  simp only [Units.val_mul, coe_dGL, coe_spsS]
  exact dMat_mul_monoS_s _

theorem spsS_spaS_sq_mem_scalars :
    (((spsS * spaS) * (spsS * spaS) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈
      StatedScalars (Fin 2 ⊕ Fin 2) K := by
  refine ⟨-1, Units.ext ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, coe_spaS, coe_spsS,
    Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [monoS, kpermS, spEs, spEa, Matrix.mul_apply, Fintype.sum_sum_type,
      Equiv.swap_apply_def, Matrix.scalar_apply]

end FourGroup

section Quotient

variable {K : Type} [Field K]

theorem xa_sq :
    (QuotientGroup.mk spaS : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spaS = 1 := by
  rw [← QuotientGroup.mk_mul, spaS_mul_self]
  rfl

theorem xs_sq :
    (QuotientGroup.mk spsS : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spsS = 1 := by
  rw [← QuotientGroup.mk_mul, spsS_mul_self]
  rfl

theorem xa_ne_one (h2 : (2 : K) ≠ 0) :
    (QuotientGroup.mk spaS : StatedProj (StatedSp 2 K)) ≠ 1 := fun h =>
  spaS_notMem_scalars h2 (mk_eq_one_iff_statedSp.1 h)

theorem xs_ne_one : (QuotientGroup.mk spsS : StatedProj (StatedSp 2 K)) ≠ 1 := fun h =>
  spsS_notMem_scalars (mk_eq_one_iff_statedSp.1 h)

theorem xs_ne_xa :
    (QuotientGroup.mk spsS : StatedProj (StatedSp 2 K)) ≠ QuotientGroup.mk spaS := fun h =>
  spaS_mul_spsS_notMem_scalars (mk_eq_mk_iff_statedSp.1 h.symm)

theorem xa_xs_comm :
    (QuotientGroup.mk spaS : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spsS =
      QuotientGroup.mk spsS * QuotientGroup.mk spaS := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  apply mk_eq_mk_iff_statedSp.2
  have : (spaS * spsS : StatedSp 2 K)⁻¹ * (spsS * spaS) = (spsS * spaS) * (spsS * spaS) := by
    rw [_root_.mul_inv_rev, spaS_inv, spsS_inv]
  rw [this]
  exact spsS_spaS_sq_mem_scalars

theorem dP_eq_one {g : SL(2, K)} (h : (dP g : StatedProj (StatedSp 2 K)) = 1) :
    g ∈ Subgroup.center SL(2, K) :=
  dGL_mem_scalars (mk_eq_one_iff_statedSp.1 h)

theorem dP_mul_xa (g : SL(2, K)) :
    (dP g : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spaS =
      QuotientGroup.mk spaS * dP g := by
  show (QuotientGroup.mk (dSp g) : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spaS =
    QuotientGroup.mk spaS * QuotientGroup.mk (dSp g)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext (dGL_mul_spaS g))

theorem dP_mul_xs (g : SL(2, K)) :
    (dP g : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spsS =
      QuotientGroup.mk spsS * dP g := by
  show (QuotientGroup.mk (dSp g) : StatedProj (StatedSp 2 K)) * QuotientGroup.mk spsS =
    QuotientGroup.mk spsS * QuotientGroup.mk (dSp g)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext (dGL_mul_spsS g))

end Quotient

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
