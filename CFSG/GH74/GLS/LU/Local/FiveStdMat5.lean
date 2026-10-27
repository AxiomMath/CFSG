module

public import CFSG.GH74.GLS.LU.Local.FiveStdDict3
public import CFSG.GH74.GLS.Stage2.Final.ModelLayer
public import CFSG.GH74.GLS.LU.Local.FiveStdMat3

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock Matrix

variable {F : Type} [Field F] [CharP F 5]

theorem ιF_normE_eq {z : E} (hA : detA z ≠ 0) (hP : detA z * detB z = 1) {g : GL (Fin 4) F}
    (hg : g ∈ (ModelData.lin F).K4) (hgm : (g : Matrix (Fin 4) (Fin 4) F) = mat4 z) :
    ιF F (normE z) = mkP (ModelData.lin F) ⟨g, hg⟩ := by
  have hv := validE_normE hA hP
  rw [ιF_eq hv, mkP_eq_iff]
  have hc : cF F (cn z) ≠ 0 := cF_ne_zero_unit (cn_ne_zero hA)
  have h1 : glE (normE z) = Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 _ hc) * g := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glE hv, hgm, scalar_mul_mat, mat4_normE]
    rfl
  refine ⟨(Units.mk0 _ hc)⁻¹, ?_⟩
  show (glE (normE z))⁻¹ * g = _
  rw [h1]
  exact inv_scalar_mul_cancel _ _

theorem exists_mkM [Finite F] (hF : Nat.card F = 5) (P : Matrix (Fin 2) (Fin 2) F) :
    ∃ p0 p1 p2 p3 : Fin 5, P = mkM p0 p1 p2 p3 := by
  obtain ⟨p0, h0⟩ := cF_surjective hF (P 0 0)
  obtain ⟨p1, h1⟩ := cF_surjective hF (P 0 1)
  obtain ⟨p2, h2⟩ := cF_surjective hF (P 1 0)
  obtain ⟨p3, h3⟩ := cF_surjective hF (P 1 1)
  refine ⟨p0, p1, p2, p3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkM, h0, h1, h2, h3]

theorem det_mkM (p0 p1 p2 p3 : Fin 5) :
    (mkM p0 p1 p2 p3 : Matrix (Fin 2) (Fin 2) F).det = cF F (p0 * p3 - p1 * p2) := by
  rw [mkM, Matrix.det_fin_two_of, cF_sub, cF_mul, cF_mul]

theorem exists_slBlock [Finite F] (hF : Nat.card F = 5) (a : Matrix (Fin 2) (Fin 2) F) (ha : a.det = 1) :
    ∃ A ∈ slBlocks, a = mkM A.1 A.2.1 A.2.2.1 A.2.2.2 := by
  obtain ⟨p0, p1, p2, p3, hp⟩ := exists_mkM hF a
  refine ⟨(p0, p1, p2, p3), ?_, hp⟩
  have hd : p0 * p3 - p1 * p2 = 1 := by
    apply cF_injective (F := F)
    rw [← det_mkM, ← hp, ha, cF_one]
  simp only [slBlocks, List.mem_filter, decide_eq_true_eq]
  exact ⟨mem_allBlocks _, hd⟩

theorem det4_eq {A : Fin 5 × Fin 5 × Fin 5 × Fin 5} (h : det4 A = 1) :
    A.1 * A.2.2.2 - A.2.1 * A.2.2.1 = 1 := h

@[expose] noncomputable def slGL (A : Fin 5 × Fin 5 × Fin 5 × Fin 5) (h : det4 A = 1) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mkM A.1 A.2.1 A.2.2.1 A.2.2.2) (by
    rw [det_mkM, det4_eq h, cF_one]
    exact one_ne_zero)

theorem coe_slGL (A : Fin 5 × Fin 5 × Fin 5 × Fin 5) (h : det4 A = 1) :
    ((slGL A h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = mkM A.1 A.2.1 A.2.2.1 A.2.2.2 := by
  simp [slGL]

theorem slGL_mem_H2 (A : Fin 5 × Fin 5 × Fin 5 × Fin 5) (h : det4 A = 1) :
    (slGL A h : GL (Fin 2) F) ∈ (ModelData.lin F).H2 :=
  ((ModelData.lin F).mem_H2 _).2 ⟨Subgroup.mem_top _, by rw [coe_slGL, det_mkM, det4_eq h, cF_one]⟩

theorem mem_slBlocks {A : Fin 5 × Fin 5 × Fin 5 × Fin 5} : A ∈ slBlocks ↔ det4 A = 1 := by
  simp only [slBlocks, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allBlocks _, h⟩⟩

theorem K1_rec_valid {A : Fin 5 × Fin 5 × Fin 5 × Fin 5} (h : det4 A = 1) :
    detA (⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩ : E) ≠ 0 ∧
      detA (⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩ : E) *
        detB (⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩ : E) = 1 := by
  have h1 : detA (⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩ : E) = 1 := h
  have h2 : detB (⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩ : E) = 1 :=
    (by decide : (1 : Fin 5) * 1 - 0 * 0 = 1)
  rw [h1, h2]
  exact ⟨by decide, by decide⟩

theorem K2_rec_valid {A : Fin 5 × Fin 5 × Fin 5 × Fin 5} (h : det4 A = 1) :
    detA (⟨1, 0, 0, 1, A.1, A.2.1, A.2.2.1, A.2.2.2, false⟩ : E) ≠ 0 ∧
      detA (⟨1, 0, 0, 1, A.1, A.2.1, A.2.2.1, A.2.2.2, false⟩ : E) *
        detB (⟨1, 0, 0, 1, A.1, A.2.1, A.2.2.1, A.2.2.2, false⟩ : E) = 1 := by
  have h1 : detA (⟨1, 0, 0, 1, A.1, A.2.1, A.2.2.1, A.2.2.2, false⟩ : E) = 1 :=
    (by decide : (1 : Fin 5) * 1 - 0 * 0 = 1)
  have h2 : detB (⟨1, 0, 0, 1, A.1, A.2.1, A.2.2.1, A.2.2.2, false⟩ : E) = 1 := h
  rw [h1, h2]
  exact ⟨by decide, by decide⟩

theorem ιF_K1_rec {A : Fin 5 × Fin 5 × Fin 5 × Fin 5} (h : det4 A = 1) :
    ιF F (normE ⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩) =
      iota1 (ModelData.lin F) ⟨slGL A h, slGL_mem_H2 A h⟩ := by
  obtain ⟨h1, h2⟩ := K1_rec_valid h
  rw [ιF_normE_eq h1 h2 ((ModelData.lin F).blkL_mem_K4 (slGL_mem_H2 A h))]
  · rfl
  · rw [blkL_apply, coe_diagGL, coe_slGL, Units.val_one]
    simp [mat4, blkA, blkB, mkM_one]

theorem ιF_K2_rec {A : Fin 5 × Fin 5 × Fin 5 × Fin 5} (h : det4 A = 1) :
    ιF F (normE ⟨1, 0, 0, 1, A.1, A.2.1, A.2.2.1, A.2.2.2, false⟩) =
      iota2 (ModelData.lin F) ⟨slGL A h, slGL_mem_H2 A h⟩ := by
  obtain ⟨h1, h2⟩ := K2_rec_valid h
  rw [ιF_normE_eq h1 h2 ((ModelData.lin F).blkR_mem_K4 (slGL_mem_H2 A h))]
  · rfl
  · rw [blkR_apply, coe_diagGL, coe_slGL, Units.val_one]
    simp [mat4, blkA, blkB, mkM_one]

theorem S_K1l [Finite F] (hF : Nat.card F = 5) :
    S (ιF F) K1l = ((K1 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) :
      Set (PG (ModelData.lin F))) := by
  ext g
  rw [mem_S]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [K1l, List.mem_map] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [ιF_K1_rec (mem_slBlocks.1 hA)]
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨A, hA, hAeq⟩ := exists_slBlock hF (a : GL (Fin 2) F)
      (((ModelData.lin F).mem_H2 _).1 a.2).2
    have hea : (⟨slGL A (mem_slBlocks.1 hA), slGL_mem_H2 _ _⟩ : ↥(ModelData.lin F).H2) = a :=
      Subtype.ext (Units.ext (by rw [coe_slGL]; exact hAeq.symm))
    refine ⟨_, ?_, (ιF_K1_rec (mem_slBlocks.1 hA)).trans (by rw [hea])⟩
    simp only [K1l, List.mem_map]
    exact ⟨A, hA, rfl⟩

theorem S_K2l [Finite F] (hF : Nat.card F = 5) :
    S (ιF F) K2l = ((K2 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) :
      Set (PG (ModelData.lin F))) := by
  ext g
  rw [mem_S]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [K2l, List.mem_map] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [ιF_K2_rec (mem_slBlocks.1 hA)]
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨A, hA, hAeq⟩ := exists_slBlock hF (a : GL (Fin 2) F)
      (((ModelData.lin F).mem_H2 _).1 a.2).2
    have hea : (⟨slGL A (mem_slBlocks.1 hA), slGL_mem_H2 _ _⟩ : ↥(ModelData.lin F).H2) = a :=
      Subtype.ext (Units.ext (by rw [coe_slGL]; exact hAeq.symm))
    refine ⟨_, ?_, (ιF_K2_rec (mem_slBlocks.1 hA)).trans (by rw [hea])⟩
    simp only [K2l, List.mem_map]
    exact ⟨A, hA, rfl⟩

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
