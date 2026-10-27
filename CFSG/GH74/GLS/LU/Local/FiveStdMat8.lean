module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat7
public import CFSG.GH74.GLS.LU.Local.FiveStdSetting

public section

open Subgroup CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.FiveStd.Mat CFSG.GH74.L5U5
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

section KK

variable {F : Type} [Field F] [CharP F 5] [Finite F]

theorem exists_sq_inv : ∀ d : Fin 5, d * d = 1 → ∃ c : Fin 5, c ≠ 0 ∧ c * c * d = 1 := by decide

omit [CharP F 5] [Finite F] in
theorem blkLR_mat (a b : GL (Fin 2) F) :
    ((blkL F a * blkR F b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blk4 (a : Matrix (Fin 2) (Fin 2) F) (b : Matrix (Fin 2) (Fin 2) F) := by
  rw [blkL_apply, blkR_apply, diagGL_mul, coe_diagGL, mul_one, one_mul]

omit [Finite F] in
theorem ιF_mem_KK {x : E} (hx : validE x = true) (hk : inKK x = true) :
    ιF F x ∈ ((K1 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) *
      ((K2 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) := by
  unfold inKK at hk
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hk
  obtain ⟨hs, hd⟩ := hk
  have hv := ((validE_iff x).1 hx).2
  obtain ⟨c, hc, hcd⟩ := exists_sq_inv (detA x) (by rw [← hd] at hv; exact hv)
  have hA1 : detA (scaleE c x) = 1 := by rw [detA_scaleE]; exact hcd
  have hB1 : detB (scaleE c x) = 1 := by rw [detB_scaleE, ← hd]; exact hcd
  have hAr : detA (scaleE c x) ≠ 0 := by rw [hA1]; decide
  have hPr : detA (scaleE c x) * detB (scaleE c x) = 1 := by rw [hA1, hB1]; decide
  set r := scaleE c x with hr
  have hrs : r.s = false := hs
  have hdA : det4 (r.a0, r.a1, r.a2, r.a3) = 1 := hA1
  have hdB : det4 (r.b0, r.b1, r.b2, r.b3) = 1 := hB1
  have hg : blkL F (slGL (r.a0, r.a1, r.a2, r.a3) hdA) * blkR F (slGL (r.b0, r.b1, r.b2, r.b3) hdB) ∈
      (ModelData.lin F).K4 :=
    Subgroup.mul_mem _ ((ModelData.lin F).blkL_mem_K4 (slGL_mem_H2 _ hdA))
      ((ModelData.lin F).blkR_mem_K4 (slGL_mem_H2 _ hdB))
  have hgm : ((blkL F (slGL (r.a0, r.a1, r.a2, r.a3) hdA) * blkR F (slGL (r.b0, r.b1, r.b2, r.b3) hdB) :
      GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = mat4 r := by
    rw [blkLR_mat, coe_slGL, coe_slGL]
    simp [mat4, hrs, blkA, blkB]
  have h1 := ιF_normE_eq hAr hPr hg hgm
  have h2 : normE r = x := normE_scaleE (((validE_iff x).1 hx).1) hc
  rw [h2] at h1
  rw [h1]
  have e : mkP (ModelData.lin F) ⟨_, hg⟩ =
      iota1 (ModelData.lin F) ⟨slGL (r.a0, r.a1, r.a2, r.a3) hdA, slGL_mem_H2 _ hdA⟩ *
        iota2 (ModelData.lin F) ⟨slGL (r.b0, r.b1, r.b2, r.b3) hdB, slGL_mem_H2 _ hdB⟩ :=
    map_mul (mkP (ModelData.lin F)) ⟨blkL F (slGL (r.a0, r.a1, r.a2, r.a3) hdA),
      (ModelData.lin F).blkL_mem_K4 (slGL_mem_H2 _ hdA)⟩ ⟨blkR F (slGL (r.b0, r.b1, r.b2, r.b3) hdB),
      (ModelData.lin F).blkR_mem_K4 (slGL_mem_H2 _ hdB)⟩
  rw [e]
  exact Set.mul_mem_mul (MonoidHom.mem_range.2 ⟨_, rfl⟩) (MonoidHom.mem_range.2 ⟨_, rfl⟩)

theorem inKK_of_mem_KK (hF : Nat.card F = 5) {x : E} (hx : validE x = true)
    (h : ιF F x ∈ ((K1 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) *
      ((K2 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F)))) :
    inKK x = true := by
  obtain ⟨g1, hg1, g2, hg2, hg⟩ := Set.mem_mul.1 h
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hg1
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hg2
  obtain ⟨A, hA, hAeq⟩ := exists_slBlock hF (a : GL (Fin 2) F) (((ModelData.lin F).mem_H2 _).1 a.2).2
  obtain ⟨B, hB, hBeq⟩ := exists_slBlock hF (b : GL (Fin 2) F) (((ModelData.lin F).mem_H2 _).1 b.2).2
  have hdA : det4 A = 1 := mem_slBlocks.1 hA
  have hdB : det4 B = 1 := mem_slBlocks.1 hB
  set z : E := ⟨A.1, A.2.1, A.2.2.1, A.2.2.2, B.1, B.2.1, B.2.2.1, B.2.2.2, false⟩ with hz
  have hzA : detA z = 1 := hdA
  have hzB : detB z = 1 := hdB
  have hAz : detA z ≠ 0 := by rw [hzA]; decide
  have hPz : detA z * detB z = 1 := by rw [hzA, hzB]; decide
  have hg' : blkL F (a : GL (Fin 2) F) * blkR F (b : GL (Fin 2) F) ∈ (ModelData.lin F).K4 :=
    Subgroup.mul_mem _ ((ModelData.lin F).blkL_mem_K4 a.2) ((ModelData.lin F).blkR_mem_K4 b.2)
  have hgm : ((blkL F (a : GL (Fin 2) F) * blkR F (b : GL (Fin 2) F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = mat4 z := by
    rw [blkLR_mat, hAeq, hBeq]
    simp [mat4, hz, blkA, blkB]
  have h1 := ιF_normE_eq hAz hPz hg' hgm
  have e : iota1 (ModelData.lin F) a * iota2 (ModelData.lin F) b =
      mkP (ModelData.lin F) ⟨_, hg'⟩ :=
    (map_mul (mkP (ModelData.lin F)) ⟨blkL F (a : GL (Fin 2) F), (ModelData.lin F).blkL_mem_K4 a.2⟩
      ⟨blkR F (b : GL (Fin 2) F), (ModelData.lin F).blkR_mem_K4 b.2⟩).symm
  have hxe : x = normE z :=
    ιF_inj hx (validE_normE hAz hPz) (hg.symm.trans (e.trans h1.symm))
  rw [hxe, normE_eq_scaleE]
  unfold inKK
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simp [scaleE, hz]
  · rw [beq_iff_eq, detA_scaleE, detB_scaleE, hzA, hzB]

@[expose] noncomputable def fiveStdSetting (hF : Nat.card F = 5) : FiveStdSetting (PG (ModelData.lin F)) where
  ι := ιF F
  model := model_ιF
  K₁ := K1 (ModelData.lin F)
  K₂ := K2 (ModelData.lin F)
  hK₁ := (S_K1l hF).symm
  hK₂ := (S_K2l hF).symm
  hC := by
    rw [ιF_zE]
    exact S_Cs hF
  hcomm := fun _ hx _ hy => K1_K2_comm _ hx hy
  hKK := fun _ hx => ⟨fun h => ιF_mem_KK hx h, fun h => inKK_of_mem_KK hF hx h⟩
  hblock := fun x hx hs => ιF_block ((mem_Cs_iff x).1 hx) hs

end KK

end CFSG.GH74.GLS.LU.Local.Five
