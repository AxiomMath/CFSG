module

public import CFSG.GH74.Generic.BProg.B3.LocBalL3Abs
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Blk
public import CFSG.GH74.Generic.S3.L3Class

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps CFSG.GH74.Generic.BProg.B2 Subgroup Matrix
open scoped MatrixGroups commutatorElement

namespace LocBalL3Lin

variable {F : Type} [Field F]

theorem layer_tInv [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    LocBalL3Abs.Layer (tInv : projectiveSL 3 F) (blockSub : Subgroup (projectiveSL 3 F)) where
  mem := tInv_mem_blockSub
  quasisimple := isQuasisimple_blockSub h4
  le_centralizer := blockSub_le_centralizer
  conj_mem := fun _ hx _ hs => conj_mem_blockSub h2 hx hs
  commutator_mem := fun _ hx _ hy => commutator_mem_blockSub h2 hx hy
  center_le := by
    intro s hs hcen
    exact blockSub_center (s := ⟨s, hs⟩)
      (Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hcen g g.2)))

theorem singleInv_proj (h2 : (2 : F) ≠ 0) : S3.SingleInv (projectiveSL 3 F) :=
  S3.SingleInv.of_mulEquiv
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    (S3.singleInv_psl h2)

theorem simple_proj : IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega)
    (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup

section Gen

open FixFourS3 GenLocL3Blk

theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : F) ≠ 1 := by
  intro h
  apply h2
  linear_combination -h

@[expose] def dd (a b c : F) (h : a * b * c = 1) : SL(3, F) :=
  ⟨Matrix.diagonal ![a, b, c], by rw [Matrix.det_diagonal, Fin.prod_univ_three]; simpa using h⟩

theorem coe_dd (a b c : F) (h : a * b * c = 1) :
    ((dd a b c h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, b, c] := rfl

theorem dd_mem_Vhat (a b c : F) (h : a * b * c = 1) (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) : dd a b c h ∈ Vhat F := by
  refine ⟨?_, ?_⟩
  · rw [coe_dd]
    exact Matrix.isDiag_diagonal _
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_dd, Matrix.diagonal_mul_diagonal,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha, hb, hc]

@[expose] def s1 : SL(3, F) := dd (-1) (-1) 1 (by ring)

@[expose] def s3 : SL(3, F) := dd 1 (-1) (-1) (by ring)

theorem s1_mem : (s1 : SL(3, F)) ∈ Vhat F :=
  dd_mem_Vhat _ _ _ _ (by ring) (by ring) (by ring)

theorem s3_mem : (s3 : SL(3, F)) ∈ Vhat F :=
  dd_mem_Vhat _ _ _ _ (by ring) (by ring) (by ring)

theorem s1_ne_one (h2 : (2 : F) ≠ 0) : (s1 : SL(3, F)) ≠ 1 := by
  intro h
  have := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [s1, coe_dd] at this
  exact neg_one_ne_one h2 this

theorem s3_ne_one (h2 : (2 : F) ≠ 0) : (s3 : SL(3, F)) ≠ 1 := by
  intro h
  have := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp [s3, coe_dd] at this
  exact neg_one_ne_one h2 this

theorem s1_ne_s3 (h2 : (2 : F) ≠ 0) : (s1 : SL(3, F)) ≠ s3 := by
  intro h
  have := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [s1, s3, coe_dd] at this
  exact neg_one_ne_one h2 this

theorem range_phi_perfect [Finite F] (h4 : 4 ≤ Nat.card F) (i : Fin 2) :
    ⁅(phi (K := F) i).range, (phi (K := F) i).range⁆ = (phi (K := F) i).range := by
  have hperf : commutator SL(2, F) = ⊤ := (isQuasisimple_sl2c h4).1.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]

theorem phi_zero_comm (g : SL(2, F)) : blkHom (K := F) 0 g * s1 = s1 * blkHom (K := F) 0 g := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blkHom, s1, coe_dd]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem phi_one_comm (g : SL(2, F)) : blkHom (K := F) 1 g * s3 = s3 * blkHom (K := F) 1 g := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blkHom, s3, coe_dd]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem proj_inj_of_mem [Finite F] {s s' : SL(3, F)} (hs : s ∈ Vhat F) (hs' : s' ∈ Vhat F)
    (h : LinearFlag.proj 3 F s = LinearFlag.proj 3 F s') : s = s' :=
  congrArg Subtype.val (proj_injective_Vhat (F := F) (a₁ := ⟨s, hs⟩) (a₂ := ⟨s', hs'⟩) h)

theorem genPair_Vproj [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    LocBalL3Abs.GenPair (Vproj F) := by
  refine ⟨LinearFlag.proj 3 F s1, ⟨⟨s1, s1_mem⟩, rfl⟩, LinearFlag.proj 3 F s3, ⟨⟨s3, s3_mem⟩, rfl⟩,
    by rw [← map_mul, s1_mem.2, map_one], ?_, by rw [← map_mul, s3_mem.2, map_one], ?_, ?_,
    (phi (K := F) 0).range, (phi (K := F) 1).range, ?_, ?_, range_phi_perfect h4 0,
    range_phi_perfect h4 1, range_phi_sup⟩
  · intro h
    exact s1_ne_one h2 (proj_inj_of_mem s1_mem (Vhat F).one_mem (by rw [h, map_one]))
  · intro h
    exact s3_ne_one h2 (proj_inj_of_mem s3_mem (Vhat F).one_mem (by rw [h, map_one]))
  · intro h
    exact s1_ne_s3 h2 (proj_inj_of_mem s1_mem s3_mem h)
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show LinearFlag.proj 3 F (blkHom 0 g) * LinearFlag.proj 3 F s1 =
      LinearFlag.proj 3 F s1 * LinearFlag.proj 3 F (blkHom 0 g)
    rw [← map_mul, ← map_mul, phi_zero_comm]
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show LinearFlag.proj 3 F (blkHom 1 g) * LinearFlag.proj 3 F s3 =
      LinearFlag.proj 3 F s3 * LinearFlag.proj 3 F (blkHom 1 g)
    rw [← map_mul, ← map_mul, phi_one_comm]

end Gen

theorem modelData_projectiveSL [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    LocBalL3Abs.ModelData (projectiveSL 3 F) :=
  ⟨simple_proj, ⟨tInv, blockSub, tInv_mul_self, tInv_ne_one h2, layer_tInv h2 h4⟩,
    singleInv_proj h2,
    FixFourS3.Vproj F,
    (B2.WeakSigGen.forall_of_isElementaryAbelian FixFourS3.isElementaryAbelian_Vproj).2,
    FixFourS3.card_Vproj h2, genPair_Vproj h2 h4⟩

end LocBalL3Lin

end CFSG.GH74.Generic.BProg.B3
