module

public import CFSG.GH74.Generic.Front.SpAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSp4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_scalar_of_comm_transvections {P : Matrix (Fin 2) (Fin 2) F}
    (hu : P * !![1, 1; 0, 1] = !![1, 1; 0, 1] * P) (hl : P * !![1, 0; 1, 1] = !![1, 0; 1, 1] * P) :
    P = Matrix.scalar (Fin 2) (P 0 0) := by
  have u00 := congrFun (congrFun hu 0) 0
  have u01 := congrFun (congrFun hu 0) 1
  have l00 := congrFun (congrFun hl 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at u00 u01 l00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u00, l00]
  linear_combination -u01

theorem trace_blk (g h : Matrix (Fin 2) (Fin 2) F) :
    (blk g h).trace = g 0 0 + h 0 0 + g 1 1 + h 1 1 := by
  simp [blk, diag2, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem trace_blk_map (σ : F ≃+* F) (g h : Matrix (Fin 2) (Fin 2) F) :
    ((blk g h).map σ).trace = σ (g 0 0) + σ (h 0 0) + σ (g 1 1) + σ (h 1 1) := by
  simp [blk, diag2, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem blk_scalar (c : F) : blk (Matrix.scalar (Fin 2) c) (Matrix.scalar (Fin 2) c) =
    c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [blk, diag2]

theorem sp4_aut_fix [Finite F] (hodd : Odd (Nat.card F)) (α : MulAut ↥(StatedSp 2 F))
    (hfix : ∀ g h : SL(2, F), (g = 1 ∨ h = 1) → α (blkSL F (g, h)) = blkSL F (g, h)) :
    α = 1 ∨ α = MulAut.conj (T1 F) := by
  have h2 : (2 : F) ≠ 0 := GH74.L5U5.two_ne_zero_of_odd_card hodd
  obtain ⟨A, σ, rfl⟩ := GH74.Generic.aut_statedSp2 hodd α
  set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hB
  set Bi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hBi
  have hBBi : B * Bi = 1 := by rw [hB, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : Bi * B = 1 := by rw [hB, hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmat : ∀ g h : SL(2, F), (g = 1 ∨ h = 1) →
      B * (blk (g : Matrix (Fin 2) (Fin 2) F) h).map σ * Bi =
        blk (g : Matrix (Fin 2) (Fin 2) F) h := by
    intro g h hgh
    have := congrArg (fun k : ↥(StatedSp 2 F) => ((k : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (hfix g h hgh)
    simp only [GH74.Generic.coe_tau, coe_blkSL] at this
    exact this
  have hσ : ∀ c : F, σ c = c := by
    intro c
    have ht := congrArg Matrix.trace (hmat (GH74.Generic.companionSL c) 1 (Or.inr rfl))
    rw [Matrix.trace_mul_cycle, hBiB, one_mul, trace_blk_map, trace_blk] at ht
    simpa [GH74.Generic.companionSL] using ht
  have hσ1 : σ = RingEquiv.refl F := RingEquiv.ext hσ
  subst hσ1
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, M.map (RingEquiv.refl F) = M :=
    fun M => by ext; simp
  have hcomm : ∀ g h : SL(2, F), (g = 1 ∨ h = 1) →
      B * blk (g : Matrix (Fin 2) (Fin 2) F) h = blk (g : Matrix (Fin 2) (Fin 2) F) h * B := by
    intro g h hgh
    have := hmat g h hgh
    rw [hmap] at this
    calc B * blk (g : Matrix (Fin 2) (Fin 2) F) h =
        B * blk (g : Matrix (Fin 2) (Fin 2) F) h * Bi * B := by
          rw [mul_assoc _ Bi, hBiB, mul_one]
      _ = blk (g : Matrix (Fin 2) (Fin 2) F) h * B := by rw [this]
  obtain ⟨P, Q, hPQ⟩ := exists_blk_of_commute h2 (A := B) (by
    have := hcomm 1 negOneSL (Or.inl rfl)
    rwa [Matrix.SpecialLinearGroup.coe_one, coe_negOneSL] at this)
  let u : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hP : ∀ s : SL(2, F), P * s = s * P := fun s => by
    have := hcomm s 1 (Or.inr rfl)
    rw [hPQ, Matrix.SpecialLinearGroup.coe_one, blk_mul, blk_mul] at this
    exact (blk_injective _ _ _ _ this).1
  have hQ : ∀ s : SL(2, F), Q * s = s * Q := fun s => by
    have := hcomm 1 s (Or.inl rfl)
    rw [hPQ, Matrix.SpecialLinearGroup.coe_one, blk_mul, blk_mul] at this
    exact (blk_injective _ _ _ _ this).2
  obtain ⟨c, rfl⟩ : ∃ c, P = Matrix.scalar (Fin 2) c :=
    ⟨_, eq_scalar_of_comm_transvections (hP u) (hP l)⟩
  obtain ⟨d, rfl⟩ : ∃ d, Q = Matrix.scalar (Fin 2) d :=
    ⟨_, eq_scalar_of_comm_transvections (hQ u) (hQ l)⟩
  obtain ⟨ν, hν⟩ := mem_gsp.mp A.2
  rw [← hB, hPQ, formJ_eq_blk, blk_transpose, blk_mul, blk_mul, J₁, transpose_mul_J₁_mul,
    transpose_mul_J₁_mul] at hν
  have e1 := congrFun (congrFun hν (Sum.inl 0)) (Sum.inr 0)
  have e2 := congrFun (congrFun hν (Sum.inl 1)) (Sum.inr 1)
  simp [blk, diag2] at e1 e2
  have hsq : (c - d) * (c + d) = 0 := by linear_combination e1 - e2
  have hα : ∀ k : ↥(StatedSp 2 F), ((((conjSp 2 F A * fieldSp 2 F (RingEquiv.refl F)) k :
      ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      B * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * Bi :=
    fun k => by rw [GH74.Generic.coe_tau, hmap]
  have hscal : ∀ (c : F) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * M = M * (c • 1) := fun c M => by
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  rcases mul_eq_zero.mp hsq with h | h
  · left
    have hB1 : B = c • 1 := by
      rw [hPQ, show d = c by linear_combination -h, blk_scalar]
    refine MulEquiv.ext fun k => sp_ext ?_
    rw [hα, MulAut.one_apply, hB1, hscal, mul_assoc, ← hB1, hBBi, mul_one]
  · right
    set T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := blk 1 (-1) with hT
    have hTT : T * T = 1 := by rw [hT, blk_mul]; simp [blk_one_one]
    have hTB : T * B = c • 1 := by
      rw [hT, hPQ, blk_mul, show d = -c by linear_combination h, ← blk_scalar]
      congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp
    have hBT : B = T * (c • 1) := by rw [← hTB, ← mul_assoc, hTT, one_mul]
    have hT1 : (T1 F)⁻¹ = T1 F := inv_eq_of_mul_eq_one_right (sp_ext (by
      rw [Subgroup.coe_mul, Units.val_mul, coe_T1, ← hT, hTT]; rfl))
    refine MulEquiv.ext fun k => sp_ext ?_
    rw [hα, MulAut.conj_apply, hT1, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
      Units.val_mul, coe_T1, ← hT]
    calc B * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * Bi =
        T * (c • 1 * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
          * Bi := by rw [hBT, mul_assoc T]
      _ = T * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * T *
          (B * Bi) := by rw [hscal, ← hTB]; simp only [mul_assoc]
      _ = T * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * T := by
          rw [hBBi, mul_one]

theorem sp4FrameOuterQ8Free_holds :
    ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
      FrameOuterQ8Free ↥(Assembly.LowTwoRank.StatedSp 2 F) (TwinFr.sp4J₂ F) (TwinFr.sp4J₄ F) := by
  intro F _ _ hodd ψ hψ h₂ h₄
  exfalso
  have hc : ∀ q, ψ q = 1 ∨ ψ q = MulAut.conj (T1 F) := fun q => sp4_aut_fix hodd (ψ q) (by
    rintro g h (rfl | rfl)
    · exact h₂ q _ ⟨h, rfl⟩
    · exact h₄ q _ ⟨g, rfl⟩)
  have hne : ∀ q : QuaternionGroup 2, q ≠ 1 → ψ q ≠ 1 := fun q hq h =>
    hq (hψ (h.trans (map_one ψ).symm))
  rcases hc (QuaternionGroup.a 1) with h1 | h1
  · exact hne _ (by decide) h1
  rcases hc (QuaternionGroup.a 2) with h2 | h2
  · exact hne _ (by decide) h2
  exact absurd (hψ (h1.trans h2.symm)) (by decide)

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
