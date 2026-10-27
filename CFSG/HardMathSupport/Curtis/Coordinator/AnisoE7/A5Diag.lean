module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Torus
public import CFSG.RankThree.PartOne.KA5L.Torus

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Diag

variable {L : Type} [Field L]

@[expose] def dEntry (a : Fin 5 → Lˣ) : Fin 6 → Lˣ :=
  ![a 0, a 1 * (a 0)⁻¹, a 2 * (a 1)⁻¹, a 3 * (a 2)⁻¹, a 4 * (a 3)⁻¹, (a 4)⁻¹]

theorem prod_dEntry (a : Fin 5 → Lˣ) : ∏ i, dEntry a i = 1 := by
  apply Units.ext
  have h0 := (a 0).ne_zero
  have h1 := (a 1).ne_zero
  have h2 := (a 2).ne_zero
  have h3 := (a 3).ne_zero
  have h4 := (a 4).ne_zero
  simp [Fin.prod_univ_six, dEntry]

theorem dEntry_mul (a b : Fin 5 → Lˣ) (i : Fin 6) :
    dEntry (a * b) i = dEntry a i * dEntry b i := by
  apply Units.ext
  have h0 := (a 0).ne_zero
  have h1 := (a 1).ne_zero
  have h2 := (a 2).ne_zero
  have h3 := (a 3).ne_zero
  have h4 := (a 4).ne_zero
  have g0 := (b 0).ne_zero
  have g1 := (b 1).ne_zero
  have g2 := (b 2).ne_zero
  have g3 := (b 3).ne_zero
  have g4 := (b 4).ne_zero
  fin_cases i <;> simp [dEntry, Units.val_inv_eq_inv_val] <;> field_simp

theorem det_dEntry (a : Fin 5 → Lˣ) :
    (Matrix.diagonal (fun i => ((dEntry a i : Lˣ) : L))).det = 1 := by
  rw [Matrix.det_diagonal, ← Units.coe_prod, prod_dEntry, Units.val_one]

variable (L) in
@[expose] def chainDiag : (Fin 5 → Lˣ) →* SL(6, L) where
  toFun a := ⟨Matrix.diagonal (fun i => ((dEntry a i : Lˣ) : L)), det_dEntry a⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dEntry, Matrix.diagonal_apply]
  map_mul' a b := by
    apply Subtype.ext
    show Matrix.diagonal (fun i => ((dEntry (a * b) i : Lˣ) : L)) =
      Matrix.diagonal (fun i => ((dEntry a i : Lˣ) : L)) *
        Matrix.diagonal (fun i => ((dEntry b i : Lˣ) : L))
    rw [Matrix.diagonal_mul_diagonal]
    simp only [dEntry_mul, Units.val_mul]

theorem coe_chainDiag (a : Fin 5 → Lˣ) :
    ((chainDiag L a : SL(6, L)) : Matrix (Fin 6) (Fin 6) L) =
      Matrix.diagonal (fun i => ((dEntry a i : Lˣ) : L)) := rfl

theorem chainDiag_mulSingle (t : Fin 5) (s : Lˣ) :
    chainDiag L (Pi.mulSingle t s) = blockSL2 L 5 t (HSL s) := by
  apply Subtype.ext
  rw [coe_chainDiag, coe_blockSL2_HSL]
  congr 1
  funext i
  fin_cases t <;> fin_cases i <;> simp [dEntry, hEntries, Pi.mulSingle_apply]

theorem a5Frame_chainDiag (a : Fin 5 → Lˣ) :
    a5Frame L (chainDiag L a) = chainTorus L a := by
  have h : (a5Frame L).comp (chainDiag L) = chainTorus L := by
    refine MonoidHom.pi_ext fun t s => ?_
    rw [MonoidHom.comp_apply, chainDiag_mulSingle, a5Frame_blockSL2_HSL, chainTorus_mulSingle]
  exact congrArg (fun f : (Fin 5 → Lˣ) →* ModGL Tag.E7 L => f a) h

theorem chainDiag_comm (x y : (chainDiag L).range) : (x : SL(6, L)) * y = y * x := by
  obtain ⟨_, ⟨a, rfl⟩⟩ := x
  obtain ⟨_, ⟨b, rfl⟩⟩ := y
  show chainDiag L a * chainDiag L b = chainDiag L b * chainDiag L a
  rw [← map_mul, ← map_mul, mul_comm]

theorem exists_pow_six_chainDiag [IsAlgClosed L] {x : SL(6, L)} (hx : x ∈ (chainDiag L).range) :
    ∃ r ∈ (chainDiag L).range, r ^ 6 = x := by
  obtain ⟨a, rfl⟩ := hx
  have : ∀ i, ∃ r : Lˣ, r ^ 6 = a i := fun i => by
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq ((a i : Lˣ) : L) (by norm_num : 0 < 6)
    have hr0 : r ≠ 0 := by
      intro h
      rw [h] at hr
      exact (a i).ne_zero (by simpa using hr.symm)
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  choose r hr using this
  exact ⟨chainDiag L r, ⟨r, rfl⟩, by rw [← map_pow]; congr 1; funext i; exact hr i⟩

theorem ker_a5Frame_le_range_chainDiag {z : SL(6, L)} (hz : z ∈ (a5Frame L).ker) :
    z ∈ (chainDiag L).range := by
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (ker_a5Frame_le_center hz)
  simp only [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    simp at hr
  set u : Lˣ := Units.mk0 r hr0 with hu
  have hu6 : u ^ 6 = 1 := Units.ext (by simpa [hu] using hr)
  have hinv : (u ^ 5)⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hu6)
  have hdE : dEntry ![u, u ^ 2, u ^ 3, u ^ 4, u ^ 5] = fun _ => u := by
    funext i
    fin_cases i <;> simp [dEntry, hinv] <;> group
  refine ⟨![u, u ^ 2, u ^ 3, u ^ 4, u ^ 5], ?_⟩
  apply Subtype.ext
  rw [coe_chainDiag, ← hzr, hdE, Matrix.scalar_apply]
  congr 1

end Diag

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
