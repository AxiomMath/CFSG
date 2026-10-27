module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorus


public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open TwA5Four

namespace TwA5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.LinearPilot
open CFSG.LocalAnalysis.GLTheoremA
open Matrix

variable {F : Type} [Field F]


private theorem fiveLine_mixed_entries_zero
    (M : Matrix (Fin 6) (Fin 6) F)
    (h02 : M 0 2 = 0) (h20 : M 2 0 = 0) (h12 : M 1 2 = 0) (h21 : M 2 1 = 0)
    (h03 : M 0 3 = 0) (h30 : M 3 0 = 0) (h13 : M 1 3 = 0) (h31 : M 3 1 = 0)
    (h04 : M 0 4 = 0) (h40 : M 4 0 = 0) (h14 : M 1 4 = 0) (h41 : M 4 1 = 0)
    (h5 : ∀ i, i ≠ 5 → M i 5 = 0) (h5' : ∀ j, j ≠ 5 → M 5 j = 0) :
    ∀ i j, (i ∈ ({0, 1} : Finset (Fin 6)) ↔ j ∉ ({0, 1} : Finset (Fin 6))) → M i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [h02, h20, h12, h21, h03, h30, h13, h31, h04, h40, h14, h41]

private theorem inf_centralizer_fiveLineSubgroup_le_unitaryBlockDiag
    (h : UnitaryFieldData 2 2 F) {ζu : Fˣ} (hζu : orderOf ζu = 5) :
    unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) ⊓
        Subgroup.centralizer (fiveLineSubgroup h : Set (unitarySU 2 2 F 6)) ≤
      unitaryBlockDiag h ({0, 1} : Finset (Fin 6)) := by
  haveI := h.finite
  let ζm : rootsOfUnity 5 F := rootsOfUnityOfNormOne (h := h) ζu (norm_zeta hζu)
  let y1p : unitaryTorusParam h ({0, 1} : Finset (Fin 6)) :=
    torusParamFourInv ![1, ζm, ζm⁻¹, 1]
  let y2p : unitaryTorusParam h ({0, 1} : Finset (Fin 6)) :=
    torusParamFourInv ![1, 1, ζm, ζm⁻¹]
  let y1 : unitarySU 2 2 F 6 := torusDiagSU h (fiveTorusParamIncl y1p)
  let y2 : unitarySU 2 2 F 6 := torusDiagSU h (fiveTorusParamIncl y2p)
  have hy1ker : y1p ∈ (fiveTorusEvalUnit (h := h)).ker := by
    rw [MonoidHom.mem_ker]
    simp [fiveTorusEvalUnit, y1p]
  have hy2ker : y2p ∈ (fiveTorusEvalUnit (h := h)).ker := by
    rw [MonoidHom.mem_ker]
    simp [fiveTorusEvalUnit, y2p]
  have hy1E : y1 ∈ fiveLineSubgroup h :=
    ⟨fiveTorusParamIncl y1p, Subgroup.mem_map_of_mem _ hy1ker, rfl⟩
  have hy2E : y2 ∈ fiveLineSubgroup h :=
    ⟨fiveTorusParamIncl y2p, Subgroup.mem_map_of_mem _ hy2ker, rfl⟩
  rintro A ⟨hAJ, hAC⟩
  have hc1 : A * y1 = y1 * A :=
    (Subgroup.mem_centralizer_iff.1 hAC _ hy1E).symm
  have hc2 : A * y2 = y2 * A :=
    (Subgroup.mem_centralizer_iff.1 hAC _ hy2E).symm
  have hmat1 : ((y1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      diagonal (fun i => ((y1p).1 i : Fˣ) : Fin 6 → F) := by
    rw [show y1 = torusDiagSU h (fiveTorusParamIncl y1p) from rfl, coe_torusDiagSU]
    congr 1
    funext i
    rw [coe_fiveTorusParamIncl]
  have hmat2 : ((y2 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      diagonal (fun i => ((y2p).1 i : Fˣ) : Fin 6 → F) := by
    rw [show y2 = torusDiagSU h (fiveTorusParamIncl y2p) from rfl, coe_torusDiagSU]
    congr 1
    funext i
    rw [coe_fiveTorusParamIncl]
  have hz1 : ∀ i j, ((y1p).1 i : F) ≠ ((y1p).1 j : F) →
      (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) i j = 0 := by
    intro i j hij
    apply apply_eq_zero_of_mul_diagonal_eq
      (A := (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)))
      (d := fun i => ((y1p).1 i : F))
    · have := congrArg (fun B : unitarySU 2 2 F 6 =>
        (((B : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) hc1
      simpa [hmat1] using this
    · exact hij
  have hz2 : ∀ i j, ((y2p).1 i : F) ≠ ((y2p).1 j : F) →
      (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) i j = 0 := by
    intro i j hij
    apply apply_eq_zero_of_mul_diagonal_eq
      (A := (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)))
      (d := fun i => ((y2p).1 i : F))
    · have := congrArg (fun B : unitarySU 2 2 F 6 =>
        (((B : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) hc2
      simpa [hmat2] using this
    · exact hij
  have hz : ((ζu : Fˣ) : F) ≠ 1 := by
    intro h
    exact zeta_ne_one hζu (Units.ext h)
  have h1z : (1 : F) ≠ ((ζu : Fˣ) : F) := hz.symm
  have hzinv : (((ζu : Fˣ) : F)⁻¹) ≠ 1 := inv_ne_one.mpr hz
  have h1zinv : (1 : F) ≠ (((ζu : Fˣ) : F)⁻¹) := hzinv.symm
  have h02 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 0 2 = 0 := by
    apply hz1 0 2; simpa [y1p, ζm] using h1z
  have h20 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 2 0 = 0 := by
    apply hz1 2 0; simpa [y1p, ζm] using hz
  have h12 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 1 2 = 0 := by
    apply hz1 1 2; simpa [y1p, ζm] using h1z
  have h21 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 2 1 = 0 := by
    apply hz1 2 1; simpa [y1p, ζm] using hz
  have h03 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 0 3 = 0 := by
    apply hz1 0 3; simpa [y1p, ζm] using h1zinv
  have h30 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 3 0 = 0 := by
    apply hz1 3 0; simpa [y1p, ζm] using hzinv
  have h13 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 1 3 = 0 := by
    apply hz1 1 3; simpa [y1p, ζm] using h1zinv
  have h31 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 3 1 = 0 := by
    apply hz1 3 1; simpa [y1p, ζm] using hzinv
  have h04 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 0 4 = 0 := by
    apply hz2 0 4; simpa [y2p, ζm] using h1zinv
  have h40 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 4 0 = 0 := by
    apply hz2 4 0; simpa [y2p, ζm] using hzinv
  have h14 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 1 4 = 0 := by
    apply hz2 1 4; simpa [y2p, ζm] using h1zinv
  have h41 : (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 4 1 = 0 := by
    apply hz2 4 1; simpa [y2p, ζm] using hzinv
  have h5 : ∀ i, i ≠ 5 → (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) i 5 = 0 := by
    intro i hi
    have := (mem_unitaryBlock h).1 hAJ i 5 (Or.inr (by simp))
    simpa [Matrix.one_apply, hi] using this
  have h5' : ∀ j, j ≠ 5 → (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) 5 j = 0 := by
    intro j hj
    have := (mem_unitaryBlock h).1 hAJ 5 j (Or.inl (by simp))
    simpa [Matrix.one_apply, Ne.symm hj] using this
  rw [mem_unitaryBlockDiag]
  exact fiveLine_mixed_entries_zero _ h02 h20 h12 h21 h03 h30 h13 h31 h04 h40 h14 h41 h5 h5'

theorem glaPLayer_fiveLineSubgroup_ne_bot
    (h : UnitaryFieldData 2 2 F) {ζu : Fˣ} (hζu : orderOf ζu = 5) :
    GLAPLayer 5
      (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) ⊓
        Subgroup.centralizer (fiveLineSubgroup h : Set (unitarySU 2 2 F 6))) ≠ ⊥ := by
  haveI := h.finite
  have hI : (({0, 1} : Finset (Fin 6)).card) = 2 := by decide
  refine glaPLayer_ne_bot_of_unitaryBlock_le (I := ({0, 1} : Finset (Fin 6))) h Nat.prime_five ?_ ?_ ?_ ?_
  · intro x hx
    exact ⟨unitaryBlock_mono h (by decide) hx,
      unitaryBlock_two_le_centralizer_fiveLineSubgroup h hx⟩
  · exact inf_centralizer_fiveLineSubgroup_le_unitaryBlockDiag h hζu
  · exact isQuasisimple_unitaryBlock_of_card_eq_two h hI (by norm_num)
  · exact dvd_card_unitaryBlock_of_card_eq_two h hI Nat.prime_five (by norm_num)

end TwA5Four

end CFSG.LocalAnalysis.GLTheoremA.Y10F
