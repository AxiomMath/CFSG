module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankCover
import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.SteinbergBR.EvenSp

section Planes

variable {K : Type} [Field K]

private noncomputable def planeSp : (Fin 4 → SpecialLinearGroup (Fin 2) K) →* StatedSp 4 K :=
  (planeHom.comp (MonoidHom.compLeft SpecialLinearGroup.toGL (Fin 4))).codRestrict
    (StatedSp 4 K) fun g => planeHom_mem_statedSp _ fun j => by simp

private theorem planeSp_injective : Function.Injective (planeSp (K := K)) := by
  intro g g' hg
  have h := planeHom_injective (congrArg Subtype.val hg)
  funext j
  exact SpecialLinearGroup.toGL_injective (congrFun h j)

private noncomputable def planeIncl (i : Fin 4) :
    SpecialLinearGroup (Fin 2) K →* StatedSp 4 K :=
  planeSp.comp (MonoidHom.mulSingle (fun _ : Fin 4 => SpecialLinearGroup (Fin 2) K) i)

private theorem planeIncl_injective (i : Fin 4) : Function.Injective (planeIncl (K := K) i) :=
  fun _ _ hxy => Pi.mulSingle_injective (M := fun _ : Fin 4 => SpecialLinearGroup (Fin 2) K) i
    (planeSp_injective hxy)

private theorem planeIncl_commute {i j : Fin 4} (hij : i ≠ j) (x y : SpecialLinearGroup (Fin 2) K) :
    Commute (planeIncl i x) (planeIncl j y) :=
  (Pi.mulSingle_commute (f := fun _ : Fin 4 => SpecialLinearGroup (Fin 2) K) hij x y).map planeSp

end Planes

section CharTwo

variable {K : Type} [Field K] [CharP K 2]

private def tSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 1], by rw [det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]⟩

private def sSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by rw [det_fin_two_of]; simp⟩

private theorem tSL_cube : tSL * tSL * tSL = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  change (!![0, 1; 1, 1] * !![0, 1; 1, 1] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  rw [mul_fin_two, mul_fin_two, one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem tSL_ne_one : tSL (K := K) ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [tSL] at this

private theorem sSL_mul_self : sSL * sSL = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  change (!![1, 1; 0, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  rw [mul_fin_two, one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem sSL_mul_tSL_mul_sSL :
    sSL * tSL * sSL = (tSL * tSL : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  change (!![1, 1; 0, 1] * !![0, 1; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (!![0, 1; 1, 1] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j
  rw [mul_fin_two, mul_fin_two, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem sSL_mul_tSL_mul_inv :
    sSL * tSL * sSL⁻¹ = (tSL : SpecialLinearGroup (Fin 2) K)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right sSL_mul_self, sSL_mul_tSL_mul_sSL,
    inv_eq_of_mul_eq_one_right (a := tSL) (b := tSL * tSL) (by rw [← mul_assoc]; exact tSL_cube)]

theorem centralCoverFour_statedSp_four : CentralCoverFour (StatedSp 4 K) := by
  refine centralCoverFour_of_inverters (fun i => planeIncl i tSL) (fun i => planeIncl i sSL)
    ?_ ?_ ?_ ?_
  · intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact planeIncl_commute hij _ _
  · intro i
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_succ, sq, tSL_cube, map_one]
    · intro h
      exact tSL_ne_one (planeIncl_injective i (by rw [h, map_one]))
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, sSL_mul_tSL_mul_inv, map_inv]
  · intro i j hij
    exact (planeIncl_commute hij _ _).mul_inv_cancel

end CharTwo

open TauCeti

theorem centralCoverFour_B4Two (q : PrimePower) (hv : (LieTypeIndex.B 4 q).Valid)
    (hp : q.p = 2) (_he : q.exponent = 1) :
    CentralCoverFour (ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩) := by
  have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B 4 q, hv⟩) 2 := by
    have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B 4 q, hv⟩)
        (ValidLieTypeIndex.characteristic ⟨.B 4 q, hv⟩) := inferInstance
    exact CharP.congr (ValidLieTypeIndex.characteristic ⟨.B 4 q, hv⟩)
      ((LieTypeIndex.characteristic_B 4 q).trans hp)
  exact CentralCoverFour.of_mulEquiv
    ((CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 4 q hv hp
      (by norm_num)).trans (projEquiv (by norm_num))).symm
    centralCoverFour_statedSp_four

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank
