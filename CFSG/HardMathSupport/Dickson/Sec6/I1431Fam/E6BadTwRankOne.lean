module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section Matrices

variable {K : Type} [Field K]

theorem rankOne_upper_mul_lower :
    (!![1, 1; 0, 1] * !![1, 0; -3, 1] : Matrix (Fin 2) (Fin 2) K) = !![-2, 1; -3, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rankOne_matrix_conj {z zi e : K} (hz : z ^ 2 + z + 1 = 0) (hzi : zi = z ^ 2)
    (he : e * (z ^ 2 - z) = 1) :
    (!![1, 0; z ^ 2 + 1, 1] * !![1, 1; 0, 1] * !![1, 0; e - 1, 1] : Matrix (Fin 2) (Fin 2) K) *
        !![z, 0; 0, zi] =
      !![-2, 1; -3, 1] * (!![1, 0; z ^ 2 + 1, 1] * !![1, 1; 0, 1] * !![1, 0; e - 1, 1]) := by
  subst hzi
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-1 : K) * he
  · ring
  · linear_combination (z - 1) * he + e * hz
  · linear_combination (z ^ 2 - z + 1) * hz

end Matrices

section

variable {K : Type} [Field K]

theorem endo_xm_pos_eq_blockOp (b : Fin Tag.E6.rank) (c : K) :
    e6Data_valid.endo K (e6Data_valid.xm K (Pi.single b 1) c) =
      e6Data_valid.blockOp K b !![1, c; 0, 1] :=
  (e6Data_valid.endo_xm K _ c).trans (e6Data_valid.blockOp_upper K b c).symm

theorem endo_xm_neg_eq_blockOp (b : Fin Tag.E6.rank) (c : K) :
    e6Data_valid.endo K (e6Data_valid.xm K (-Pi.single b 1) c) =
      e6Data_valid.blockOp K b !![1, 0; c, 1] :=
  (e6Data_valid.endo_xm K _ c).trans (e6Data_valid.blockOp_lower K b c).symm

theorem endo_rankOneThree (b : Fin Tag.E6.rank) :
    e6Data_valid.endo K (rankOneThree K b) = e6Data_valid.blockOp K b !![-2, 1; -3, 1] := by
  unfold rankOneThree
  rw [e6Data_valid.endo_mul, endo_xm_pos_eq_blockOp, endo_xm_neg_eq_blockOp,
    ← e6Data_valid.blockOp_mul, rankOne_upper_mul_lower]

theorem exists_conj_rankOneThree (b : Fin Tag.E6.rank) (ζ : Kˣ)
    (hζ : (ζ : K) ^ 2 + ζ + 1 = 0) (h3 : (3 : K) ≠ 0) :
    ∃ g ∈ rootPair K (Pi.single b 1 : Fin Tag.E6.rank → ℤ),
      g * e6Data_valid.hm K b ζ * g⁻¹ = rankOneThree K b := by
  have hzi : ((ζ⁻¹ : Kˣ) : K) = (ζ : K) ^ 2 := by
    have h1 : (ζ : K) * ((ζ⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ζ
    linear_combination (ζ : K) ^ 2 * h1 - ((ζ⁻¹ : Kˣ) : K) * ((ζ : K) - 1) * hζ
  have hd : (ζ : K) ^ 2 - ζ ≠ 0 := by
    intro h
    apply h3
    linear_combination ((ζ : K) ^ 2 - 3 * ζ + 3) * hζ - ((ζ : K) ^ 2 - ζ) * h
  obtain ⟨e, he⟩ : ∃ e : K, e * ((ζ : K) ^ 2 - ζ) = 1 := ⟨_, inv_mul_cancel₀ hd⟩
  have hp : e6Data_valid.xm K (Pi.single b 1) (1 : K) ∈
      rootPair K (Pi.single b 1 : Fin Tag.E6.rank → ℤ) :=
    Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup K _ _)
  have hn : ∀ c : K, e6Data_valid.xm K (-Pi.single b 1) c ∈
      rootPair K (Pi.single b 1 : Fin Tag.E6.rank → ℤ) :=
    fun c => Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup K _ _)
  refine ⟨e6Data_valid.xm K (-Pi.single b 1) ((ζ : K) ^ 2 + 1) *
    e6Data_valid.xm K (Pi.single b 1) 1 * e6Data_valid.xm K (-Pi.single b 1) (e - 1),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hn _) hp) (hn _), ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine e6Data_valid.endo_injective K ?_
  simp only [e6Data_valid.endo_mul, endo_xm_neg_eq_blockOp, endo_xm_pos_eq_blockOp,
    endo_rankOneThree, e6Data_valid.endo_hm]
  rw [← e6Data_valid.blockOp_diag]
  simp only [← e6Data_valid.blockOp_mul]
  congr 1
  exact rankOne_matrix_conj hζ hzi he

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
