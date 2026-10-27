module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SecOdd
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier

public section

namespace CFSG.EvenSporadicStandard.Induction

open Matrix CFSG.Blueprint

section Matrices

variable {K : Type} [Field K] [CharP K 2]

def l3MatA : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

def l3MatB : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

theorem two_eq_zero_of_charP : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem l3MatA_mul_self : (l3MatA : Matrix (Fin 3) (Fin 3) K) * l3MatA = 1 := by
  have h2 := two_eq_zero_of_charP (K := K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l3MatA, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | rfl | linear_combination h2

theorem l3MatB_mul_self : (l3MatB : Matrix (Fin 3) (Fin 3) K) * l3MatB = 1 := by
  have h2 := two_eq_zero_of_charP (K := K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l3MatB, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | rfl | linear_combination h2

theorem l3MatAB_pow_four : ((l3MatA : Matrix (Fin 3) (Fin 3) K) * l3MatB) ^ 4 = 1 := by
  have h2 := two_eq_zero_of_charP (K := K)
  have e : ((l3MatA : Matrix (Fin 3) (Fin 3) K) * l3MatB) ^ 4 =
      ((l3MatA * l3MatB) * (l3MatA * l3MatB)) * ((l3MatA * l3MatB) * (l3MatA * l3MatB)) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l3MatA, l3MatB, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | rfl | linear_combination h2 | linear_combination 2 * h2 | linear_combination 5 * h2

def l3GlA : Matrix.GeneralLinearGroup (Fin 3) K :=
  ⟨l3MatA, l3MatA, l3MatA_mul_self, l3MatA_mul_self⟩

def l3GlB : Matrix.GeneralLinearGroup (Fin 3) K :=
  ⟨l3MatB, l3MatB, l3MatB_mul_self, l3MatB_mul_self⟩

theorem l3GlA_mul_self : (l3GlA : Matrix.GeneralLinearGroup (Fin 3) K) * l3GlA = 1 :=
  Units.ext l3MatA_mul_self

theorem l3GlB_mul_self : (l3GlB : Matrix.GeneralLinearGroup (Fin 3) K) * l3GlB = 1 :=
  Units.ext l3MatB_mul_self

theorem l3GlA_mem : (l3GlA : Matrix.GeneralLinearGroup (Fin 3) K) ∈
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) K →* Kˣ).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  simp [l3GlA, l3MatA, Matrix.det_fin_three]

theorem l3GlB_mem : (l3GlB : Matrix.GeneralLinearGroup (Fin 3) K) ∈
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) K →* Kˣ).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  simp [l3GlB, l3MatB, Matrix.det_fin_three]

theorem projSL_three_dihedral :
    ∃ u v : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K), u * u = 1 ∧ v * v = 1 ∧
      (u * v) ^ 4 = 1 ∧ u * v ≠ v * u := by
  let u : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K) :=
    ⟨Matrix.ProjGenLinGroup.mk l3GlA, l3GlA, l3GlA_mem, rfl⟩
  let v : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K) :=
    ⟨Matrix.ProjGenLinGroup.mk l3GlB, l3GlB, l3GlB_mem, rfl⟩
  have hu : u * u = 1 := by
    apply Subtype.ext
    show Matrix.ProjGenLinGroup.mk l3GlA * Matrix.ProjGenLinGroup.mk l3GlA = 1
    rw [← map_mul, l3GlA_mul_self, map_one]
  have hv : v * v = 1 := by
    apply Subtype.ext
    show Matrix.ProjGenLinGroup.mk l3GlB * Matrix.ProjGenLinGroup.mk l3GlB = 1
    rw [← map_mul, l3GlB_mul_self, map_one]
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · apply Subtype.ext
    show (Matrix.ProjGenLinGroup.mk l3GlA * Matrix.ProjGenLinGroup.mk l3GlB) ^ 4 = 1
    rw [← map_mul, ← map_pow]
    have : (l3GlA * l3GlB : Matrix.GeneralLinearGroup (Fin 3) K) ^ 4 = 1 :=
      Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mul]
        exact l3MatAB_pow_four (K := K))
    rw [this, map_one]
  · intro h
    have h1 : Matrix.ProjGenLinGroup.mk (l3GlA (K := K) * l3GlB) =
        Matrix.ProjGenLinGroup.mk (l3GlB (K := K) * l3GlA) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h
    have h2 : (l3GlA (K := K) * l3GlB)⁻¹ * (l3GlB * l3GlA) ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) K) :=
      QuotientGroup.eq.1 h1
    have hAi : (l3GlA : Matrix.GeneralLinearGroup (Fin 3) K)⁻¹ = l3GlA :=
      inv_eq_of_mul_eq_one_right l3GlA_mul_self
    have hBi : (l3GlB : Matrix.GeneralLinearGroup (Fin 3) K)⁻¹ = l3GlB :=
      inv_eq_of_mul_eq_one_right l3GlB_mul_self
    rw [_root_.mul_inv_rev, hAi, hBi] at h2
    obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h2
    have := congrFun (congrFun ha 0) 2
    simp [l3GlA, l3GlB, l3MatA, l3MatB, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar_apply, Matrix.diagonal] at this

end Matrices

theorem sylowNonabelian_of_lieModel_psl_three {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 3 2 n) : SylowNonabelian X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel h (by decide)
  have : CharP K 2 :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.charP_two_of_card hn hK rfl
  let e' : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K :=
    e.trans (CFSG.RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm
  have : Finite ↥(CFSG.Assembly.RankThreeEven.projSL 3 K) := Finite.of_equiv X e'.toEquiv
  obtain ⟨u, v, hu, hv, huv, hne⟩ := projSL_three_dihedral (K := K)
  exact SylowNonabelian.of_mulEquiv e' (sylowNonabelian_of_dihedral hu hv huv hne)

end CFSG.EvenSporadicStandard.Induction
