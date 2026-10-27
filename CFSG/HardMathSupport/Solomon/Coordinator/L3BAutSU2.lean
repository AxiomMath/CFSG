module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutQ2
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSU
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag
open Matrix.GeneralLinearGroup (scalar coe_scalar)
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def hF (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

section Char2

variable [CharP K 2] {ω : K} (hsum : ω ^ 2 + ω + 1 = 0)
include hsum

theorem det_hF : (hF ω).det = 1 := by
  simp [hF, Matrix.det_fin_three]
  grind

theorem hF_mul_hF : hF ω * hF ω = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hF, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem hF_mul_hP : hF ω * (hP : Matrix (Fin 3) (Fin 3) K) = hX ω * hF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hF, hX, hP, Matrix.mul_apply,
    Matrix.diagonal_apply] <;> grind

theorem hP_mul_hF_mul_hX : (hP : Matrix (Fin 3) (Fin 3) K) * hF ω * hX ω = hF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hF, hX, hP, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.diagonal_apply] <;> grind

theorem hF_unitary {p f : ℕ} (h : UnitaryFieldData p f K) (hq : p ^ f = 2) :
    ((hF ω).map h.bar)ᵀ * hF ω = 1 := by
  have hb : ∀ x : K, h.bar x = x ^ 2 := fun x => by rw [h.bar_apply, hq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hF, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, hb] <;> grind

end Char2

theorem eq_scalar_of_commute {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (A : Matrix (Fin 3) (Fin 3) K) (h1 : A * hX ω = hX ω * A)
    (h2 : A * (hP : Matrix (Fin 3) (Fin 3) K) = hP * A) : A = Matrix.scalar (Fin 3) (A 0 0) := by
  have e1 : ∀ i j : Fin 3, A i j * ω ^ (j : ℕ) = ω ^ (i : ℕ) * A i j := by
    intro i j
    have := congrFun (congrFun h1 i) j
    simpa [hX, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have e2 : ∀ i j : Fin 3, A i (j + 1) = A (i - 1) j := by
    intro i j
    have := congrFun (congrFun h2 i) j
    simpa [mul_hP_apply, hP_mul_apply] using this
  have off : ∀ i j : Fin 3, i ≠ j → A i j = 0 := fun i j hij => by
    have h := e1 i j
    have hne : ω ^ (j : ℕ) - ω ^ (i : ℕ) ≠ 0 :=
      sub_ne_zero.2 (fun h' => hij (pow_inj_fin_three hω3 hω1 h'.symm))
    have : A i j * (ω ^ (j : ℕ) - ω ^ (i : ℕ)) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_right hne
  have d1 : A 1 1 = A 0 0 := by simpa using e2 1 0
  have d2 : A 2 2 = A 1 1 := by
    have h := e2 2 1
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (2 : Fin 3) - 1 = 1 from rfl] at h
    exact h
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [Matrix.scalar_apply, d1, d2]
  · rw [off i j hij]
    simp [Matrix.scalar_apply, hij]

theorem sylowCentreInn_statedSU_two [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    SylowCentreInn ↥(StatedSU 3 (2 ^ 1) K) := by
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hchar : CharP K 2 := h.charP
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root K (by rw [hK]; norm_num)
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  have hωq : ω ^ (2 ^ 1) = ω ^ 2 := by norm_num
  set H : Subgroup (GL (Fin 3) K) := StatedSU 3 (2 ^ 1) K with hH
  have hXH : Matrix.SpecialLinearGroup.toGL (hXsl hω3) ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hX hω3, hX_unitary h hω3 hωq⟩
  have hPH : Matrix.SpecialLinearGroup.toGL (hPsl : Matrix.SpecialLinearGroup (Fin 3) K) ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hP, hP_unitary h⟩
  have hω0 := ne_zero_of_pow_three hω3
  have hwH : wGL hω3 ∈ H := scalar_mem_unitarySU h (by norm_num) (c := Units.mk0 ω hω0)
    (by
      show ω * h.bar ω = 1
      rw [h.bar_apply]
      calc ω * ω ^ 2 ^ 1 = ω ^ 3 := by ring
        _ = 1 := hω3)
    (Units.ext (by simpa using hω3))
  let Fsl : Matrix.SpecialLinearGroup (Fin 3) K := ⟨hF ω, det_hF hsum⟩
  have hFH : Matrix.SpecialLinearGroup.toGL Fsl ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hF hsum, hF_unitary hsum h rfl⟩
  have hcard : Nat.card ↥H = 216 := by
    have hZ := card_unitaryScalars h (n := 3) (by norm_num)
    have hPSU : Nat.card (unitaryPSU h 3) = 72 := by
      rw [Nat.card_congr (unitaryPSUEquiv h (n := 3) (by norm_num)).toEquiv]
      exact CFSG.Quasithin.card_statedProj_one hK
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars h 3)
    rw [hZ, hPSU] at this
    have h3 : Nat.gcd 3 (2 ^ 1 + 1) = 3 := by norm_num
    rw [h3] at this
    exact this
  let Xm : ↥H := ⟨_, hXH⟩
  let Pm : ↥H := ⟨_, hPH⟩
  let wm : ↥H := ⟨_, hwH⟩
  let Fm : ↥H := ⟨_, hFH⟩
  have hcomm_scalar : ∀ y : ↥H, y * Xm = Xm * y → y * Pm = Pm * y →
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) := by
    intro y h1 h2
    refine eq_scalar_of_commute hω3 hω1 _ ?_ ?_
    · have := congrArg (fun u : ↥H => ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
      exact this
    · have := congrArg (fun u : ↥H => ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h2
      exact this
  have htt : (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have htne : (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun h' => by
    have := congrFun (congrFun h' 1) 1
    simp at this
  have hFF : (((Matrix.SpecialLinearGroup.toGL Fsl) ^ 2 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    rw [Units.val_pow_eq_pow_val, pow_two]
    exact hF_mul_hF hsum
  have hHeis : HeisData ↥H Xm Pm wm Fm := by
    refine
      { card := hcard
        w_central := fun g => Subtype.ext (Matrix.GeneralLinearGroup.scalar_commute _ _)
        w_pow := Subtype.ext (wGL_pow_three hω3)
        w_ne := ?_
        X_pow := Subtype.ext (XGL_pow_three hω3)
        P_pow := Subtype.ext PGL_pow_three
        XP := Subtype.ext (XGL_mul_PGL hω3)
        FP := ?_
        FX := ?_
        F_pow := ?_
        F_sq := ?_
        cent := ?_
        center_le := ?_ }
    · intro h'
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0)
        (congrArg Subtype.val h')
      simp [wm, wGL, Matrix.scalar_apply] at this
      exact hω1 this
    · refine Subtype.ext (mul_inv_eq_iff_eq_mul.2 (Units.ext ?_))
      exact hF_mul_hP hsum
    · refine Subtype.ext (mul_inv_eq_iff_eq_mul.2 ?_)
      refine (inv_mul_eq_iff_eq_mul.2 (Units.ext ?_)).symm
      show (hF ω) = (hP : Matrix (Fin 3) (Fin 3) K) * (hF ω * hX ω)
      rw [← mul_assoc]
      exact (hP_mul_hF_mul_hX hsum).symm
    · refine Subtype.ext (Units.ext ?_)
      show (((Matrix.SpecialLinearGroup.toGL Fsl) ^ 4 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Units.val_pow_eq_pow_val, hFF, pow_two, htt]
    · intro h'
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K))
        (congrArg Subtype.val h')
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [hFF] at this
      exact htne this
    · intro y h1 h2
      have hy := hcomm_scalar y h1 h2
      refine Subgroup.mem_center_iff.2 fun g => Subtype.ext (Units.ext ?_)
      show ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((y : GL (Fin 3) K) : Matrix _ _ K)
        = ((y : GL (Fin 3) K) : Matrix _ _ K) * ((g : GL (Fin 3) K) : Matrix _ _ K)
      rw [hy]
      exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).symm.eq
    · intro z hz
      have h1 : z * Xm = Xm * z := (Subgroup.mem_center_iff.1 hz Xm).symm
      have h2 : z * Pm = Pm * z := (Subgroup.mem_center_iff.1 hz Pm).symm
      have hzs := hcomm_scalar z h1 h2
      set c : K := ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 with hc
      have hdet : c ^ 3 = 1 := by
        have := ((mem_unitarySU_iff h).1 z.2).1
        rw [hzs] at this
        simpa [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ] using this
      obtain ⟨b, -, hb⟩ := eq_pow_of_pow_three_eq_one hω3 hω1 hdet
      refine Subgroup.mem_zpowers_iff.2 ⟨b, ?_⟩
      refine Subtype.ext (Units.ext ?_)
      rw [zpow_natCast]
      show (((wGL hω3) ^ b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [hzs, wGL, ← map_pow, coe_scalar, Units.val_pow_eq_pow_val, Units.val_mk0, hb]
  exact sylowCentreInn_of_heis hHeis

end CFSG.HardMathSupport.Solomon.Coordinator
