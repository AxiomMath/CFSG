module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

theorem mem_statedSU_iff (h : UnitaryFieldData p f K) (n : ℕ) (A : GL (Fin n) K) :
    A ∈ StatedSU n (p ^ f) K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  have hbar : (fun x : K => x ^ (p ^ f)) = ⇑h.bar := funext fun x => (h.bar_apply x).symm
  let S : Subgroup (GL (Fin n) K) :=
    { carrier := {A | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
        ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}
      one_mem' := by
        refine ⟨by simp, ?_⟩
        simp
      mul_mem' := by
        intro A B hA hB
        obtain ⟨hA1, hA2⟩ := hA
        obtain ⟨hB1, hB2⟩ := hB
        refine ⟨?_, ?_⟩
        · simp only [Units.val_mul, Matrix.det_mul, hA1, hB1, mul_one]
        · simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ
            (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin n) K), hA2, Matrix.one_mul, hB2]
      inv_mem' := by
        intro A hA
        obtain ⟨hA1, hA2⟩ := hA
        refine ⟨?_, ?_⟩
        · rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hA1, Ring.inverse_one]
        · have hinv : (A : Matrix (Fin n) (Fin n) K)⁻¹ =
              ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ :=
            Matrix.inv_eq_left_inv hA2
          have hmapinv : (((A : Matrix (Fin n) (Fin n) K)⁻¹).map h.bar) =
              ((A : Matrix (Fin n) (Fin n) K)ᵀ) := by
            rw [hinv, Matrix.transpose_map, Matrix.map_map]
            ext i j
            simp [Function.comp_def, h.bar_bar]
          rw [Matrix.coe_units_inv, hmapinv, Matrix.transpose_transpose, Matrix.mul_nonsing_inv]
          rw [hA1]
          exact isUnit_one }
  have hS : StatedSU n (p ^ f) K = S := by
    unfold StatedSU
    try unfold CFSG.MatrixModel.unitaryCore
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [hbar] at hx
      exact hx
    · intro x hx
      apply Subgroup.subset_closure
      rw [hbar]
      exact hx
  rw [hS]
  exact Iff.rfl


theorem card_filter_eq_count' {ι : Type} [Fintype ι] {L : Type} [Field L] (f : ι → L) (a : L) :
    (univ.filter fun i => f i = a).card = Multiset.count a (univ.val.map f) := by
  rw [Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _
  exact eq_comm

theorem count_eq_of_prod_eq {ι : Type} [Fintype ι] {L : Type} [Field L] (a b : ι → L)
    (hab : ∏ i, (Polynomial.X - Polynomial.C (a i)) = ∏ i, (Polynomial.X - Polynomial.C (b i)))
    (c : L) : (univ.filter fun i => a i = c).card = (univ.filter fun i => b i = c).card := by
  have hm : ∀ d : ι → L, ∏ i, (Polynomial.X - Polynomial.C (d i)) =
      ((univ.val.map d).map fun x => Polynomial.X - Polynomial.C x).prod := by
    intro d
    rw [Multiset.map_map]
    rfl
  have hroots : univ.val.map a = univ.val.map b := by
    have h1 := congrArg Polynomial.roots hab
    rw [hm a, hm b, Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.roots_multiset_prod_X_sub_C] at h1
    exact h1
  rw [card_filter_eq_count', card_filter_eq_count', hroots]

theorem symm_count_of_unitary (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (A : GL (Fin 7) K) {z : GL (Fin 7) K}
    (hz : z ∈ StatedSU 7 (p ^ f) K) {d : Fin 7 → K}
    (hd : (A : Matrix (Fin 7) (Fin 7) K) * (z : Matrix (Fin 7) (Fin 7) K) *
      ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ = Matrix.diagonal d) :
    (univ.filter fun i => d i = ζ).card = (univ.filter fun i => d i = ζ ^ 2).card := by
  rw [mem_statedSU_iff h] at hz
  obtain ⟨hdet, hunit⟩ := hz
  have hinvZ : ((z : Matrix (Fin 7) (Fin 7) K))⁻¹ =
      ((z : Matrix (Fin 7) (Fin 7) K).map h.bar)ᵀ :=
    Matrix.inv_eq_left_inv hunit
  have hA0 : IsUnit (A : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  have hdet_d : ∏ i, d i = 1 := by
    have h2 := congrArg Matrix.det hd
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_diagonal, hdet,
      mul_one, Ring.mul_inverse_cancel _ hA0] at h2
    exact h2.symm
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mp (by rw [hdet_d]; exact one_ne_zero) i (Finset.mem_univ i)
  have hcpZ : (z : Matrix (Fin 7) (Fin 7) K).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
    rw [← Matrix.charpoly_units_conj A (z : Matrix (Fin 7) (Fin 7) K), hd,
      Matrix.charpoly_diagonal]
  have hY : ((A : Matrix (Fin 7) (Fin 7) K) * ((z : Matrix (Fin 7) (Fin 7) K))⁻¹ *
      ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) = (Matrix.diagonal d)⁻¹ := by
    have hgroup : A * z⁻¹ * A⁻¹ = (A * z * A⁻¹)⁻¹ := by group
    have hval := congrArg (fun g : GL (Fin 7) K => (g : Matrix (Fin 7) (Fin 7) K)) hgroup
    simp only [Units.val_mul, Matrix.coe_units_inv] at hval
    rw [hval, hd]
  have hDinv : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    simp [Matrix.diagonal_mul_diagonal, hd0]
  have hcpZinv : ((z : Matrix (Fin 7) (Fin 7) K))⁻¹.charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (d i)⁻¹) := by
    rw [← Matrix.charpoly_units_conj A ((z : Matrix (Fin 7) (Fin 7) K))⁻¹, hY, hDinv,
      Matrix.charpoly_diagonal]
  have hcpZinv' : ((z : Matrix (Fin 7) (Fin 7) K))⁻¹.charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (h.bar (d i))) := by
    rw [hinvZ, Matrix.charpoly_transpose, Matrix.charpoly_map, hcpZ, Polynomial.map_prod]
    simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hEq : ∏ i, (Polynomial.X - Polynomial.C (d i)⁻¹) =
      ∏ i, (Polynomial.X - Polynomial.C (h.bar (d i))) :=
    hcpZinv.symm.trans hcpZinv'
  have hbarζ : h.bar ζ = ζ := by
    obtain ⟨k, hk⟩ := hQ
    have hpos : 0 < p ^ f := pow_pos h.prime.pos f
    have hq : p ^ f = 3 * k + 1 := by omega
    rw [h.bar_apply, hq, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hζinv : ζ⁻¹ = ζ ^ 2 := by
    have h' : ζ ^ 2 * ζ = 1 := by rw [← pow_succ]; exact hζ.pow_eq_one
    exact (eq_inv_of_mul_eq_one_left h').symm
  have hc1 : (univ.filter fun i => (d i)⁻¹ = ζ).card =
      (univ.filter fun i => h.bar (d i) = ζ).card :=
    count_eq_of_prod_eq (fun i => (d i)⁻¹) (fun i => h.bar (d i)) hEq ζ
  have hc2 : (univ.filter fun i => h.bar (d i) = ζ) = (univ.filter fun i => d i = ζ) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro hi
      apply h.bar.injective
      rw [hi, hbarζ]
    · intro hi
      rw [hi, hbarζ]
  have hc3 : (univ.filter fun i => (d i)⁻¹ = ζ) = (univ.filter fun i => d i = ζ ^ 2) := by
    apply Finset.filter_congr
    intro i _
    rw [inv_eq_iff_eq_inv, hζinv]
  rw [hc3, hc2] at hc1
  exact hc1.symm

theorem exists_diag_StatedSU (h : UnitaryFieldData p f K) {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (P : Subgroup (GL (Fin 7) K)) (hP : ∀ x ∈ P, x ∈ StatedSU 7 (p ^ f) K)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hpow : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ A : GL (Fin 7) K, ∀ x ∈ P, ∀ i j, i ≠ j →
      ((A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
        ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) i j = 0 := by
  have hdetP : ∀ x ∈ P, (x : Matrix (Fin 7) (Fin 7) K).det = 1 := fun x hx =>
    ((mem_statedSU_iff h 7 x).mp (hP x hx)).1
  let E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K) :=
    P.comap (Matrix.SpecialLinearGroup.toGL (n := Fin 7) (R := K))
  have hmem : ∀ x ∈ P, ∃ y ∈ E₀, (y : Matrix (Fin 7) (Fin 7) K) = (x : Matrix (Fin 7) (Fin 7) K) := by
    intro x hx
    refine ⟨⟨(x : Matrix (Fin 7) (Fin 7) K), hdetP x hx⟩, ?_, rfl⟩
    have hg : Matrix.SpecialLinearGroup.toGL (n := Fin 7) (R := K)
        ⟨(x : Matrix (Fin 7) (Fin 7) K), hdetP x hx⟩ = x := Units.ext rfl
    exact Subgroup.mem_comap.mpr (by rw [hg]; exact hx)
  have hcomm' : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    have ha' : Matrix.SpecialLinearGroup.toGL (n := Fin 7) (R := K) a ∈ P :=
      Subgroup.mem_comap.mp ha
    have hb' : Matrix.SpecialLinearGroup.toGL (n := Fin 7) (R := K) b ∈ P :=
      Subgroup.mem_comap.mp hb
    have key := congrArg (fun g : GL (Fin 7) K => (g : Matrix (Fin 7) (Fin 7) K))
      (hcomm _ ha' _ hb')
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact key
  have hpow' : ∀ a ∈ E₀, a ^ 3 = 1 := by
    intro a ha
    have ha' : Matrix.SpecialLinearGroup.toGL (n := Fin 7) (R := K) a ∈ P :=
      Subgroup.mem_comap.mp ha
    have h3 : (((Matrix.SpecialLinearGroup.toGL (n := Fin 7) (R := K) a) ^ 3 :
        GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
        ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
      rw [hpow _ ha']
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h3
    exact h3
  haveI : Finite K := h.finite
  obtain ⟨A, hA⟩ :=
    CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀ hcomm' hpow'
  refine ⟨A, fun x hx i j hij => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hmem x hx
  have hyz := hA y hy i j hij
  rw [← hyx]
  exact hyz

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
