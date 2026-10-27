module

public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements
public import CFSG.LieType.Steinberg.PartB
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexSL2

public noncomputable section
namespace CFSG.LinearGroups.SL2

open Matrix CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

private theorem upper_sq (s : F) : sl2Upper s ^ 2 = 1 := by
  change CFSG.RankThree.CentralCover.sl2Upper s ^ 2 = 1
  rw [CFSG.RankThree.CentralCover.sl2Upper_pow]
  simp [CharTwo.two_eq_zero, CFSG.RankThree.CentralCover.sl2Upper]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lower_form_of_involution_pair {B : SL(2, F)}
    (hB2 : B ^ 2 = 1) (hBne : B ≠ sl2Upper (1 : F))
    (hCube : (sl2Upper (1 : F) * B) ^ 3 = 1) :
    ∃ t : F, B * sl2Upper t = sl2Upper t * sl2Lower 1 := by
  let a : F := (B : Matrix (Fin 2) (Fin 2) F) 0 0
  let b : F := (B : Matrix (Fin 2) (Fin 2) F) 0 1
  let c : F := (B : Matrix (Fin 2) (Fin 2) F) 1 0
  let d : F := (B : Matrix (Fin 2) (Fin 2) F) 1 1
  have hmat : (B : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hB2
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_two] at hsq
  have e00 : a * a + b * c = 1 := by
    have hh := congrFun (congrFun hsq 0) 0
    simpa [hmat, Matrix.mul_apply, Fin.sum_univ_two] using hh
  have e11 : c * b + d * d = 1 := by
    have hh := congrFun (congrFun hsq 1) 1
    simpa [hmat, Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hda : d = a := by
    have hh : (a - d) * (a - d) = 0 := by
      linear_combination e00 - e11 + (d * (d - a)) * h2
    exact (sub_eq_zero.mp (mul_self_eq_zero.mp hh)).symm
  have hdet : a * a + b * c = 1 := e00
  have hcne : c ≠ 0 := by
    intro hc
    have hdet0 : a * a = 1 := by simpa [hc] using hdet
    have ha : a = 1 := by
      have hh : (a - 1) * (a - 1) = 0 := by
        linear_combination hdet0 + (1 - a) * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp hh)
    have hB : B = sl2Upper b := by
      apply Subtype.ext
      change (B : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1]
      rw [hmat, hda, hc, ha]
    have hcomm : Commute (sl2Upper (1 : F)) B := by
      rw [hB]
      change sl2Upper (1 : F) * sl2Upper b = sl2Upper b * sl2Upper 1
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      change !![(1 : F), 1; 0, 1] * !![1, b; 0, 1] =
        !![1, b; 0, 1] * !![1, 1; 0, 1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, sl2Upper, Matrix.mul_apply,
          Fin.sum_univ_two, add_comm]
    have hX2 : (sl2Upper (1 : F) * B) ^ 2 = 1 := by
      rw [hcomm.mul_pow, upper_sq, hB2, one_mul]
    have hX1 : sl2Upper (1 : F) * B = 1 := by
      have hh := hCube
      rw [pow_succ, hX2, one_mul] at hh
      exact hh
    apply hBne
    calc B = sl2Upper 1 * (sl2Upper 1 * B) := by
          rw [← mul_assoc, ← pow_two, upper_sq, one_mul]
         _ = sl2Upper 1 := by rw [hX1, mul_one]
  have hCube' : (sl2Upper (1 : F) * B) * (sl2Upper 1 * B) * (sl2Upper 1 * B) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using hCube
  have hX3 := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hCube'
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hX3
  have hc3 : c * c * c + c = 0 := by
    have hh := congrFun (congrFun hX3 1) 0
    simp [hmat, sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, hda] at hh
    linear_combination hh - c * hdet - (a * a * c + 2 * a * c * c) * h2
  have hcEq : c = 1 := by
    have hf : c * (c * c + 1) = 0 := by linear_combination hc3
    have hs : c * c + 1 = 0 := (mul_eq_zero.mp hf).resolve_left hcne
    have hz : (c - 1) * (c - 1) = 0 := by
      linear_combination hs - c * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hz)
  have hb : b = a * a + 1 := by
    rw [hcEq, mul_one] at hdet
    linear_combination hdet - (a * a) * h2
  refine ⟨a + 1, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (B : Matrix (Fin 2) (Fin 2) F) * !![1, a + 1; 0, 1] =
    !![1, a + 1; 0, 1] * !![1, 0; 1, 1]
  rw [hmat, hda, hcEq, hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first
    | linear_combination h2
    | linear_combination -h2
    | linear_combination (a * a) * h2
    | linear_combination -(a * a) * h2
    | linear_combination a * h2
    | linear_combination -a * h2
    | ring

theorem exists_conj_involution_pair
    (hsq : ∀ a : F, ∃ b : F, b * b = a)
    {A B : SL(2, F)} (hA2 : A ^ 2 = 1) (hAne : A ≠ 1)
    (hB2 : B ^ 2 = 1) (hBne : B ≠ A) (hCube : (A * B) ^ 3 = 1) :
    ∃ g : SL(2, F), g⁻¹ * A * g = sl2Upper 1 ∧ g⁻¹ * B * g = sl2Lower 1 := by
  have hU2 : sl2Upper (1 : F) * sl2Upper 1 = 1 := by
    simpa only [pow_two] using upper_sq (1 : F)
  have hUne : sl2Upper (1 : F) ≠ 1 := by
    intro h
    have hh := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa [sl2Upper] using hh
  obtain ⟨g, hg⟩ := CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.SL2.sl2_involutions_conj
    CharTwo.two_eq_zero hsq (by simpa only [pow_two] using hA2) hAne hU2 hUne
  let e : MulAut (SL(2, F)) := MulAut.conj g⁻¹
  have hAe : e A = sl2Upper 1 := by simpa [e, MulAut.conj_apply] using hg
  have hBe2 : e B ^ 2 = 1 := by rw [← map_pow, hB2, map_one]
  have hBene : e B ≠ sl2Upper 1 := by
    intro h
    exact hBne (e.injective (h.trans hAe.symm))
  have hBecube : (sl2Upper (1 : F) * e B) ^ 3 = 1 := by
    rw [← hAe, ← map_mul, ← map_pow, hCube, map_one]
  obtain ⟨t, ht⟩ := lower_form_of_involution_pair hBe2 hBene hBecube
  have hcomm : Commute (sl2Upper (1 : F)) (sl2Upper t) := by
    change sl2Upper (1 : F) * sl2Upper t = sl2Upper t * sl2Upper 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    change !![(1 : F), 1; 0, 1] * !![1, t; 0, 1] =
      !![1, t; 0, 1] * !![1, 1; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, sl2Upper, Matrix.mul_apply,
        Fin.sum_univ_two, add_comm]
  refine ⟨g * sl2Upper t, ?_, ?_⟩
  · calc
      (g * sl2Upper t)⁻¹ * A * (g * sl2Upper t) =
          (sl2Upper t)⁻¹ * (g⁻¹ * A * g) * sl2Upper t := by group
      _ = (sl2Upper t)⁻¹ * sl2Upper 1 * sl2Upper t := by rw [hg]
      _ = sl2Upper 1 := by rw [mul_assoc, hcomm.eq]; group
  · calc
      (g * sl2Upper t)⁻¹ * B * (g * sl2Upper t) =
          (sl2Upper t)⁻¹ * (e B * sl2Upper t) := by
            simp only [e, MulAut.conj_apply]
            group
      _ = (sl2Upper t)⁻¹ * (sl2Upper t * sl2Lower 1) := by rw [ht]
      _ = sl2Lower 1 := by group

theorem exists_corrector_of_normalizes_range
    {G : Type} [Group G] (phi : SL(2, F) →* G) (hinj : Function.Injective phi)
    (hsq : ∀ a : F, ∃ b : F, b * b = a)
    {n : G} (hn : n ∈ Subgroup.normalizer (phi.range : Set G)) :
    ∃ g : SL(2, F), Commute ((phi g)⁻¹ * n) (phi (sl2Upper 1)) ∧
      Commute ((phi g)⁻¹ * n) (phi (sl2Lower 1)) := by
  let e : SL(2, F) ≃* phi.range := MonoidHom.ofInjective hinj
  let a : MulAut phi.range := phi.range.normalizerMonoidHom ⟨n, hn⟩
  let s : MulAut SL(2, F) := e.trans (a.trans e.symm)
  have he (X : SL(2, F)) : ((e X : phi.range) : G) = phi X :=
    MonoidHom.ofInjective_apply hinj
  have hs (X : SL(2, F)) : e (s X) = a (e X) := by
    change e (e.symm (a (e X))) = a (e X)
    exact e.apply_symm_apply _
  have haction (X : SL(2, F)) : phi (s X) = n * phi X * n⁻¹ := by
    calc
      phi (s X) = ((e (s X) : phi.range) : G) := (he _).symm
      _ = ((a (e X) : phi.range) : G) := congrArg Subtype.val (hs X)
      _ = n * ((e X : phi.range) : G) * n⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
      _ = n * phi X * n⁻¹ := by rw [he]
  have hUne : sl2Upper (1 : F) ≠ 1 := by
    intro h
    have hh := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa [sl2Upper] using hh
  have hVne : sl2Lower (1 : F) ≠ sl2Upper 1 := by
    intro h
    have hh := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa [sl2Lower, sl2Upper] using hh
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hV2 : sl2Lower (1 : F) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.two_eq_zero]
    all_goals exact h2
  have hUV3 : (sl2Upper (1 : F) * sl2Lower 1) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sl2Upper, sl2Lower, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        CharTwo.two_eq_zero]
    all_goals first
      | linear_combination 6 * h2
      | linear_combination 4 * h2
      | linear_combination 2 * h2
  have hX2 : s (sl2Upper (1 : F)) ^ 2 = 1 := by
    rw [← map_pow, upper_sq, map_one]
  have hXne : s (sl2Upper (1 : F)) ≠ 1 := by
    intro h
    exact hUne (s.injective (h.trans s.map_one.symm))
  have hY2 : s (sl2Lower (1 : F)) ^ 2 = 1 := by rw [← map_pow, hV2, map_one]
  have hYne : s (sl2Lower (1 : F)) ≠ s (sl2Upper 1) := fun h => hVne (s.injective h)
  have hXY3 : (s (sl2Upper (1 : F)) * s (sl2Lower 1)) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, hUV3, map_one]
  obtain ⟨g, hgU, hgV⟩ := exists_conj_involution_pair hsq hX2 hXne hY2 hYne hXY3
  have hcomm (T : SL(2, F)) (ht : g⁻¹ * s T * g = T) :
      Commute ((phi g)⁻¹ * n) (phi T) := by
    have h := congrArg phi ht
    rw [map_mul, map_mul, map_inv, haction] at h
    let k : G := (phi g)⁻¹ * n
    change k * phi T = phi T * k
    calc
      k * phi T = ((phi g)⁻¹ * (n * phi T * n⁻¹) * phi g) * k := by dsimp [k]; group
      _ = phi T * k := by rw [h]
  exact ⟨g, hcomm _ hgU, hcomm _ hgV⟩

end CFSG.LinearGroups.SL2
