module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionCorner

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne
  rootElt_add rootElt_zero)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {K : Type} [Field K] {n : ℕ}

theorem conjAut_mul_conjAut_mul_dualAut_mul_inv (H C : GL (Fin n) K) :
    conjAut n K H * (conjAut n K C * dualAut n K) * (conjAut n K H)⁻¹ =
      conjAut n K (H * C * GeneralLinearGroup.inverseTranspose H⁻¹) * dualAut n K := by
  rw [← map_inv, mul_assoc, mul_assoc, dualAut_mul_conjAut, map_mul, map_mul]
  group

theorem coe_mul_mul_inverseTranspose_inv (H C : GL (Fin n) K) :
    ((H * C * GeneralLinearGroup.inverseTranspose H⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      (H : Matrix (Fin n) (Fin n) K) * C * (H : Matrix (Fin n) (Fin n) K)ᵀ := by
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, inv_inv]

section Corner

variable [CharP K 2]

theorem slConjugation_fusionSwap_transpose (g : SpecialLinearGroup (Fin 2) K) :
    slConjugation 2 K (SpecialLinearGroup.toGL fusionSwap) (g⁻¹).transpose = g := by
  have hww : (fusionSwap : SpecialLinearGroup (Fin 2) K) * fusionSwap = 1 := by
    apply Subtype.ext
    change !![0, 1; 1, 0] * !![0, 1; 1, 0] = (1 : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hinv : (SpecialLinearGroup.toGL (fusionSwap : SpecialLinearGroup (Fin 2) K))⁻¹ =
      SpecialLinearGroup.toGL fusionSwap := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right hww]
  apply Subtype.ext
  rw [coe_slConjugation, hinv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two,
    coe_fusionSwap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [CharTwo.neg_eq]

omit [CharP K 2] in
theorem cornerSL_slConjugation {k : ℕ} (hk : k ≤ n) (A : GL (Fin k) K)
    (g : SpecialLinearGroup (Fin k) K) :
    cornerSL hk (slConjugation k K A g) = slConjugation n K (cornerGL hk A) (cornerSL hk g) := by
  apply Subtype.ext
  change cornerMat hk _ = _
  rw [coe_slConjugation, coe_slConjugation, ← map_inv, coe_cornerGL, coe_cornerGL, coe_cornerSL,
    ← cornerMat_mul, ← cornerMat_mul]

omit [CharP K 2] in
theorem toGL_cornerSL {k : ℕ} (hk : k ≤ n) (g : SpecialLinearGroup (Fin k) K) :
    SpecialLinearGroup.toGL (cornerSL hk g) = cornerGL hk (SpecialLinearGroup.toGL g) :=
  Units.ext rfl

theorem coe_cornerSL_fusionSwap_three :
    ((cornerSL (show 2 ≤ 3 by norm_num) (fusionSwap : SpecialLinearGroup (Fin 2) K) :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [coe_cornerSL, coe_fusionSwap]
  ext i j
  rw [cornerMat_apply]
  fin_cases i <;> fin_cases j <;> simp

omit [CharP K 2] in
theorem coe_cornerSL_fusionUpper_three :
    ((cornerSL (show 2 ≤ 3 by norm_num) (fusionUpper 1 : SpecialLinearGroup (Fin 2) K) :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  rw [coe_cornerSL, coe_fusionUpper]
  ext i j
  rw [cornerMat_apply]
  fin_cases i <;> fin_cases j <;> simp

@[expose] def fusionM3 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 1, 1], by simp [det_fin_three]⟩

@[expose] def fusionN3 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 1; 0, 1, 0; 0, 1, 1], by simp [det_fin_three]⟩

@[expose] def fusionH3 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 1; 1, 1, 1], by
    simp [det_fin_three]⟩

theorem fusionM3_inv : (fusionM3 : SpecialLinearGroup (Fin 3) K)⁻¹ = fusionN3 := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change !![1, 0, 1; 0, 1, 0; 0, 1, 1] * !![1, 1, 1; 0, 1, 0; 0, 1, 1] =
    (1 : Matrix (Fin 3) (Fin 3) K)
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem slConjugation_fusionM3 :
    slConjugation 3 K (SpecialLinearGroup.toGL
        (cornerSL (show 2 ≤ 3 by norm_num) (fusionSwap : SpecialLinearGroup (Fin 2) K)))
      ((fusionM3 : SpecialLinearGroup (Fin 3) K)⁻¹).transpose *
      cornerSL (show 2 ≤ 3 by norm_num) (fusionUpper 1) = fusionM3 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hww : (cornerSL (show 2 ≤ 3 by norm_num) (fusionSwap : SpecialLinearGroup (Fin 2) K)) *
      cornerSL (show 2 ≤ 3 by norm_num) fusionSwap = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_cornerSL_fusionSwap_three,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hinv : (SpecialLinearGroup.toGL (cornerSL (show 2 ≤ 3 by norm_num)
      (fusionSwap : SpecialLinearGroup (Fin 2) K)))⁻¹ =
      SpecialLinearGroup.toGL (cornerSL (show 2 ≤ 3 by norm_num) fusionSwap) := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right hww]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, hinv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_cornerSL_fusionSwap_three,
    Matrix.SpecialLinearGroup.coe_transpose, fusionM3_inv, coe_cornerSL_fusionUpper_three]
  change !![0, 1, 0; 1, 0, 0; 0, 0, 1] *
      (!![1, 1, 1; 0, 1, 0; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ *
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] * !![1, 1, 0; 0, 1, 0; 0, 0, 1] = !![1, 0, 1; 0, 1, 0; 0, 1, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [h2]

theorem fusionH3_mul_transpose :
    ((fusionH3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((fusionH3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  change !![1, 1, 0; 0, 1, 1; 1, 1, 1] *
      (!![1, 1, 0; 0, 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h2]

end Corner

theorem commutator_range_eq_range_of_isPerfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (φ : G →* H) : ⁅φ.range, φ.range⁆ = φ.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact Group.IsPerfect.commutator_eq_top

theorem perfectTwistedFusionIn_conjAut_cornerSwap_mul_dualAut [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) (hn : 3 ≤ n) :
    PerfectTwistedFusionIn
      (conjAut n K (cornerGL hn (SpecialLinearGroup.toGL
        (cornerSL (show 2 ≤ 3 by norm_num) (fusionSwap : SpecialLinearGroup (Fin 2) K))))
        * dualAut n K) (IsInvolutionClass 1) := by
  set h23 : 2 ≤ 3 := by norm_num
  set w3 : SpecialLinearGroup (Fin 3) K := cornerSL h23 fusionSwap with hw3
  set β := conjAut n K (cornerGL hn (SpecialLinearGroup.toGL w3)) * dualAut n K with hβ
  have hβapply : ∀ g : SpecialLinearGroup (Fin 3) K, β (proj n K (cornerSL hn g)) =
      proj n K (cornerSL hn (slConjugation 3 K (SpecialLinearGroup.toGL w3) (g⁻¹).transpose)) :=
    fun g => by
      rw [hβ, MulAut.mul_apply, dualAut_proj_cornerSL, conjAut_cornerGL_proj_cornerSL]
  set φ : SpecialLinearGroup (Fin 2) K →* projectiveSL n K :=
    (proj n K).comp ((cornerSL hn).comp (cornerSL h23)) with hφ
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr hK4)
  have hfixP : ∀ p ∈ φ.range, β p = p := by
    rintro _ ⟨g, rfl⟩
    rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, hβapply, ← map_inv, cornerSL_transpose,
      hw3, toGL_cornerSL, ← cornerSL_slConjugation, slConjugation_fusionSwap_transpose]
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hU : cornerSL hn (cornerSL h23 (fusionUpper (1 : K))) = rootElt a b 1 := by
    rw [fusionUpper_eq_rootElt, cornerSL_rootElt h23 (by decide),
      cornerSL_rootElt hn (by simp)]
    rfl
  have hfus : (β (proj n K (cornerSL hn fusionM3)))⁻¹ * proj n K (cornerSL hn fusionM3) =
      proj n K (rootElt a b 1) := by
    rw [hβapply, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ← hU]
    congr 2
    rw [inv_mul_eq_iff_eq_mul]
    exact slConjugation_fusionM3.symm
  have hcl := isInvolutionClass_one_proj_rootElt (K := K) hab
  refine ⟨proj n K (cornerSL hn fusionM3), proj n K (rootElt a b 1), hcl.ne_one one_ne_zero, hfus,
    hcl, φ.range, commutator_range_eq_range_of_isPerfect φ, ⟨fusionUpper 1, ?_⟩, hfixP⟩
  rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, hU]

theorem perfectTwistedFusionIn_dualAut [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (hn : 3 ≤ n) : PerfectTwistedFusionIn (dualAut n K) (IsInvolutionClass 1) := by
  set H : GL (Fin n) K := cornerGL hn (SpecialLinearGroup.toGL fusionH3) with hH
  have hconj : conjAut n K H * dualAut n K * (conjAut n K H)⁻¹ =
      conjAut n K (cornerGL hn (SpecialLinearGroup.toGL
        (cornerSL (show 2 ≤ 3 by norm_num) (fusionSwap : SpecialLinearGroup (Fin 2) K)))) *
        dualAut n K := by
    have h1 := conjAut_mul_conjAut_mul_dualAut_mul_inv H 1
    have hd : conjAut n K 1 * dualAut n K = dualAut n K := by rw [map_one, one_mul]
    rw [hd] at h1
    rw [h1]
    congr 2
    apply Units.ext
    rw [coe_mul_mul_inverseTranspose_inv, Units.val_one, Matrix.mul_one, hH, coe_cornerGL,
      coe_cornerGL, cornerMat_transpose, ← cornerMat_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      fusionH3_mul_transpose, coe_cornerSL_fusionSwap_three]
  exact PerfectTwistedFusionIn.of_conj hconj (fun x hx => hx.conjAut_inv H)
    (perfectTwistedFusionIn_conjAut_cornerSwap_mul_dualAut hK4 hn)

theorem perfectTwistedFusionIn_conjAut_mul_dualAut_of_not_alt {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hα : (conjAut n K A * dualAut n K) ^ 2 = 1)
    (halt : ¬∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0) :
    PerfectTwistedFusionIn (conjAut n K A * dualAut n K) (IsInvolutionClass 1) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    have h4 : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms (by omega) hK hn A hα
  rcases hC with ⟨hC1, -⟩ | ⟨r, -, -, halt'⟩
  · have hC1' : C = 1 := Units.ext hC1
    refine PerfectTwistedFusionIn.of_conj (ψ := (conjAut n K H)⁻¹) (β := dualAut n K) ?_
      (fun x hx => ?_) (perfectTwistedFusionIn_dualAut hK4 hn)
    · rw [hH, hC1', map_one, one_mul]
      group
    · rw [inv_inv]
      exact hx.conjAut H
  · exact absurd halt' halt

end CFSG.SeitzReduction.LinearPilot
