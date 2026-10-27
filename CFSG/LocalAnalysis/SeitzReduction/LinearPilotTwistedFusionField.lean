module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionCorner
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuter
public import CFSG.LocalAnalysis.SeitzReduction.Fusion

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne
  rootElt_add rootElt_zero)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField mem_fixedField)
open CFSG.RankThree.PartOne (linearSubfieldInclusion
  fixingSubgroup_range_linearSubfieldInclusion simple_nonabelian_range_linearSubfieldInclusion
  mem_range_linearSubfieldInclusion)
open CFSG.ComponentClassification.RankTwoHypIIY (commutator_eq_self_of_isSimpleGroup)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Assembly.LowTwoRank (StatedSU)

variable {K : Type} [Field K] {n : ℕ}

theorem specialLinearGroupMap_rootElt (σ : K →+* K) (i j : Fin n) (c : K) :
    SpecialLinearGroup.map σ (rootElt i j c) = rootElt i j (σ c) := by
  by_cases hij : i = j
  · subst hij
    rw [LinearCover.rootElt_self, LinearCover.rootElt_self, map_one]
  · apply Subtype.ext
    change (rootElt i j c : Matrix (Fin n) (Fin n) K).map σ = _
    rw [coe_rootElt_of_ne hij, coe_rootElt_of_ne hij]
    ext a b
    simp only [transvection, Matrix.map_apply, Matrix.add_apply, one_apply, single_apply,
      map_add, apply_ite σ, map_one, map_zero]

theorem rootElt_neg_eq_inv (i j : Fin n) (c : K) : rootElt i j (-c) = (rootElt i j c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootElt_add, neg_add_cancel, rootElt_zero]

theorem perfectTwistedFusionIn_fieldAut [Finite K] [CharP K 2] {e : ℕ}
    (hK : Nat.card K = (2 ^ e) ^ 2) (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2 ^ e) :
    PerfectTwistedFusionIn (fieldAut n K σ) (IsInvolutionClass 1) := by
  obtain ⟨c, hc⟩ := exists_add_pow_eq_of_pow_eq hK (d := (1 : K)) (one_pow _)
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hy : (fieldAut n K σ (proj n K (rootElt a b c)))⁻¹ * proj n K (rootElt a b c) =
      proj n K (rootElt a b 1) := by
    rw [fieldAut_proj, specialLinearGroupMap_rootElt, ← map_inv, ← map_mul, ← rootElt_neg_eq_inv,
      ← rootElt_add, CharTwo.neg_eq]
    congr 2
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, add_comm]
    exact hc
  have hcl := isInvolutionClass_one_proj_rootElt (K := K) hab
  have hk : ∀ x, x ∈ fixedField K σ ↔ σ x = x := fun x => mem_fixedField K σ x
  have hfix := fixingSubgroup_range_linearSubfieldInclusion hk hn
  obtain ⟨hsimple, hnc⟩ := simple_nonabelian_range_linearSubfieldInclusion (K := K) hn
    (fixedField K σ)
  have hσmem : fieldAut n K σ ∈ fixingSubgroup (MulAut (projectiveSL n K))
      ((linearSubfieldInclusion n (fixedField K σ)).range : Set (projectiveSL n K)) := by
    rw [hfix]
    exact mem_zpowers _
  refine ⟨proj n K (rootElt a b c), proj n K (rootElt a b 1), hcl.ne_one one_ne_zero, hy, hcl,
    (linearSubfieldInclusion n (fixedField K σ)).range,
    commutator_eq_self_of_isSimpleGroup hsimple hnc, ?_,
    fun p hp => (mem_fixingSubgroup_iff _).mp hσmem p hp⟩
  refine mem_range_linearSubfieldInclusion.mpr ⟨rootElt a b 1, fun i j => ?_, rfl⟩
  rw [coe_rootElt_of_ne hab]
  simp only [transvection, Matrix.add_apply, one_apply, single_apply]
  refine add_mem ?_ ?_ <;> split_ifs <;> simp

theorem perfectTwistedFusionIn_conjAut_mul_fieldAut [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    PerfectTwistedFusionIn (conjAut n K A * fieldAut n K σ) (IsInvolutionClass 1) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨⟨e, he⟩, hσx, H, hH⟩ := even_linear_field_involution_descent hf hK hn A σ hσ hα
  have hK' : Nat.card K = (2 ^ e) ^ 2 := by rw [hK, he, ← pow_mul, mul_two]
  have hσ' : ∀ x, σ x = x ^ 2 ^ e := fun x => by rw [hσx, show f / 2 = e by omega]
  refine PerfectTwistedFusionIn.of_conj (ψ := (conjAut n K H)⁻¹) (β := fieldAut n K σ) ?_
    (fun x hx => ?_) (perfectTwistedFusionIn_fieldAut hK' hn σ hσ')
  · rw [hH]
    group
  · rw [inv_inv]
    exact hx.conjAut H

theorem coe_fusionLower_mul_fusionUpper (b : K) :
    ((fusionLower 1 * fusionUpper b : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, b; 1, 1 + b] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_fusionLower, coe_fusionUpper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem fusionLower_mul_fusionUpper_eq [CharP K 2] (σ : K →+* K) {b : K} (hb : σ b = 1 + b) :
    fusionLower 1 * fusionUpper b =
      SpecialLinearGroup.map σ ((fusionLower 1 * fusionUpper b)⁻¹).transpose * fusionSwap := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  change ((fusionLower 1 * fusionUpper b : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) =
    (((fusionLower 1 * fusionUpper b)⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)ᵀ.map σ * !![0, 1; 1, 0]
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_fusionLower_mul_fusionUpper, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hb, ← add_assoc, h2]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hb, CharTwo.neg_eq]

theorem toGL_cornerSL_fusionSwap_mem_unitarySU [CharP K 2] {e : ℕ} (h : UnitaryFieldData 2 e K)
    (hk : 2 ≤ n) :
    SpecialLinearGroup.toGL (cornerSL hk (fusionSwap : SpecialLinearGroup (Fin 2) K)) ∈
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 e K n := by
  rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h]
  refine ⟨(cornerSL hk fusionSwap).2, ?_⟩
  change ((cornerMat hk !![0, 1; 1, 0]).map h.bar)ᵀ * cornerMat hk !![0, 1; 1, 0] = 1
  have hw : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map h.bar = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.map_apply] <;> simp
  have hww : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [cornerMat_map, hw, cornerMat_transpose, ← cornerMat_mul, hww, cornerMat_one]

theorem isInvolutionClass_one_proj_cornerSL_fusionSwap [CharP K 2] (hk : 2 ≤ n) :
    IsInvolutionClass 1 (proj n K (cornerSL hk (fusionSwap : SpecialLinearGroup (Fin 2) K))) := by
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hL : cornerSL hk (fusionLower (1 : K)) = rootElt b a 1 := by
    rw [fusionLower_eq_rootElt, cornerSL_rootElt hk (by decide)]
    rfl
  have hU : cornerSL hk (fusionUpper (1 : K)) = rootElt a b 1 := by
    rw [fusionUpper_eq_rootElt, cornerSL_rootElt hk (by decide)]
    rfl
  have hLinv : (rootElt b a (1 : K))⁻¹ = rootElt b a 1 := by
    rw [← rootElt_neg_eq_inv, CharTwo.neg_eq]
  have heq : proj n K (cornerSL hk (fusionSwap : SpecialLinearGroup (Fin 2) K)) =
      conjAut n K (SpecialLinearGroup.toGL (rootElt b a 1)) (proj n K (rootElt a b 1)) := by
    rw [conjAut_toGL, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hLinv, fusionSwap_eq,
      map_mul (cornerSL hk), map_mul (cornerSL hk), hL, hU]
  rw [heq]
  exact (isInvolutionClass_one_proj_rootElt hab).conjAut _

theorem perfectTwistedFusionIn_fieldAut_mul_dualAut {e : ℕ} (h : UnitaryFieldData 2 e K)
    (hn : 3 ≤ n) (hq : (n, 2 ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    PerfectTwistedFusionIn (fieldAut n K σ * dualAut n K) (IsInvolutionClass 1) := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hinn, -, hcent, -, -⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := n) hn σ hσ
  have hSU : Group.IsPerfect (StatedSU n (2 ^ e) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (by rw [h.card, ← pow_mul, mul_comm]) hn hq
  let eN := ι.symm.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := n) (by omega))
  have hperf : Group.IsPerfect
      ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 e K n).map (conjAut n K)) :=
    Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hK : Nat.card K = (2 ^ e) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨b, hb⟩ := exists_add_pow_eq_of_pow_eq hK (d := (1 : K)) (one_pow _)
  have hσb : (σ : K →+* K) b = 1 + b := by
    rw [RingHom.coe_coe, hσ, UnitaryFieldData.bar_apply, ← hb, add_comm b, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have hk : 2 ≤ n := by omega
  set g : SpecialLinearGroup (Fin 2) K := fusionLower 1 * fusionUpper b with hg
  have hy : ((fieldAut n K σ * dualAut n K) (proj n K (cornerSL hk g)))⁻¹ *
      proj n K (cornerSL hk g) = proj n K (cornerSL hk fusionSwap) := by
    rw [MulAut.mul_apply, dualAut_proj_cornerSL, fieldAut_proj_cornerSL, ← map_inv, ← map_mul,
      ← map_inv, ← map_mul]
    congr 2
    rw [inv_mul_eq_iff_eq_mul]
    exact fusionLower_mul_fusionUpper_eq (σ : K →+* K) hσb
  have hcl := isInvolutionClass_one_proj_cornerSL_fusionSwap (K := K) hk
  refine perfectTwistedFusionIn_of_inner (LinearOuter.conj_injective hn) hinn hcent
    (Subgroup.isPerfect_iff.mp hperf) (proj n K (cornerSL hk g)) ?_ ?_ ?_
  · rw [hy]
    exact hcl.ne_one one_ne_zero
  · rw [hy, ← conjAut_toGL]
    exact mem_map_of_mem _ (toGL_cornerSL_fusionSwap_mem_unitarySU h hk)
  · rw [hy]
    exact hcl

theorem perfectTwistedFusionIn_conjAut_mul_fieldAut_mul_dualAut [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hnf : ¬(n = 3 ∧ f = 2)) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    PerfectTwistedFusionIn (conjAut n K A * fieldAut n K σ * dualAut n K)
      (IsInvolutionClass 1) := by
  obtain ⟨⟨e, he⟩, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A σ hσ hα
  have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by
    rw [hσx, UnitaryFieldData.bar_apply, show f / 2 = e by omega]
  have hq : (n, 2 ^ e) ≠ (3, 2) := by
    intro hq
    have h1 := congrArg Prod.fst hq
    have h2 : 2 ^ e = 2 ^ 1 := by simpa using congrArg Prod.snd hq
    have := Nat.pow_right_injective le_rfl h2
    simp only at h1
    omega
  refine PerfectTwistedFusionIn.of_conj (ψ := (conjAut n K H)⁻¹)
    (β := fieldAut n K σ * dualAut n K) ?_ (fun x hx => ?_)
    (perfectTwistedFusionIn_fieldAut_mul_dualAut hud hn hq σ hσbar)
  · rw [hH]
    group
  · rw [inv_inv]
    exact hx.conjAut H

end CFSG.SeitzReduction.LinearPilot
