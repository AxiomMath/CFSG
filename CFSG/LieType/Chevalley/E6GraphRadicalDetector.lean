module

public import CFSG.LieType.Chevalley.E6GraphInvolutionForms

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphInvolution
open Matrix

variable {E : Type} [Field E]

theorem simpleRootSL2_injective_of_two
    {τ : Tag} (h2 : (2 : E) = 0) (i : Fin τ.rank) :
    Function.Injective (simpleRootSL2 τ E i) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  obtain ⟨l, hl, hBl⟩ := (exceptional_ordinary_rank_one_central_image τ E i).choose_spec.2.2.2.2.2.1
    B (MonoidHom.mem_ker.2 hB)
  have hl1 : (l : E) = 1 := eq_one_of_mul_self_eq_one_of_two_eq_zero h2 (by rw [← sq]; exact hl)
  refine Subtype.ext ?_
  rw [hBl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem trace_sq_of_two (h2 : (2 : E) = 0) (M : SL2 E) :
    ((M ^ 2 : SL2 E) : Matrix (Fin 2) (Fin 2) E).trace =
      ((M : Matrix (Fin 2) (Fin 2) E).trace) ^ 2 := by
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.SpecialLinearGroup.coe_pow, sq, sq, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-2 : E) * hdet - h2

theorem trace_pow_two_pow (h2 : (2 : E) = 0) (M : SL2 E) (n : ℕ) :
    ((M ^ 2 ^ n : SL2 E) : Matrix (Fin 2) (Fin 2) E).trace =
      ((M : Matrix (Fin 2) (Fin 2) E).trace) ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, trace_sq_of_two h2, ih, ← pow_mul, ← pow_succ]

theorem pow_two_pow_ne_one_of_trace (h2 : (2 : E) = 0) {M : SL2 E}
    (hM : (M : Matrix (Fin 2) (Fin 2) E).trace ≠ 0) (n : ℕ) : M ^ 2 ^ n ≠ 1 := by
  intro h
  have := trace_pow_two_pow h2 M n
  rw [h, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one, Fintype.card_fin] at this
  push_cast at this
  rw [h2] at this
  exact hM (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 this.symm)

theorem trace_detectorSL2 (h2 : (2 : E) = 0) (c : E) :
    ((vSL 1 * (uSL c * vSL 1 * (uSL c)⁻¹) : SL2 E) : Matrix (Fin 2) (Fin 2) E).trace = c ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.trace_fin_two]
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  linear_combination (1 - c ^ 2) * h2

theorem detector_pow_ne_one
    (h2 : (2 : E) = 0) {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1}) {c : E} (hc : c ≠ 0) (n : ℕ) :
    (yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
        (q * xUnit TwistTag.E6.tag E (e6Idx 1) c * yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
          (q * xUnit TwistTag.E6.tag E (e6Idx 1) c)⁻¹)) ^ 2 ^ n ≠ 1 := by
  have hJ : e6Idx 1 ∈ ({e6Idx 1} : Set (Fin TwistTag.E6.tag.rank)) := rfl
  set y := yUnit TwistTag.E6.tag E (e6Idx 1) 1 with hy
  set x := xUnit TwistTag.E6.tag E (e6Idx 1) c with hx
  have hyM : y ∈ parabolicLevi TwistTag.E6.tag E {e6Idx 1} := yUnit_mem_parabolicLevi hJ 1
  have hxM : x ∈ parabolicLevi TwistTag.E6.tag E {e6Idx 1} := xUnit_mem_parabolicLevi hJ c
  have hMN : parabolicLevi TwistTag.E6.tag E {e6Idx 1} ≤ Subgroup.normalizer
      (parabolicRadical TwistTag.E6.tag E {e6Idx 1} : Set (ModGL TwistTag.E6.tag E)) :=
    (parabolicLevi_le_parabolicSubgroup _).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical _)
  set m := y * (x * y * x⁻¹) with hm
  have hmM : m ∈ parabolicLevi TwistTag.E6.tag E {e6Idx 1} :=
    mul_mem hyM (mul_mem (mul_mem hxM hyM) (inv_mem hxM))
  have hconj : ∀ g ∈ parabolicLevi TwistTag.E6.tag E {e6Idx 1},
      ∀ u ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1},
        g * u * g⁻¹ ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1} := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.1 (hMN hg) u).1 hu
  have hq' : (y * q * y⁻¹) * (m * q⁻¹ * m⁻¹) ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1} :=
    mul_mem (hconj y hyM q hq) (hconj m hmM q⁻¹ (inv_mem hq))
  have hg : y * (q * x * y * (q * x)⁻¹) = (y * q * y⁻¹) * (m * q⁻¹ * m⁻¹) * m := by
    rw [hm]
    group
  intro hpow
  rw [hg] at hpow
  obtain ⟨q'', hq'', he⟩ := exists_mul_pow_eq_mul_pow hq' (hMN hmM) (2 ^ n)
  rw [he] at hpow
  have hmn : m ^ 2 ^ n ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1} ⊓
      parabolicLevi TwistTag.E6.tag E {e6Idx 1} := by
    refine Subgroup.mem_inf.2 ⟨?_, pow_mem hmM _⟩
    rw [eq_inv_of_mul_eq_one_right hpow]
    exact inv_mem hq''
  rw [(parabolic_root_radical_Levi_factors TwistTag.E6.tag E {e6Idx 1}).2.2.2.2.1,
    Subgroup.mem_bot] at hmn
  have hmφ : m = simpleRootSL2 TwistTag.E6.tag E (e6Idx 1)
      (vSL 1 * (uSL c * vSL 1 * (uSL c)⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv, simpleRootSL2_vSL, simpleRootSL2_uSL]
  rw [hmφ, ← map_pow] at hmn
  refine pow_two_pow_ne_one_of_trace h2 (M := vSL 1 * (uSL c * vSL 1 * (uSL c)⁻¹)) ?_ n
    (simpleRootSL2_injective_of_two h2 _ (by rw [hmn, map_one]))
  rw [trace_detectorSL2 h2]
  exact pow_ne_zero 2 hc

theorem not_isPGroup_two_of_detector
    (h2 : (2 : E) = 0) {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1}) {c : E} (hc : c ≠ 0)
    (z : ModGL TwistTag.E6.tag E) {H : Subgroup (ModGL TwistTag.E6.tag E)}
    (h₁ : z⁻¹ * yUnit TwistTag.E6.tag E (e6Idx 1) 1 * z ∈ H)
    (h₂ : z⁻¹ * (q * xUnit TwistTag.E6.tag E (e6Idx 1) c * yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
      (q * xUnit TwistTag.E6.tag E (e6Idx 1) c)⁻¹) * z ∈ H) : ¬ IsPGroup 2 H := by
  set g := yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
    (q * xUnit TwistTag.E6.tag E (e6Idx 1) c * yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
      (q * xUnit TwistTag.E6.tag E (e6Idx 1) c)⁻¹) with hgdef
  have hgH : z⁻¹ * g * z ∈ H := by
    have := mul_mem h₁ h₂
    rwa [show z⁻¹ * yUnit TwistTag.E6.tag E (e6Idx 1) 1 * z *
        (z⁻¹ * (q * xUnit TwistTag.E6.tag E (e6Idx 1) c * yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
          (q * xUnit TwistTag.E6.tag E (e6Idx 1) c)⁻¹) * z) = z⁻¹ * g * z by rw [hgdef]; group]
      at this
  intro hP
  obtain ⟨n, hn⟩ := hP ⟨_, hgH⟩
  have hn' : (z⁻¹ * g * z) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hconjpow : (z⁻¹ * g * z) ^ 2 ^ n = z⁻¹ * g ^ 2 ^ n * z := by
    rw [show z⁻¹ * g * z = z⁻¹ * g * z⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  rw [hconjpow] at hn'
  apply detector_pow_ne_one h2 hq hc n
  calc g ^ 2 ^ n = z * (z⁻¹ * g ^ 2 ^ n * z) * z⁻¹ := by group
    _ = 1 := by rw [hn']; group

end CFSG.LieType.Chevalley.E6GraphRadical
