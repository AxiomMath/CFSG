module

public import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {α : Type*} [Fintype α]

theorem classFunInner_eq_cfInner (f h : α → ℂ) :
    CauchySchwarzProjection.classFunInner f h = cfInner f h := by
  rw [CauchySchwarzProjection.classFunInner_apply, cfInner_def, Nat.card_eq_fintype_card]

theorem sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → α → ℂ} (hv : ∀ i j, cfInner (v i) (v j) = if i = j then 1 else 0) (f : α → ℂ) :
    ∑ i, ‖cfInner f (v i)‖ ^ 2 ≤ (cfInner f f).re := by
  have hv' : ∀ i j, CauchySchwarzProjection.classFunInner (v i) (v j) = if i = j then 1 else 0 :=
    fun i j => by rw [classFunInner_eq_cfInner]; exact hv i j
  have h := CauchySchwarzProjection.classFunInner_self_eq_add_of_inner_eq hv' f
    (fun i => cfInner f (v i)) (fun i => classFunInner_eq_cfInner _ _)
  rw [classFunInner_eq_cfInner] at h
  have hnn := CauchySchwarzProjection.classFunInner_self_re_nonneg
    (f - ∑ i, cfInner f (v i) • v i)
  have hre := congrArg Complex.re h
  rw [Complex.add_re] at hre
  have hcast : (∑ i, cfInner f (v i) * conj (cfInner f (v i))).re
      = ∑ i, ‖cfInner f (v i)‖ ^ 2 := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.mul_conj']; norm_cast
  rw [hcast] at hre
  linarith

theorem sum_norm_sq_cfInner_le_re {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → α → ℂ}
    (hv : IsOrthonormalFamily v) (f : α → ℂ) :
    ∑ i, ‖cfInner f (v i)‖ ^ 2 ≤ (cfInner f f).re :=
  sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hv.cfInner_eq_ite f

theorem cfInner_conj_right_of_real {f h : α → ℂ} (hf : ∀ x, conj (f x) = f x) :
    cfInner f (fun x => conj (h x)) = conj (cfInner f h) := by
  simp only [cfInner_def, map_mul, map_sum, map_inv₀, Complex.conj_natCast, Complex.conj_conj]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [hf x]

theorem cfInner_one_one [Nonempty α] : cfInner (1 : α → ℂ) (1 : α → ℂ) = 1 := by
  simp [cfInner_def, Finset.card_univ, Nat.card_eq_fintype_card]

variable {G : Type*} [Group G]

theorem mem_span_Irr_of_mem_signedIrr {f : G → ℂ} (hf : f ∈ signedIrr G) :
    f ∈ Submodule.span ℤ (Irr G) := by
  rcases mem_signedIrr.1 hf with h | h
  · exact Submodule.subset_span h
  · simpa using (Submodule.span ℤ (Irr G)).neg_mem (Submodule.subset_span (R := ℤ) h)

theorem sum_norm_sq_cfInner_le_of_real_bridge [Fintype G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ Γ : G → ℂ} {r : ℝ} {v : ι → G → ℂ}
    (hθ : θ ∈ signedIrr G) (hθnr : θ ≠ fun x => conj (θ x))
    (hθ1 : cfInner θ (1 : G → ℂ) = 0)
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ x, conj (Γ x) = Γ x)
    (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
    (_hr : 0 ≤ r)
    (hB : cfInner (1 - θ + Γ) (1 - θ + Γ) = (r : ℂ) + 2)
    (hv : IsOrthonormalFamily v) (_hvmem : ∀ i, v i ∈ classFun G)
    (hvθ : ∀ i, IsOrthogonal (v i) θ)
    (hvθbar : ∀ i, IsOrthogonal (v i) (fun x => conj (θ x))) :
    ∑ i, ‖cfInner Γ (v i)‖ ^ 2 ≤ r := by
  classical
  set θ' : G → ℂ := fun x => conj (θ x) with hθ'def
  have hθ'mem : θ' ∈ signedIrr G := conj_mem_signedIrr hθ
  have hθθ' : cfInner θ θ' = 0 := cfInner_conj_eq_zero_of_ne hθ hθnr
  have hθ'θ : cfInner θ' θ = 0 := by rw [← conj_cfInner, hθθ', map_zero]
  have hθθ : cfInner θ θ = 1 := cfInner_self_of_mem_signedIrr hθ
  have hθ'θ' : cfInner θ' θ' = 1 := cfInner_self_of_mem_signedIrr hθ'mem
  have hvθ' : ∀ i, cfInner (v i) θ = 0 := fun i => isOrthogonal_iff.1 (hvθ i)
  have hvθb' : ∀ i, cfInner (v i) θ' = 0 := fun i => isOrthogonal_iff.1 (hvθbar i)
  have hθv : ∀ i, cfInner θ (v i) = 0 := fun i => by rw [← conj_cfInner, hvθ' i, map_zero]
  have hθ'v : ∀ i, cfInner θ' (v i) = 0 := fun i => by rw [← conj_cfInner, hvθb' i, map_zero]
  obtain ⟨a, ha⟩ := exists_int_cfInner_of_mem_span_Irr hΓ (mem_span_Irr_of_mem_signedIrr hθ)
  have haθ' : cfInner Γ θ' = (a : ℂ) := by
    rw [hθ'def, cfInner_conj_right_of_real hΓreal, ha]; simp
  have hθΓ : cfInner θ Γ = (a : ℂ) := by rw [← conj_cfInner, ha]; simp
  have h1θ : cfInner (1 : G → ℂ) θ = 0 := by rw [← conj_cfInner, hθ1, map_zero]
  have h1Γ : cfInner (1 : G → ℂ) Γ = 0 := by rw [← conj_cfInner, hΓ1, map_zero]
  simp only [cfInner_add_left, cfInner_sub_left, cfInner_add_right, cfInner_sub_right,
    cfInner_one_one, h1θ, h1Γ, hθ1, hθθ, hθΓ, hΓ1, ha] at hB
  have hΓΓ : cfInner Γ Γ = (r : ℂ) + 2 * a := by linear_combination hB
  have hsub : cfInner (Γ - θ) (Γ - θ) = (r : ℂ) + 1 := by
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hΓΓ, ha, hθΓ, hθθ]; ring
  set w : ι ⊕ Bool → G → ℂ := Sum.elim v (fun b => bif b then θ else θ') with hwdef
  have hw : ∀ j j', cfInner (w j) (w j') = if j = j' then 1 else 0 := by
    intro j j'
    match j, j' with
    | Sum.inl i, Sum.inl i' => simpa [hwdef] using hv.cfInner_eq_ite i i'
    | Sum.inl i, Sum.inr b => cases b <;> simp [hwdef, hvθ' i, hvθb' i]
    | Sum.inr b, Sum.inl i => cases b <;> simp [hwdef, hθv i, hθ'v i]
    | Sum.inr b, Sum.inr b' => cases b <;> cases b' <;> simp [hwdef, hθθ, hθ'θ', hθθ', hθ'θ]
  have hbessel := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hw (Γ - θ)
  rw [hsub] at hbessel
  have hsplit : ∑ j, ‖cfInner (Γ - θ) (w j)‖ ^ 2
      = (∑ i, ‖cfInner Γ (v i)‖ ^ 2) + (‖cfInner (Γ - θ) θ‖ ^ 2 + ‖cfInner (Γ - θ) θ'‖ ^ 2) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by simp [hwdef, cfInner_sub_left, hθv i]
    · rw [Fintype.sum_bool]; simp [hwdef]
  have hθterm : cfInner (Γ - θ) θ = ((a - 1 : ℤ) : ℂ) := by
    rw [cfInner_sub_left, ha, hθθ]; push_cast; ring
  have hθ'term : cfInner (Γ - θ) θ' = ((a : ℤ) : ℂ) := by
    rw [cfInner_sub_left, haθ', hθθ', sub_zero]
  rw [hsplit, hθterm, hθ'term, Complex.norm_intCast, Complex.norm_intCast] at hbessel
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at hbessel
  have hn1 : |((a - 1 : ℤ) : ℝ)| ^ 2 = ((a : ℝ) - 1) ^ 2 := by rw [sq_abs]; push_cast; ring
  have hn2 : |((a : ℤ) : ℝ)| ^ 2 = (a : ℝ) ^ 2 := by rw [sq_abs]
  rw [hn1, hn2] at hbessel
  have hint : (0 : ℤ) ≤ a * (a - 1) := by
    rcases le_or_gt 1 a with h | h
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hintR : (0 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 1) := by
    have h := (Int.cast_le (R := ℝ)).2 hint
    push_cast at h
    linarith
  have hkey : ((a : ℝ) - 1) ^ 2 + (a : ℝ) ^ 2 = 1 + 2 * ((a : ℝ) * ((a : ℝ) - 1)) := by ring
  rw [hkey] at hbessel
  linarith

end CFSG.FeitThompson
