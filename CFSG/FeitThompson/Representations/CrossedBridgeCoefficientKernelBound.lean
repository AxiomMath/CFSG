module

public import CFSG.FeitThompson.Representations.ProjectionCoefficientsDistinctFamilies
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.NormalInducedFamilyWeightedNorm
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CoherentBridgeProjection

open scoped ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)

section RealBridge

variable {G : Type*} [Group G] [Fintype G]

theorem sum_norm_sq_cfInner_le_of_real_bridge_of_forall_cfInner {ι : Type*} [Fintype ι]
    {θ Γ : G → ℂ} {r : ℝ} {v : ι → G → ℂ}
    (hθ : θ ∈ signedIrr G) (hθnr : θ ≠ fun x => conj (θ x))
    (hθ1 : cfInner θ (1 : G → ℂ) = 0)
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ x, conj (Γ x) = Γ x)
    (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
    (hB : cfInner (1 - θ + Γ) (1 - θ + Γ) = (r : ℂ) + 2)
    (hvone : ∀ i, cfInner (v i) (v i) = 1)
    (hvzero : ∀ i j, i ≠ j → cfInner (v i) (v j) = 0)
    (hvθ : ∀ i, cfInner (v i) θ = 0)
    (hvθbar : ∀ i, cfInner (v i) (fun x => conj (θ x)) = 0) :
    ∑ i, ‖cfInner Γ (v i)‖ ^ 2 ≤ r := by
  classical
  have hv : ∀ i j, cfInner (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hvone i]
    · simp [h, hvzero i j h]
  set θ' : G → ℂ := fun x => conj (θ x) with hθ'def
  have hθ'mem : θ' ∈ signedIrr G := conj_mem_signedIrr hθ
  have hθθ' : cfInner θ θ' = 0 := cfInner_conj_eq_zero_of_ne hθ hθnr
  have hθ'θ : cfInner θ' θ = 0 := by rw [← conj_cfInner, hθθ', map_zero]
  have hθθ : cfInner θ θ = 1 := cfInner_self_of_mem_signedIrr hθ
  have hθ'θ' : cfInner θ' θ' = 1 := cfInner_self_of_mem_signedIrr hθ'mem
  have hθv : ∀ i, cfInner θ (v i) = 0 := fun i => by rw [← conj_cfInner, hvθ i, map_zero]
  have hθ'v : ∀ i, cfInner θ' (v i) = 0 := fun i => by rw [← conj_cfInner, hvθbar i, map_zero]
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
    | Sum.inl i, Sum.inl i' => simpa [hwdef] using hv i i'
    | Sum.inl i, Sum.inr b => cases b <;> simp [hwdef, hvθ i, hvθbar i]
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

end RealBridge

section Main

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {ι : Type*} [Finite ι] {ξ : ι → (L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G}
  {θ Γ B : G → ℂ} {r : ℝ}

theorem range_subset_indFam {H : Subgroup L} (hS : Set.range ξ = indFam H (Irr H \ {1})) :
    Set.range ξ ⊆ indFam H (Irr H) := hS ▸ indFam_mono H Set.sdiff_subset

theorem coherentImage_mem_span_Irr (k : ι) :
    coherentImage ξ ν k ∈ Submodule.span ℤ (Irr G) := by
  rw [coherentImage_apply]
  exact virtualChars_le_span_Irr (ν _).2

theorem norm_sq_cfInner_bridge_mul_le (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hIrr : ∀ k, ξ k ∈ Irr L) (hν : IsCoherentWith (Set.range ξ) τ ν)
    {k₀ : ι} (hζ : ξ k₀ 1 = (H.index : ℂ))
    (hθ : θ ∈ signedIrr G) (hθnr : θ ≠ fun x => conj (θ x))
    (hθ1 : IsOrthogonal θ (1 : G → ℂ))
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ x, conj (Γ x) = Γ x)
    (hΓ1 : IsOrthogonal Γ (1 : G → ℂ))
    (hBdef : B = 1 - θ + Γ) (hBnorm : cfInner B B = (r : ℂ) + 2)
    (hBτ : ∀ f : charSpanZero (Set.range ξ), cfInner B (τ f : G → ℂ) = 0)
    (hν1 : ∀ k, IsOrthogonal (coherentImage ξ ν k) (1 : G → ℂ))
    (hνθ : ∀ k, IsOrthogonal (coherentImage ξ ν k) θ)
    (hνθbar : ∀ k, IsOrthogonal (coherentImage ξ ν k) (fun x => conj (θ x))) :
    ‖cfInner B (coherentImage ξ ν k₀)‖ ^ 2 * (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) ≤ r := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  subst hBdef
  have hξS : Set.range ξ ⊆ indFam H (Irr H) := range_subset_indFam hS
  choose m hm0 hmdvd hmeq using fun k =>
    NormalInducedFamily.exists_apply_one_eq_of_mem_indFam H (hξS ⟨k, rfl⟩)
  have hidxR : (H.index : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have hcast : ∀ k, ξ k 1 / (H.index : ℂ) = (((m k : ℝ) / (H.index : ℝ) : ℝ) : ℂ) := by
    intro k
    rw [hmeq k]
    push_cast
    ring
  have hBη : ∀ k, cfInner (1 - θ + Γ) (coherentImage ξ ν k)
      = (((m k : ℝ) / (H.index : ℝ) : ℝ) : ℂ)
        * cfInner (1 - θ + Γ) (coherentImage ξ ν k₀) := fun k => by
    rw [CrossFamilyProjection.cfInner_coherentImage_eq H hξS hν hBτ hζ k, hcast k]
  have hΓη : ∀ k, cfInner Γ (coherentImage ξ ν k)
      = (((m k : ℝ) / (H.index : ℝ) : ℝ) : ℂ)
        * cfInner (1 - θ + Γ) (coherentImage ξ ν k₀) := by
    intro k
    have h1 : cfInner (1 : G → ℂ) (coherentImage ξ ν k) = 0 := by
      rw [← conj_cfInner, isOrthogonal_iff.1 (hν1 k), map_zero]
    have hθc : cfInner θ (coherentImage ξ ν k) = 0 := by
      rw [← conj_cfInner, isOrthogonal_iff.1 (hνθ k), map_zero]
    have hh := hBη k
    rw [cfInner_add_left, cfInner_sub_left, h1, hθc] at hh
    simpa using hh
  have hbound := sum_norm_sq_cfInner_le_of_real_bridge_of_forall_cfInner
    (v := coherentImage ξ ν) hθ hθnr (isOrthogonal_iff.1 hθ1) hΓ hΓreal
    (isOrthogonal_iff.1 hΓ1) hBnorm
    (fun k => by
      simpa using CrossFamilyProjection.cfInner_coherentImage_coherentImage hinj hIrr hν k k)
    (fun k l hkl => by
      simpa [hkl] using
        CrossFamilyProjection.cfInner_coherentImage_coherentImage hinj hIrr hν k l)
    (fun k => isOrthogonal_iff.1 (hνθ k)) (fun k => isOrthogonal_iff.1 (hνθbar k))
  have hterm : ∀ k, ‖cfInner Γ (coherentImage ξ ν k)‖ ^ 2
      = ((m k : ℝ) / (H.index : ℝ)) ^ 2
        * ‖cfInner (1 - θ + Γ) (coherentImage ξ ν k₀)‖ ^ 2 := by
    intro k
    rw [hΓη k, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_mul] at hbound
  have hweight : ∑ k, ((m k : ℝ) / (H.index : ℝ)) ^ 2
      = ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
    have hC : ((∑ k, ((m k : ℝ) / (H.index : ℝ)) ^ 2 : ℝ) : ℂ)
        = ((((Nat.card H : ℝ) - 1) / (H.index : ℝ) : ℝ) : ℂ) := by
      push_cast
      rw [← NormalInducedWeightedNorm.sum_sq_div_cfInner H hinj hS]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [cfInner_self_of_mem_Irr (hIrr k), div_one, hmeq k]
    exact_mod_cast hC
  rw [hweight] at hbound
  rw [mul_comm]
  exact hbound

theorem div_le_of_cfInner_bridge_ne_zero (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hIrr : ∀ k, ξ k ∈ Irr L) (hν : IsCoherentWith (Set.range ξ) τ ν)
    {k₀ : ι} (hζ : ξ k₀ 1 = (H.index : ℂ))
    (hθ : θ ∈ signedIrr G) (hθnr : θ ≠ fun x => conj (θ x))
    (hθ1 : IsOrthogonal θ (1 : G → ℂ))
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ x, conj (Γ x) = Γ x)
    (hΓ1 : IsOrthogonal Γ (1 : G → ℂ))
    (hBdef : B = 1 - θ + Γ) (hBnorm : cfInner B B = (r : ℂ) + 2)
    (hBτ : ∀ f : charSpanZero (Set.range ξ), cfInner B (τ f : G → ℂ) = 0)
    (hν1 : ∀ k, IsOrthogonal (coherentImage ξ ν k) (1 : G → ℂ))
    (hνθ : ∀ k, IsOrthogonal (coherentImage ξ ν k) θ)
    (hνθbar : ∀ k, IsOrthogonal (coherentImage ξ ν k) (fun x => conj (θ x)))
    (hc : cfInner B (coherentImage ξ ν k₀) ≠ 0) :
    ((Nat.card H : ℝ) - 1) / (H.index : ℝ) ≤ r := by
  have hbound := norm_sq_cfInner_bridge_mul_le H hinj hS hIrr hν hζ hθ hθnr hθ1 hΓ hΓreal hΓ1
    hBdef hBnorm hBτ hν1 hνθ hνθbar
  have hBmem : B ∈ Submodule.span ℤ (Irr G) := by
    rw [hBdef]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.subset_span one_mem_Irr)
      (mem_span_Irr_of_mem_signedIrr hθ)) hΓ
  obtain ⟨n, hn⟩ := exists_int_cfInner_of_mem_span_Irr hBmem
    (coherentImage_mem_span_Irr (ξ := ξ) (ν := ν) k₀)
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    exact hc (by simpa using hn)
  have h1 : (1 : ℝ) ≤ ‖cfInner B (coherentImage ξ ν k₀)‖ ^ 2 := by
    rw [hn, Complex.norm_intCast, sq_abs]
    have hsq : (1 : ℤ) ≤ n ^ 2 := by
      rcases lt_or_gt_of_ne hn0 with h | h <;> nlinarith
    exact_mod_cast (Int.cast_le (R := ℝ)).2 hsq
  have hnonneg : (0 : ℝ) ≤ ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
    refine div_nonneg ?_ (by positivity)
    have h1H : (1 : ℝ) ≤ (Nat.card H : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    linarith
  nlinarith [hbound, h1, hnonneg]

end Main

end CoherentBridgeProjection

end CFSG.FeitThompson
