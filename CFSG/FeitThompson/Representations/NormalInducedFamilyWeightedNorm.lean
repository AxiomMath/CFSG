module

import CFSG.FeitThompson.Representations.RegularCharOrthogonalInducedBasis
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.ProjectionCoefficientsDistinctFamilies
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedWeightedNorm

open scoped ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)

section Eta
variable {L : Type*} [Group L]

theorem inertiaGroup_one (H : Subgroup L) [H.Normal] : inertiaGroup H (1 : H → ℂ) = ⊤ :=
  (Subgroup.eq_top_iff' _).2 fun t =>
    mem_inertiaGroup.2 (NormalInducedFamily.conjClassFun_one_right H t)

private theorem index_ne_zero {K : Type*} [Group K] [Finite K] (H : Subgroup K) :
    (H.index : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'

variable [Fintype L]

theorem indClassFun_one_apply_one (H : Subgroup L) :
    indClassFun H (1 : H → ℂ) 1 = (H.index : ℂ) := by
  rw [NormalInducedFamily.indClassFun_one_eq_index_mul]; simp

theorem cfInner_self_indClassFun_one (H : Subgroup L) [H.Normal] :
    cfInner (indClassFun H (1 : H → ℂ)) (indClassFun H (1 : H → ℂ)) = (H.index : ℂ) := by
  rw [cfInner_self_indClassFun H one_mem_Irr, inertiaGroup_one, Subgroup.relIndex_top_right]

end Eta

section Sum
variable {L : Type*} [Group L] [Fintype L] {ι : Type*} {ξ : ι → (L → ℂ)}

theorem mem_indFam_of_range_eq {H : Subgroup L} [H.Normal]
    (hS : Set.range ξ = indFam H (Irr H \ {1})) (k : ι) : ξ k ∈ indFam H (Irr H) := by
  have h : ξ k ∈ Set.range ξ := Set.mem_range_self k
  rw [hS, ← NormalInducedFamily.indFam_diff_singleton] at h
  exact h.1

theorem range_eq_sdiff {H : Subgroup L} [H.Normal] (hS : Set.range ξ = indFam H (Irr H \ {1})) :
    Set.range ξ = indFam H (Irr H) \ {indClassFun H (1 : H → ℂ)} := by
  rw [hS, NormalInducedFamily.indFam_diff_singleton]

theorem cfInner_self_ne_zero {H : Subgroup L} [H.Normal] {f : L → ℂ}
    (hf : f ∈ indFam H (Irr H)) : cfInner f f ≠ 0 := by
  obtain ⟨n, hn, hne⟩ := NormalInducedSupportBasis.exists_cfInner_self_eq_of_mem_indFam H hf
  rw [hne]
  exact_mod_cast hn.ne'

theorem conj_apply_one_div_cfInner {H : Subgroup L} [H.Normal] {e : ℂ} (he : conj e = e)
    {f : L → ℂ} (hf : f ∈ indFam H (Irr H)) :
    conj ((f 1 / e) / cfInner f f) = (f 1 / e) / cfInner f f := by
  obtain ⟨d, -, -, hd⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_indFam H hf
  obtain ⟨n, -, hn⟩ := NormalInducedSupportBasis.exists_cfInner_self_eq_of_mem_indFam H hf
  rw [hd, hn]
  simp [map_div₀, he]

variable [Fintype ι]

private theorem card_eq_index_add_sum (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1})) :
    (Nat.card L : ℂ) = (H.index : ℂ) + ∑ k, (ξ k 1) ^ 2 / cfInner (ξ k) (ξ k) := by
  classical
  have : Fintype (indFam H (Irr H)) := Fintype.ofFinite _
  set η : L → ℂ := indClassFun H (1 : H → ℂ) with hη
  set F : (L → ℂ) → ℂ := fun f => (f 1) ^ 2 / cfInner f f with hF
  have h := congrFun (leftRegular_character_eq_sum_indFam (L := L) H) 1
  rw [leftRegular_character_one, Finset.sum_apply] at h
  have h2 : (Nat.card L : ℂ) = ∑ f : indFam H (Irr H), F (f : L → ℂ) := by
    rw [h]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [hF, Pi.smul_apply, smul_eq_mul]
    ring
  have hSd : Set.range ξ = indFam H (Irr H) \ {η} := range_eq_sdiff hS
  have hTeq : indFam H (Irr H) = insert η (Set.range ξ) := by
    rw [hSd, Set.insert_sdiff_singleton,
      Set.insert_eq_self.2 (NormalInducedFamily.indClassFun_one_mem_indFam H)]
  have hnot : η ∉ Set.range ξ := by rw [hSd]; simp
  rw [h2, Finset.sum_set_coe (f := F), Set.toFinset_congr hTeq, Set.toFinset_insert,
    Finset.sum_insert (by simpa using hnot), Set.toFinset_range,
    Finset.sum_image fun a _ b _ h => hinj h]
  congr 1
  simp only [hF, hη, indClassFun_one_apply_one, cfInner_self_indClassFun_one]
  rw [sq, mul_div_assoc, div_self (index_ne_zero H), mul_one]

theorem sum_sq_div_cfInner (H : Subgroup L) [H.Normal] (hinj : Function.Injective ξ)
    (hS : Set.range ξ = indFam H (Irr H \ {1})) :
    ∑ k, (ξ k 1 / (H.index : ℂ)) ^ 2 / cfInner (ξ k) (ξ k)
      = ((Nat.card H : ℂ) - 1) / (H.index : ℂ) := by
  have he := index_ne_zero H
  have hcard : (Nat.card L : ℂ) = (H.index : ℂ) * (Nat.card H : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have key := card_eq_index_add_sum H hinj hS
  rw [hcard] at key
  have hsum : ∑ k, (ξ k 1) ^ 2 / cfInner (ξ k) (ξ k)
      = (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
    rw [mul_sub, mul_one]; linear_combination -key
  have hterm : ∀ k : ι, (ξ k 1 / (H.index : ℂ)) ^ 2 / cfInner (ξ k) (ξ k)
      = ((H.index : ℂ) ^ 2)⁻¹ * ((ξ k 1) ^ 2 / cfInner (ξ k) (ξ k)) := fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, hsum]
  field_simp

end Sum

section Q
variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {ι : Type*} [Fintype ι] {ξ : ι → (L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G}

noncomputable def weightedCoherentSum (ξ : ι → (L → ℂ))
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (e : ℂ) : G → ℂ :=
  ∑ k, ((ξ k 1 / e) / cfInner (ξ k) (ξ k)) • coherentImage ξ ν k

omit [Fintype G] in
theorem weightedCoherentSum_apply (e : ℂ) :
    weightedCoherentSum ξ ν e
      = ∑ k, ((ξ k 1 / e) / cfInner (ξ k) (ξ k)) • coherentImage ξ ν k := (rfl)

omit [Fintype G] in
theorem weightedCoherentSum_mem_span (e : ℂ) :
    weightedCoherentSum ξ ν e ∈ Submodule.span ℂ (Set.range (coherentImage ξ ν)) :=
  Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (CrossFamilyProjection.coherentImage_mem_span ξ ν k)

omit [Fintype ι] in
open scoped Classical in
theorem cfInner_coherentImage_eq_ite (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν) (k l : ι) :
    cfInner (coherentImage ξ ν k) (coherentImage ξ ν l)
      = if k = l then cfInner (ξ k) (ξ k) else 0 := by
  rw [coherentImage_apply, coherentImage_apply, hν.inner_eq]
  by_cases hkl : k = l
  · rw [if_pos hkl, hkl]
  · rw [if_neg hkl]
    exact NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H (mem_indFam_of_range_eq hS k)
      (mem_indFam_of_range_eq hS l) fun h => hkl (hinj h)

theorem cfInner_weightedCoherentSum_coherentImage (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν) (k₀ : ι) :
    cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) (coherentImage ξ ν k₀)
      = ξ k₀ 1 / (H.index : ℂ) := by
  classical
  rw [weightedCoherentSum_apply, cfInner_sum_left,
    Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ k₀)]
  · rw [cfInner_smul_left, cfInner_coherentImage_eq_ite H hinj hS hν, if_pos rfl,
      div_mul_cancel₀ _ (cfInner_self_ne_zero (mem_indFam_of_range_eq hS k₀))]
  · intro k _ hk
    rw [cfInner_smul_left, cfInner_coherentImage_eq_ite H hinj hS hν, if_neg hk, mul_zero]

theorem cfInner_weightedCoherentSum_coherentImage_of_apply_one_eq (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν) {k₀ : ι} (hζ : ξ k₀ 1 = (H.index : ℂ)) :
    cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) (coherentImage ξ ν k₀) = 1 := by
  rw [cfInner_weightedCoherentSum_coherentImage H hinj hS hν k₀, hζ, div_self (index_ne_zero H)]

theorem cfInner_self_weightedCoherentSum (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν) :
    cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) (weightedCoherentSum ξ ν (H.index : ℂ))
      = ((Nat.card H : ℂ) - 1) / (H.index : ℂ) := by
  classical
  set c : ι → ℂ := fun k => (ξ k 1 / (H.index : ℂ)) / cfInner (ξ k) (ξ k) with hc
  have hQ : weightedCoherentSum ξ ν (H.index : ℂ) = ∑ k, c k • coherentImage ξ ν k := rfl
  have hconj : ∀ k, conj (c k) = c k := fun k =>
    conj_apply_one_div_cfInner (by simp) (mem_indFam_of_range_eq hS k)
  rw [hQ, cfInner_sum_left]
  have hrow : ∀ k : ι, cfInner (c k • coherentImage ξ ν k) (∑ l, c l • coherentImage ξ ν l)
      = c k * (c k * cfInner (ξ k) (ξ k)) := by
    intro k
    rw [cfInner_sum_right, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · rw [cfInner_smul_left, cfInner_smul_right, hconj k,
        cfInner_coherentImage_eq_ite H hinj hS hν, if_pos rfl]
    · intro l _ hl
      rw [cfInner_smul_left, cfInner_smul_right, cfInner_coherentImage_eq_ite H hinj hS hν,
        if_neg (Ne.symm hl), mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun k _ => hrow k, ← sum_sq_div_cfInner H hinj hS]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hn := cfInner_self_ne_zero (H := H) (mem_indFam_of_range_eq hS k)
  simp only [hc]
  field_simp

end Q

end NormalInducedWeightedNorm

end CFSG.FeitThompson
