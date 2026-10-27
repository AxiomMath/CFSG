module

public import CFSG.FeitThompson.Representations.NormalInducedBlockPartition
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

variable {L : Type*} [Group L] [Fintype L]

noncomputable def irrConstituentsFinset (θ : L → ℂ) : Finset (L → ℂ) :=
  (finite_irrConstituents θ).toFinset

@[simp] theorem mem_irrConstituentsFinset {θ χ : L → ℂ} :
    χ ∈ irrConstituentsFinset θ ↔ χ ∈ irrConstituents θ := Set.Finite.mem_toFinset _

@[simp] theorem coe_irrConstituentsFinset (θ : L → ℂ) :
    (irrConstituentsFinset θ : Set (L → ℂ)) = irrConstituents θ := Set.Finite.coe_toFinset _

theorem irrConstituentsFinset_subset_irrFinset (θ : L → ℂ) :
    irrConstituentsFinset θ ⊆ irrFinset L := fun _ hχ =>
  mem_irrFinset.2 (irrConstituents_subset_Irr θ (mem_irrConstituentsFinset.1 hχ))

theorem eq_sum_cfInner_smul_irrFinset {f : L → ℂ} (hf : f ∈ classFun L) :
    f = ∑ χ ∈ irrFinset L, cfInner f χ • χ := by
  classical
  have : Fintype (Irr L) := Fintype.ofFinite _
  rw [← Finset.sum_coe_sort (irrFinset L) (fun χ => cfInner f χ • χ)]
  refine (eq_sum_cfInner_smul_of_mem_classFun hf).trans
    (Fintype.sum_equiv (Equiv.subtypeEquivRight (fun _ => mem_irrFinset.symm)) _ _ fun _ => ?_)
  rfl

theorem apply_eq_sum_cfInner_mul {f : L → ℂ} (hf : f ∈ classFun L) (y : L) :
    f y = ∑ χ ∈ irrFinset L, cfInner f χ * χ y := by
  conv_lhs => rw [eq_sum_cfInner_smul_irrFinset hf]
  simp [Finset.sum_apply]

omit [Fintype L] in
theorem apply_mul_eq_of_mem_irrTrivialOn [Finite L] {H : Subgroup L} [H.Normal] {χ : L → ℂ}
    (hχ : χ ∈ irrTrivialOn H) (x : L) {h : L} (hh : h ∈ H) : χ (x * h) = χ x := by
  obtain ⟨ψ, -, rfl⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn hχ
  simp only [Function.comp_apply]
  congr 1
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).2 hh, mul_one]

section Main

variable (H : Subgroup L) [H.Normal]

noncomputable def indFamNonprincipalFinset : Finset (L → ℂ) :=
  (indFam_finite H finite_nonprincipalIrr).toFinset

omit [H.Normal] in
@[simp] theorem mem_indFamNonprincipalFinset {θ : L → ℂ} :
    θ ∈ indFamNonprincipalFinset H ↔ θ ∈ indFam H (nonprincipalIrr H) :=
  Set.Finite.mem_toFinset _

open scoped Classical in
noncomputable def irrDetectFinset : Finset (L → ℂ) :=
  (indFamNonprincipalFinset H).biUnion irrConstituentsFinset

open scoped Classical in
theorem coe_irrDetectFinset : (irrDetectFinset H : Set (L → ℂ)) = irrDetect ℂ H := by
  rw [irrDetectFinset, Finset.coe_biUnion, ← iUnion_irrConstituents H]
  simp

omit [H.Normal] in
theorem irrDetectFinset_subset_irrFinset : irrDetectFinset H ⊆ irrFinset L := by
  classical
  intro χ hχ
  rw [irrDetectFinset, Finset.mem_biUnion] at hχ
  obtain ⟨θ, -, hχθ⟩ := hχ
  exact irrConstituentsFinset_subset_irrFinset θ hχθ

theorem pairwiseDisjoint_irrConstituentsFinset :
    (indFamNonprincipalFinset H : Set (L → ℂ)).PairwiseDisjoint irrConstituentsFinset := by
  intro θ hθ θ' hθ' hne
  have h := pairwiseDisjoint_irrConstituents H ((mem_indFamNonprincipalFinset H).1 hθ)
    ((mem_indFamNonprincipalFinset H).1 hθ') hne
  simpa [Function.onFun, ← Finset.disjoint_coe] using h

theorem mem_irrTrivialOn_of_notMem_irrDetectFinset {χ : L → ℂ} (hχ : χ ∈ irrFinset L)
    (hχ' : χ ∉ irrDetectFinset H) : χ ∈ irrTrivialOn H := by
  classical
  have h : χ ∉ irrDetect ℂ H := by
    rw [← coe_irrDetectFinset H]; simpa using hχ'
  rw [mem_irrDetect, not_and_or] at h
  have hIrr := mem_irrFinset.1 hχ
  refine mem_irrTrivialOn.2 ⟨hIrr, fun n hn => ?_⟩
  rcases h with h | h
  · exact absurd ((Irr_eq_irrChar L) ▸ hIrr) h
  · exact mem_charValueKernel.1 (not_not.1 h hn)

theorem sum_irrDetectFinset_eq_zero
    (hS : ∀ θ ∈ indFam H (nonprincipalIrr H), θ = ∑ χ ∈ irrConstituentsFinset θ, χ)
    {f : L → ℂ}
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr H), ∀ χ ∈ irrConstituents θ,
      ∀ ψ ∈ irrConstituents θ, cfInner f (χ - ψ) = 0)
    {y : L} (hy : y ∉ H) :
    ∑ χ ∈ irrDetectFinset H, cfInner f χ * χ y = 0 := by
  classical
  rw [irrDetectFinset, Finset.sum_biUnion (pairwiseDisjoint_irrConstituentsFinset H)]
  refine Finset.sum_eq_zero fun θ hθ => ?_
  have hθ' := (mem_indFamNonprincipalFinset H).1 hθ
  obtain ⟨χ₀, hχ₀⟩ := irrConstituents_nonempty_of_mem_indFam H hθ'
  have hconst : ∀ χ ∈ irrConstituentsFinset θ, cfInner f χ = cfInner f χ₀ := by
    intro χ hχ
    have h := horth θ hθ' χ (mem_irrConstituentsFinset.1 hχ) χ₀ hχ₀
    rw [cfInner_sub_right] at h
    linear_combination h
  have hsum : ∑ χ ∈ irrConstituentsFinset θ, χ y = θ y := by
    conv_rhs => rw [hS θ hθ']
    simp
  calc ∑ χ ∈ irrConstituentsFinset θ, cfInner f χ * χ y
      = cfInner f χ₀ * ∑ χ ∈ irrConstituentsFinset θ, χ y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ hχ => by rw [hconst χ hχ]
    _ = 0 := by
        rw [hsum, eq_zero_of_mem_indFam_of_notMem H hθ' hy, mul_zero]

theorem apply_mul_eq_of_cfInner_sub_eq_zero
    (hS : ∀ θ ∈ indFam H (nonprincipalIrr H), θ = ∑ χ ∈ irrConstituentsFinset θ, χ)
    {f : L → ℂ} (hf : f ∈ classFun L)
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr H), ∀ χ ∈ irrConstituents θ,
      ∀ ψ ∈ irrConstituents θ, cfInner f (χ - ψ) = 0)
    {x : L} (hx : x ∉ H) {h : L} (hh : h ∈ H) : f (x * h) = f x := by
  classical
  have hxh : x * h ∉ H := fun hmem => hx (by simpa using H.mul_mem hmem (H.inv_mem hh))
  have hsplit : ∀ y : L, y ∉ H →
      f y = ∑ χ ∈ irrFinset L \ irrDetectFinset H, cfInner f χ * χ y := by
    intro y hy
    rw [apply_eq_sum_cfInner_mul hf y,
      ← Finset.sum_sdiff (irrDetectFinset_subset_irrFinset H),
      sum_irrDetectFinset_eq_zero H hS horth hy, add_zero]
  rw [hsplit _ hxh, hsplit _ hx]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Finset.mem_sdiff] at hχ
  rw [apply_mul_eq_of_mem_irrTrivialOn
    (mem_irrTrivialOn_of_notMem_irrDetectFinset H hχ.1 hχ.2) x hh]

theorem apply_mul_eq_of_isOrthogonal_sub
    (hS : ∀ θ ∈ indFam H (nonprincipalIrr H), θ = ∑ χ ∈ irrConstituentsFinset θ, χ)
    {f : L → ℂ} (hf : f ∈ classFun L)
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr H), ∀ χ ∈ irrConstituents θ,
      ∀ ψ ∈ irrConstituents θ, IsOrthogonal f (χ - ψ))
    {x : L} (hx : x ∉ H) {h : L} (hh : h ∈ H) : f (x * h) = f x :=
  apply_mul_eq_of_cfInner_sub_eq_zero H hS hf
    (fun θ hθ χ hχ ψ hψ => isOrthogonal_iff.1 (horth θ hθ χ hχ ψ hψ)) hx hh

theorem apply_eq_of_mul_mem
    (hS : ∀ θ ∈ indFam H (nonprincipalIrr H), θ = ∑ χ ∈ irrConstituentsFinset θ, χ)
    {f : L → ℂ} (hf : f ∈ classFun L)
    (horth : ∀ θ ∈ indFam H (nonprincipalIrr H), ∀ χ ∈ irrConstituents θ,
      ∀ ψ ∈ irrConstituents θ, cfInner f (χ - ψ) = 0)
    {x y : L} (hx : x ∉ H) (hxy : x⁻¹ * y ∈ H) : f y = f x := by
  have := apply_mul_eq_of_cfInner_sub_eq_zero H hS hf horth hx hxy
  rwa [mul_inv_cancel_left] at this

end Main

end CFSG.FeitThompson
