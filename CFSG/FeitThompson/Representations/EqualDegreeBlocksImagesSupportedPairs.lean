module

public import CFSG.FeitThompson.Representations.DegreeZeroIsometryDisjointConjPairs
import CFSG.FeitThompson.Representations.EqualDegreeDifferencesAssignedPairs
import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
public import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.MultiplicityFreeBlockAgreeOnCore
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.SignedPairInducedBlockSpans

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {L G : Type*} [Group L] [Group G]

omit [Group L] in
theorem star_eq_conj_fun (f : L → ℂ) : (star f : L → ℂ) = fun y => conj (f y) := rfl

theorem charValueKernel_star (f : L → ℂ) : charValueKernel (star f) = charValueKernel f := by
  ext x
  simp only [mem_charValueKernel, star_eq_conj_fun]
  exact ⟨fun h => by simpa using congrArg conj h, fun h => by rw [h]⟩

theorem irrDetect_subset_Irr (H : Subgroup L) : irrDetect ℂ H ⊆ Irr L := by
  rw [Irr_eq_irrChar]
  exact irrDetect_subset_irrChar H

theorem star_mem_irrDetect [Finite L] {H : Subgroup L} {χ : L → ℂ} (hχ : χ ∈ irrDetect ℂ H) :
    star χ ∈ irrDetect ℂ H := by
  refine mem_irrDetect.2 ⟨?_, ?_⟩
  · rw [← Irr_eq_irrChar, star_eq_conj_fun]
    exact conj_mem_Irr (irrDetect_subset_Irr H hχ)
  · rw [charValueKernel_star]
    exact (mem_irrDetect.1 hχ).2

theorem star_ne_of_mem_irrDetect [Finite L] (hodd : Odd (Nat.card L)) {H : Subgroup L}
    {χ : L → ℂ} (hχ : χ ∈ irrDetect ℂ H) : star χ ≠ χ := fun h =>
  ne_conj_of_mem_Irr_of_ne_one_of_odd hodd (irrDetect_subset_Irr H hχ)
    (ne_one_of_mem_irrDetect hχ) (by rw [← star_eq_conj_fun, h])

theorem isAntirealIsometry_irrDetect [Fintype L] [Fintype G] (hodd : Odd (Nat.card L))
    (H : Subgroup L) {τ : (L → ℂ) → G → ℂ}
    (hadd : ∀ f ∈ charSpanZero (irrDetect ℂ H), ∀ h ∈ charSpanZero (irrDetect ℂ H),
      τ (f + h) = τ f + τ h)
    (hmem : ∀ f ∈ charSpanZero (irrDetect ℂ H), τ f ∈ Submodule.span ℤ (Irr G))
    (hisom : ∀ f ∈ charSpanZero (irrDetect ℂ H), ∀ h ∈ charSpanZero (irrDetect ℂ H),
      cfInner (τ f) (τ h) = cfInner f h)
    (hone : ∀ f ∈ charSpanZero (irrDetect ℂ H), τ f 1 = 0)
    (hstar : ∀ f ∈ charSpanZero (irrDetect ℂ H), τ (star f) = star (τ f)) :
    IsAntirealIsometry (irrDetect ℂ H) τ where
  subset_Irr := irrDetect_subset_Irr H
  star_mem _ hχ := star_mem_irrDetect hχ
  star_ne _ hχ := star_ne_of_mem_irrDetect hodd hχ
  map_add := hadd
  map_mem := hmem
  inner_eq := hisom
  apply_one := hone
  map_star := hstar

section Sums

variable [Fintype L]

theorem cfInner_sub_sum_sub_star {B₁ B₂ : Finset (L → ℂ)} (hB₁ : ↑B₁ ⊆ Irr L)
    (hB₂ : ↑B₂ ⊆ Irr L) {χ : L → ℂ} (hχ : χ ∈ Irr L) (h₁ : star χ ∉ B₁) (h₂ : star χ ∉ B₂) :
    cfInner ((∑ ψ ∈ B₁, ψ) - ∑ ψ ∈ B₂, ψ) (χ - star χ)
      = (if χ ∈ B₁ then (1 : ℂ) else 0) - (if χ ∈ B₂ then 1 else 0) := by
  classical
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_sum_eq_ite hB₁ hχ, cfInner_sum_eq_ite hB₂ hχ,
    cfInner_sum_eq_ite hB₁ (star_mem_Irr hχ), cfInner_sum_eq_ite hB₂ (star_mem_Irr hχ),
    if_neg h₁, if_neg h₂]
  ring

theorem cfInner_self_sub_sum {B₁ B₂ : Finset (L → ℂ)} (hB₁ : ↑B₁ ⊆ Irr L) (hB₂ : ↑B₂ ⊆ Irr L)
    (hdisj : Disjoint B₁ B₂) :
    cfInner ((∑ ψ ∈ B₁, ψ) - ∑ ψ ∈ B₂, ψ) ((∑ ψ ∈ B₁, ψ) - ∑ ψ ∈ B₂, ψ)
      = ((B₁.card : ℂ) + B₂.card) := by
  classical
  have hself : ∀ C : Finset (L → ℂ), ↑C ⊆ Irr L →
      cfInner (∑ ψ ∈ C, ψ) (∑ ψ ∈ C, ψ) = (C.card : ℂ) := by
    intro C hC
    rw [cfInner_sum_right]
    have h : ∀ ρ ∈ C, cfInner (∑ ψ ∈ C, ψ) ρ = 1 := fun ρ hρ => by
      rw [cfInner_sum_eq_ite hC (hC (Finset.mem_coe.2 hρ)), if_pos hρ]
    rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcross : ∀ C D : Finset (L → ℂ), ↑C ⊆ Irr L → ↑D ⊆ Irr L → Disjoint C D →
      cfInner (∑ ψ ∈ C, ψ) (∑ ψ ∈ D, ψ) = 0 := by
    intro C D hC hD hCD
    rw [cfInner_sum_right]
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    rw [cfInner_sum_eq_ite hC (hD (Finset.mem_coe.2 hρ)),
      if_neg (Finset.disjoint_right.1 hCD hρ)]
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hself B₁ hB₁, hself B₂ hB₂,
    hcross B₁ B₂ hB₁ hB₂ hdisj, hcross B₂ B₁ hB₂ hB₁ hdisj.symm]
  ring

end Sums

theorem one_le_sq_add_sq_of_ne {a b : ℤ} (h : a ≠ b) : 1 ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := fun h0 => h (by rw [h0])
    nlinarith [Int.one_le_abs hb, sq_abs b]
  · nlinarith [Int.one_le_abs ha, sq_abs a, sq_nonneg b]

namespace IsAntirealIsometry

variable [Fintype L] [Fintype G] {X : Set (L → ℂ)} {τ : (L → ℂ) → G → ℂ}
  (hτ : IsAntirealIsometry X τ)

include hτ

theorem map_sub_sum_mem_span {η : (L → ℂ) → G → ℂ}
    (hη : ∀ χ ∈ X, η χ ∈ Irr G ∧ τ (χ - star χ) = η χ - star (η χ))
    {B₁ B₂ : Finset (L → ℂ)} (hB₁ : ↑B₁ ⊆ X) (hB₂ : ↑B₂ ⊆ X) (hdisj : Disjoint B₁ B₂)
    (hst : ∀ χ ∈ B₁ ∪ B₂, star χ ∉ B₁ ∪ B₂)
    (hdeg : (∑ ψ ∈ B₁, (ψ : L → ℂ)) 1 = (∑ ψ ∈ B₂, (ψ : L → ℂ)) 1) :
    τ ((∑ ψ ∈ B₁, ψ) - ∑ ψ ∈ B₂, ψ) ∈
      Submodule.span ℤ {ρ : G → ℂ | ∃ χ ∈ B₁ ∪ B₂, ρ = η χ ∨ ρ = star (η χ)} := by
  classical
  set U := B₁ ∪ B₂ with hU
  have hUX : ↑U ⊆ X := by
    intro χ hχ
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hχ) with h | h
    · exact hB₁ h
    · exact hB₂ h
  have hB₁Irr : ↑B₁ ⊆ Irr L := fun _ h => hτ.subset_Irr (hB₁ h)
  have hB₂Irr : ↑B₂ ⊆ Irr L := fun _ h => hτ.subset_Irr (hB₂ h)
  set f : L → ℂ := (∑ ψ ∈ B₁, ψ) - ∑ ψ ∈ B₂, ψ with hf
  have hfmem : f ∈ charSpanZero X := by
    refine mem_charSpanZero.2 ⟨sub_mem ?_ ?_, by simp [hf, hdeg]⟩
    · exact Submodule.sum_mem _ fun ψ hψ => Submodule.subset_span (hB₁ hψ)
    · exact Submodule.sum_mem _ fun ψ hψ => Submodule.subset_span (hB₂ hψ)
  have hv : τ f ∈ Submodule.span ℤ (Irr G) := hτ.map_mem _ hfmem
  have hkey : ∀ χ ∈ U, η χ ∈ Irr G ∧ τ (χ - star χ) = η χ - star (η χ) :=
    fun χ hχ => hη χ (hUX hχ)
  have hnr : ∀ χ ∈ U, star (η χ) ≠ η χ := fun χ hχ =>
    hτ.star_ne_of_map_sub_star_eq (hUX hχ) (hkey χ hχ).1 (hkey χ hχ).2
  have hdisjpair : ∀ χ ∈ U, ∀ ψ ∈ U, χ ≠ ψ →
      Disjoint ({η χ, star (η χ)} : Set (G → ℂ)) {η ψ, star (η ψ)} := fun χ hχ ψ hψ hne =>
    hτ.disjoint_pair_of_map_sub_star_eq (hUX hχ) (hUX hψ) (Ne.symm hne)
      (fun h => hst χ hχ (h ▸ hψ)) (hkey χ hχ).1 (hkey ψ hψ).1 (hkey χ hχ).2 (hkey ψ hψ).2
  set pair : (L → ℂ) → Finset (G → ℂ) := fun χ => {η χ, star (η χ)} with hpair
  set R : Finset (G → ℂ) := U.biUnion pair with hR
  have hpairIrr : ∀ χ ∈ U, ∀ r ∈ pair χ, r ∈ Irr G := by
    intro χ hχ r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact (hkey χ hχ).1
    · rw [Finset.mem_singleton] at hr
      exact hr ▸ star_mem_Irr (hkey χ hχ).1
  have hRIrr : ∀ r ∈ R, r ∈ Irr G := by
    intro r hr
    obtain ⟨χ, hχ, hr'⟩ := Finset.mem_biUnion.1 hr
    exact hpairIrr χ hχ r hr'
  have hRspan : ↑R ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := fun r hr =>
    Submodule.subset_span (hRIrr r (Finset.mem_coe.1 hr))
  have hone : ∀ r ∈ R, cfInner r r = 1 := fun r hr => cfInner_self_of_mem_Irr (hRIrr r hr)
  have hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0 := fun r hr s hs hne =>
    cfInner_eq_zero_of_mem_Irr (hRIrr r hr) (hRIrr s hs) hne
  obtain ⟨a, ha⟩ := IntegralBlockProjection.exists_int_cfInner_forall_mem hRspan hv
  have hpairdisj : (U : Set (L → ℂ)).PairwiseDisjoint pair := by
    intro χ hχ ψ hψ hne
    have h := hdisjpair χ (Finset.mem_coe.1 hχ) ψ (Finset.mem_coe.1 hψ) hne
    simp only [Function.onFun, hpair, ← Finset.disjoint_coe]
    simpa using h
  have hcoeff : ∀ χ ∈ U, a (η χ) ≠ a (star (η χ)) := by
    intro χ hχ
    have hmemη : η χ ∈ R := Finset.mem_biUnion.2 ⟨χ, hχ, by simp [hpair]⟩
    have hmemsη : star (η χ) ∈ R := Finset.mem_biUnion.2 ⟨χ, hχ, by simp [hpair]⟩
    have hsub : χ - star χ ∈ charSpanZero X := hτ.sub_star_mem (hUX hχ)
    have hiso : cfInner (τ f) (τ (χ - star χ)) = cfInner f (χ - star χ) :=
      hτ.inner_eq _ hfmem _ hsub
    rw [(hkey χ hχ).2, cfInner_sub_right, ha _ hmemη, ha _ hmemsη] at hiso
    have hstχ : star χ ∉ B₁ ∧ star χ ∉ B₂ := by
      have h := hst χ hχ
      rw [hU, Finset.mem_union] at h
      tauto
    rw [cfInner_sub_sum_sub_star hB₁Irr hB₂Irr (hτ.subset_Irr (hUX hχ)) hstχ.1 hstχ.2] at hiso
    intro hcon
    rw [hcon, sub_self] at hiso
    rcases Finset.mem_union.1 hχ with h | h
    · rw [if_pos h, if_neg (Finset.disjoint_left.1 hdisj h)] at hiso
      norm_num at hiso
    · rw [if_neg (Finset.disjoint_right.1 hdisj h), if_pos h] at hiso
      norm_num at hiso
  have hbessel : (U.card : ℤ) ≤ ∑ r ∈ R, a r ^ 2 := by
    rw [hR, Finset.sum_biUnion hpairdisj]
    have h : ∀ χ ∈ U, (1 : ℤ) ≤ ∑ r ∈ pair χ, a r ^ 2 := by
      intro χ hχ
      rw [hpair, Finset.sum_pair (Ne.symm (hnr χ hχ))]
      exact one_le_sq_add_sq_of_ne (hcoeff χ hχ)
    calc (U.card : ℤ) = ∑ _χ ∈ U, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum h
  have hnormv : cfInner (τ f) (τ f) = ((U.card : ℤ) : ℂ) := by
    rw [hτ.inner_eq _ hfmem _ hfmem, hf, cfInner_self_sub_sum hB₁Irr hB₂Irr hdisj, hU,
      Finset.card_union_of_disjoint hdisj]
    push_cast
    ring
  set P : G → ℂ := ∑ r ∈ R, cfInner (τ f) r • r with hP
  have hPnorm : cfInner P P = ((∑ r ∈ R, a r ^ 2 : ℤ) : ℂ) :=
    IntegralBlockProjection.cfInner_sum_cfInner_smul_self hone hzero ha
  have hsplit : cfInner (τ f) (τ f) = cfInner P P + cfInner (τ f - P) (τ f - P) :=
    IntegralBlockProjection.cfInner_self_eq_add hone hzero
  have hPmem : P ∈ Submodule.span ℤ (Irr G) := by
    rw [hP]
    refine Submodule.sum_mem _ fun r hr => ?_
    rw [ha r hr, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hRspan (Finset.mem_coe.2 hr))
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr (sub_mem hv hPmem) (sub_mem hv hPmem)
  have hm0 : 0 ≤ m := by
    have h : (0 : ℂ) ≤ (m : ℂ) := hm ▸ cfInner_self_nonneg _
    exact_mod_cast h
  have harith : (U.card : ℤ) = (∑ r ∈ R, a r ^ 2) + m := by
    have h := hsplit
    rw [hnormv, hPnorm, hm] at h
    exact_mod_cast h
  have hmzero : m = 0 := by omega
  have hfeq : τ f = P := by
    have : Nonempty G := ⟨1⟩
    have hz : cfInner (τ f - P) (τ f - P) = 0 := by rw [hm, hmzero, Int.cast_zero]
    have h := cfInner_self_eq_zero.1 hz
    rwa [sub_eq_zero] at h
  rw [show τ ((∑ ψ ∈ B₁, ψ) - ∑ ψ ∈ B₂, ψ) = τ f from rfl, hfeq, hP]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [ha r hr, Int.cast_smul_eq_zsmul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨χ, hχ, hr'⟩ := Finset.mem_biUnion.1 hr
  refine ⟨χ, hχ, ?_⟩
  rcases Finset.mem_insert.1 hr' with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.1 h)

end IsAntirealIsometry

variable [Fintype L] [Fintype G] {η : (L → ℂ) → G → ℂ}

def rootPairSet (η : (L → ℂ) → G → ℂ) (θ : L → ℂ) : Set (G → ℂ) :=
  ⋃ χ ∈ irrConstituents θ, {η χ, -star (η χ)}

omit [Group G] [Fintype G] in
theorem mem_rootPairSet {θ : L → ℂ} {ρ : G → ℂ} :
    ρ ∈ rootPairSet η θ ↔ ∃ χ ∈ irrConstituents θ, ρ = η χ ∨ ρ = -star (η χ) := by
  simp [rootPairSet]

omit [Group G] [Fintype G] in
theorem root_mem_span_rootPairSet {θ χ : L → ℂ} (hχ : χ ∈ irrConstituents θ) :
    η χ ∈ Submodule.span ℤ (rootPairSet η θ) :=
  Submodule.subset_span (mem_rootPairSet.2 ⟨χ, hχ, Or.inl rfl⟩)

omit [Group G] [Fintype G] in
theorem star_root_mem_span_rootPairSet {θ χ : L → ℂ} (hχ : χ ∈ irrConstituents θ) :
    star (η χ) ∈ Submodule.span ℤ (rootPairSet η θ) := by
  have h := Submodule.subset_span (R := ℤ)
    (mem_rootPairSet.2 ⟨χ, hχ, Or.inr rfl⟩ : -star (η χ) ∈ rootPairSet η θ)
  simpa using neg_mem h

theorem map_sub_mem_span_rootPairSet (hodd : Odd (Nat.card L)) (H : Subgroup L) [H.Normal]
    {τ : (L → ℂ) → G → ℂ} (hτ : IsAntirealIsometry (irrDetect ℂ H) τ)
    (hη : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G ∧ τ (χ - star χ) = η χ - star (η χ))
    (hS : ∀ θ ∈ indFam H (nonprincipalIrr H), θ = ∑ χ ∈ irrConstituentsFinset θ, χ)
    {θ₁ θ₂ : L → ℂ} (hθ₁ : θ₁ ∈ indFam H (nonprincipalIrr H))
    (hθ₂ : θ₂ ∈ indFam H (nonprincipalIrr H)) (hdeg : θ₁ 1 = θ₂ 1) :
    τ (θ₁ - θ₂) ∈ Submodule.span ℤ (rootPairSet η θ₁ ∪ rootPairSet η θ₂) := by
  classical
  have hBX : ∀ θ ∈ indFam H (nonprincipalIrr H), ∀ χ ∈ irrConstituentsFinset θ,
      χ ∈ irrDetect ℂ H := fun θ hθ χ hχ =>
    (iUnion_irrConstituents H) ▸ Set.mem_biUnion hθ (mem_irrConstituentsFinset.1 hχ)
  by_cases h1 : θ₂ = θ₁
  ·
    subst h1
    rw [sub_self, hτ.map_zero]
    exact zero_mem _
  by_cases h2 : θ₂ = star θ₁
  ·
    subst h2
    have hsum : θ₁ - star θ₁ = ∑ χ ∈ irrConstituentsFinset θ₁, (χ - star χ) := by
      rw [Finset.sum_sub_distrib, ← hS θ₁ hθ₁, ← star_sum, ← hS θ₁ hθ₁]
    rw [hsum, hτ.map_sum fun χ hχ => hτ.sub_star_mem (hBX θ₁ hθ₁ χ hχ)]
    refine Submodule.sum_mem _ fun χ hχ => ?_
    rw [(hη χ (hBX θ₁ hθ₁ χ hχ)).2]
    refine sub_mem (Submodule.span_mono Set.subset_union_left ?_)
      (Submodule.span_mono Set.subset_union_left ?_)
    · exact root_mem_span_rootPairSet (mem_irrConstituentsFinset.1 hχ)
    · exact star_root_mem_span_rootPairSet (mem_irrConstituentsFinset.1 hχ)
  set B₁ := irrConstituentsFinset θ₁ with hB₁def
  set B₂ := irrConstituentsFinset θ₂ with hB₂def
  have hdisj : Disjoint B₁ B₂ := by
    have h := pairwiseDisjoint_irrConstituents H hθ₁ hθ₂ (Ne.symm h1)
    simpa [hB₁def, hB₂def, Function.onFun, ← Finset.disjoint_coe] using h
  have hstar : ∀ χ ∈ B₁ ∪ B₂, star χ ∉ B₁ ∪ B₂ := by
    intro χ hχ hcon
    have hne21 : θ₂ ≠ star θ₁ := h2
    have hne12 : θ₁ ≠ star θ₂ := fun h => hne21 (by rw [h, star_star])
    rcases Finset.mem_union.1 hχ with h | h <;> rcases Finset.mem_union.1 hcon with h' | h'
    · exact conj_notMem_irrConstituents hodd H hθ₁ (mem_irrConstituentsFinset.1 h)
        (mem_irrConstituentsFinset.1 h')
    · exact Set.disjoint_left.1
        (pairwiseDisjoint_irrConstituents H (conj_mem_indFam_nonprincipalIrr H hθ₁) hθ₂
          (Ne.symm hne21)) (conj_mem_irrConstituents (mem_irrConstituentsFinset.1 h))
        (mem_irrConstituentsFinset.1 h')
    · exact Set.disjoint_left.1
        (pairwiseDisjoint_irrConstituents H (conj_mem_indFam_nonprincipalIrr H hθ₂) hθ₁
          (Ne.symm hne12)) (conj_mem_irrConstituents (mem_irrConstituentsFinset.1 h))
        (mem_irrConstituentsFinset.1 h')
    · exact conj_notMem_irrConstituents hodd H hθ₂ (mem_irrConstituentsFinset.1 h)
        (mem_irrConstituentsFinset.1 h')
  have hdeg' : (∑ ψ ∈ B₁, (ψ : L → ℂ)) 1 = (∑ ψ ∈ B₂, (ψ : L → ℂ)) 1 := by
    rw [hB₁def, hB₂def, ← hS θ₁ hθ₁, ← hS θ₂ hθ₂]
    exact hdeg
  have hmain := hτ.map_sub_sum_mem_span hη (fun _ h => hBX θ₁ hθ₁ _ h)
    (fun _ h => hBX θ₂ hθ₂ _ h) hdisj hstar hdeg'
  rw [← hS θ₁ hθ₁, ← hS θ₂ hθ₂] at hmain
  refine Submodule.span_le.2 ?_ hmain
  rintro ρ ⟨χ, hχ, hρ⟩
  rcases Finset.mem_union.1 hχ with h | h
  · rcases hρ with rfl | rfl
    · exact Submodule.span_mono Set.subset_union_left
        (root_mem_span_rootPairSet (mem_irrConstituentsFinset.1 h))
    · exact Submodule.span_mono Set.subset_union_left
        (star_root_mem_span_rootPairSet (mem_irrConstituentsFinset.1 h))
  · rcases hρ with rfl | rfl
    · exact Submodule.span_mono Set.subset_union_right
        (root_mem_span_rootPairSet (mem_irrConstituentsFinset.1 h))
    · exact Submodule.span_mono Set.subset_union_right
        (star_root_mem_span_rootPairSet (mem_irrConstituentsFinset.1 h))

theorem map_sub_mem_span_rootPairSet_of_isometry (hodd : Odd (Nat.card L)) (H : Subgroup L)
    [H.Normal] {τ : (L → ℂ) → G → ℂ}
    (hadd : ∀ f ∈ charSpanZero (irrDetect ℂ H), ∀ h ∈ charSpanZero (irrDetect ℂ H),
      τ (f + h) = τ f + τ h)
    (hmem : ∀ f ∈ charSpanZero (irrDetect ℂ H), τ f ∈ Submodule.span ℤ (Irr G))
    (hisom : ∀ f ∈ charSpanZero (irrDetect ℂ H), ∀ h ∈ charSpanZero (irrDetect ℂ H),
      cfInner (τ f) (τ h) = cfInner f h)
    (hone : ∀ f ∈ charSpanZero (irrDetect ℂ H), τ f 1 = 0)
    (hstar : ∀ f ∈ charSpanZero (irrDetect ℂ H), τ (star f) = star (τ f))
    (hη : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G ∧ τ (χ - star χ) = η χ - star (η χ))
    (hS : ∀ θ ∈ indFam H (nonprincipalIrr H), θ = ∑ χ ∈ irrConstituentsFinset θ, χ)
    {θ₁ θ₂ : L → ℂ} (hθ₁ : θ₁ ∈ indFam H (nonprincipalIrr H))
    (hθ₂ : θ₂ ∈ indFam H (nonprincipalIrr H)) (hdeg : θ₁ 1 = θ₂ 1) :
    τ (θ₁ - θ₂) ∈ Submodule.span ℤ (rootPairSet η θ₁ ∪ rootPairSet η θ₂) :=
  map_sub_mem_span_rootPairSet hodd H
    (isAntirealIsometry_irrDetect hodd H hadd hmem hisom hone hstar) hη hS hθ₁ hθ₂ hdeg

end

end CFSG.FeitThompson
