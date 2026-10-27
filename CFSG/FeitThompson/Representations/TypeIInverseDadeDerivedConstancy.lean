module

public import CFSG.FeitThompson.Representations.EqualDegreeBlocksImagesSupportedPairs
public import CFSG.FeitThompson.Representations.DadeReciprocityCoefficientEquality
public import CFSG.FeitThompson.Representations.FrobeniusTypeLocalBlockData
public import CFSG.FeitThompson.Representations.EqualDegreeCoefficientsDerivedConstancy
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.CoherentQuotientLinearImageConstant
import CFSG.FeitThompson.Representations.CoherentJoiningOneBridge

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {R : G → Subgroup G}

noncomputable def dadeExtend (L : Subgroup G) (A : Set G) (R : G → Subgroup G) (f : ↥L → ℂ) :
    G → ℂ :=
  dadeSupportExtension A R (extendByZero L f)

theorem dadeExtend_eq_dadeSupportExtension (f : ↥L → ℂ) :
    dadeExtend L A R f = dadeSupportExtension A R (extendByZero L f) := (rfl)

theorem dadeExtend_eq_dadeMap [Finite G] (hD : IsDadeData L A R) {f : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A) :
    dadeExtend L A R f = ((dadeMap hD ⟨f, hf⟩ : classFun G) : G → ℂ) :=
  (dadeMap_apply_coe hD ⟨f, hf⟩).symm

theorem dadeExtend_add (f g : ↥L → ℂ) :
    dadeExtend L A R (f + g) = dadeExtend L A R f + dadeExtend L A R g := by
  rw [dadeExtend_eq_dadeSupportExtension, dadeExtend_eq_dadeSupportExtension,
    dadeExtend_eq_dadeSupportExtension, extendByZero_add, dadeSupportExtension_add]

theorem dadeExtend_star (f : ↥L → ℂ) :
    dadeExtend L A R (star f) = star (dadeExtend L A R f) := by
  rw [dadeExtend_eq_dadeSupportExtension, dadeExtend_eq_dadeSupportExtension, extendByZero_star,
    dadeSupportExtension_star]

noncomputable def invDadeRoot (L : Subgroup G) (A : Set G) (R : G → Subgroup G) (χ : ↥L → ℂ) :
    G → ℂ :=
  antirealRoot (dadeExtend L A R (χ - star χ))

theorem invDadeRoot_eq (χ : ↥L → ℂ) :
    invDadeRoot L A R χ = antirealRoot (dadeExtend L A R (χ - star χ)) := (rfl)

variable {H U U₁ : Subgroup ↥L} [H.Normal]

theorem mem_dadeDomain_of_mem_charSpanZero [Finite G]
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero (irrDetect ℂ H)) : f ∈ dadeDomain L A := by
  have : Finite ↥L := Subtype.finite
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeDomain_of_mem_span_Irr (Submodule.span_mono (irrDetect_subset_Irr H) hspan)
    fun x hx => ?_
  rcases eq_or_ne x 1 with rfl | hx1
  · exact h1
  · refine NormalLinearInduced.apply_eq_zero_of_mem_span (x := x) ?_ hspan
    intro s hs
    exact eq_zero_of_notMem_insert_one_coreCentralizerSupport hs
      (by simp only [Set.mem_insert_iff]; exact fun h => h.elim hx1 (fun h => hx ((hA x).2 h)))

theorem isAntirealIsometry_dadeExtend [Fintype G] [Fintype ↥L] (hD : IsDadeData L A R)
    (hodd : Odd (Nat.card ↥L))
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H) :
    IsAntirealIsometry (irrDetect ℂ H) (dadeExtend L A R) := by
  refine isAntirealIsometry_irrDetect hodd H (fun f _ h _ => dadeExtend_add f h) ?_ ?_ ?_
    (fun f _ => dadeExtend_star f)
  · intro f hf
    rw [dadeExtend_eq_dadeMap hD (mem_dadeDomain_of_mem_charSpanZero hA hf)]
    exact hD.dadeMap_mem_span_Irr _
      (Submodule.span_mono (irrDetect_subset_Irr H) (mem_charSpanZero.1 hf).1)
  · intro f hf h hh
    rw [dadeExtend_eq_dadeMap hD (mem_dadeDomain_of_mem_charSpanZero hA hf),
      dadeExtend_eq_dadeMap hD (mem_dadeDomain_of_mem_charSpanZero hA hh)]
    exact cfInner_dadeMap hD _ _
  · intro f hf
    rw [dadeExtend_eq_dadeMap hD (mem_dadeDomain_of_mem_charSpanZero hA hf)]
    exact dadeMap_one_eq_zero hD _

theorem existsUnique_invDadeRoot [Finite G] (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {χ : ↥L → ℂ} (hχ : χ ∈ irrDetect ℂ H) :
    ∃! η : G → ℂ, η ∈ Irr G ∧ star η ≠ η ∧ dadeExtend L A R (χ - star χ) = η - star η := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite ↥L
  exact (isAntirealIsometry_dadeExtend hD hodd hA).existsUnique_root hχ

theorem invDadeRoot_mem_Irr [Finite G] (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {χ : ↥L → ℂ} (hχ : χ ∈ irrDetect ℂ H) : invDadeRoot L A R χ ∈ Irr G := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite ↥L
  exact (isAntirealIsometry_dadeExtend hD hodd hA).root_mem_Irr hχ

theorem dadeExtend_sub_star_eq [Finite G] (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {χ : ↥L → ℂ} (hχ : χ ∈ irrDetect ℂ H) :
    dadeExtend L A R (χ - star χ) = invDadeRoot L A R χ - star (invDadeRoot L A R χ) := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite ↥L
  exact (isAntirealIsometry_dadeExtend hD hodd hA).map_sub_star_eq hχ

omit [H.Normal] in
theorem mem_of_mem_of_ne_one (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {x : ↥L} (hx : x ∈ H) (hx1 : x ≠ 1) : (x : G) ∈ A :=
  (hA x).2 (mem_coreCentralizerSupport_iff_exists.2 ⟨hx1, x, hx, hx1, rfl⟩)

section Main

variable [Fintype G] [Fintype ↥L]

omit [Fintype G] in
theorem sum_irrConstituentsFinset_of_mem_indFam (hLD : IsFrobeniusTypeLocalData H U U₁)
    {θ : ↥L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr ↥H)) :
    θ = ∑ χ ∈ irrConstituentsFinset θ, χ := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  have hfs : irrConstituentsFinset (indClassFun H lam)
      = (finite_irrConstituents (indClassFun H lam)).toFinset := by
    rw [← Finset.coe_inj, coe_irrConstituentsFinset, Set.Finite.coe_toFinset]
  rw [hfs]
  exact indClassFun_eq_sum_irrConstituents hLD hlam

theorem dadeAverage_apply_eq_apply_of_notMem_commutator
    (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hLD : IsFrobeniusTypeLocalData H U U₁)
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {η : (↥L → ℂ) → G → ℂ}
    (hη : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G ∧
      dadeExtend L A R (χ - star χ) = η χ - star (η χ))
    {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G)
    (hortho : ∀ θ ∈ indFam H (nonprincipalIrr ↥H), ∀ ρ ∈ rootPairSet η θ, IsOrthogonal Ψ ρ)
    {x y : ↥H} (hx : x ∉ commutator ↥H) (hy : y ∉ commutator ↥H) :
    dadeAverage A R Ψ ((x : ↥L) : G) = dadeAverage A R Ψ ((y : ↥L) : G) := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have hτ : IsAntirealIsometry (irrDetect ℂ H) (dadeExtend L A R) :=
    isAntirealIsometry_dadeExtend hD hodd hA
  have hS := fun θ hθ => sum_irrConstituentsFinset_of_mem_indFam hLD (θ := θ) hθ
  have hNA : ∀ z : ↥L, z ∈ H → z ≠ 1 → (z : G) ∈ A := fun z hz hz1 =>
    mem_of_mem_of_ne_one hA hz hz1
  have hortho' : ∀ θ ∈ Irr ↥H, ∀ θ' ∈ Irr ↥H, θ ≠ 1 → θ' ≠ 1 → ∀ hdeg : θ 1 = θ' 1,
      cfInner Ψ ((dadeMap hD ⟨indClassFun H θ - indClassFun H θ',
        indClassFun_sub_mem_dadeDomain hNA hdeg⟩ : classFun G) : G → ℂ) = 0 := by
    intro θ hθ θ' hθ' hθ1 hθ'1 hdeg
    have h1 : indClassFun H θ ∈ indFam H (nonprincipalIrr ↥H) :=
      (mem_indFam H).2 ⟨θ, mem_nonprincipalIrr.2 ⟨hθ, hθ1⟩, rfl⟩
    have h2 : indClassFun H θ' ∈ indFam H (nonprincipalIrr ↥H) :=
      (mem_indFam H).2 ⟨θ', mem_nonprincipalIrr.2 ⟨hθ', hθ'1⟩, rfl⟩
    have hdeg' : indClassFun H θ 1 = indClassFun H θ' 1 := by
      rw [indClassFun_one, indClassFun_one, hdeg]
    have hmem := map_sub_mem_span_rootPairSet (η := η) hodd H hτ hη hS h1 h2 hdeg'
    rw [← dadeExtend_eq_dadeMap hD (indClassFun_sub_mem_dadeDomain hNA hdeg)]
    refine cfInner_eq_zero_of_mem_span_of_mem_span (A := {Ψ}) ?_ (Submodule.subset_span rfl) hmem
    rintro u rfl ρ hρ
    rcases hρ with hρ | hρ
    · exact isOrthogonal_iff.1 (hortho _ h1 _ hρ)
    · exact isOrthogonal_iff.1 (hortho _ h2 _ hρ)
  have hcoeff : HasEqualDegreeCoeffs
      (resClassFun H fun z : ↥L => dadeAverage A R Ψ (z : G)) :=
    hasEqualDegreeCoeffs_iff.2 fun lam hlam mu hmu hlam1 hmu1 hdeg =>
      cfInner_dadeAverage_res_eq_of_cfInner_dadeMap_eq_zero hD hNA hΨ hortho'
        hlam hmu hlam1 hmu1 hdeg
  have hfc : (resClassFun H fun z : ↥L => dadeAverage A R Ψ (z : G)) ∈ classFun ↥H :=
    dadeAverage_res_mem_classFun hD hΨ
  have hxy := hcoeff.apply_eq_apply_of_notMem_commutator hfc hx hy
  rwa [resClassFun_apply, resClassFun_apply] at hxy

theorem dadeAverage_apply_eq_apply_of_notMem_commutator_invDadeRoot
    (hD : IsDadeData L A R) (hodd : Odd (Nat.card ↥L))
    (hLD : IsFrobeniusTypeLocalData H U U₁)
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ coreCentralizerSupport H)
    {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G)
    (hortho : ∀ θ ∈ indFam H (nonprincipalIrr ↥H),
      ∀ ρ ∈ rootPairSet (invDadeRoot L A R) θ, IsOrthogonal Ψ ρ)
    {x y : ↥H} (hx : x ∉ commutator ↥H) (hy : y ∉ commutator ↥H) :
    dadeAverage A R Ψ ((x : ↥L) : G) = dadeAverage A R Ψ ((y : ↥L) : G) :=
  dadeAverage_apply_eq_apply_of_notMem_commutator hD hodd hLD hA
    (fun _ hχ => ⟨invDadeRoot_mem_Irr hD hodd hA hχ, dadeExtend_sub_star_eq hD hodd hA hχ⟩)
    hΨ hortho hx hy

end Main

end CFSG.FeitThompson
