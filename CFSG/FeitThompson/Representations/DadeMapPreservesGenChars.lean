module

public import CFSG.FeitThompson.Representations.DadeMapInductionExpansion
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.InductionMulRestrictedClassFun
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

theorem mem_dadeDomain_of_mem_span_Irr {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ (Irr ↥L))
    (hf0 : ∀ x : ↥L, (x : G) ∉ A → f x = 0) : f ∈ dadeDomain L A :=
  mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_Irr hf, hf0⟩

theorem dadeExpansionTerm_mem_span_Irr [Fintype G] (hD : IsDadeData L A H) {f : ↥L → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr ↥L)) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A) :
    dadeExpansionTerm hD f B ∈ Submodule.span ℤ (Irr G) := by
  have hterm : dadeExpansionTerm hD f B
      = ((-1 : ℤ) ^ (B.ncard + 1)) •
        InducedCharacterConstruction.indClassFun (dadeSubsetGroup H L B)
          (dadePullback (hD.dadeProj hBA hB) f) := by
    funext g
    rw [dadeExpansionTerm_of_mem hD f hB hBA,
      NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq]
    simp [zsmul_eq_mul]
  rw [hterm]
  exact Submodule.smul_mem _ _
    (InducedCharacterConstruction.indClassFun_mem_span_Irr
      (hD.dadePullback_mem_span_Irr hBA hB hf))

theorem IsDadeData.dadeMap_mem_span_Irr [Finite G] (hD : IsDadeData L A H) {f : ↥L → ℂ}
    (hfD : f ∈ dadeDomain L A) (hf : f ∈ Submodule.span ℤ (Irr ↥L)) :
    ((dadeMap hD ⟨f, hfD⟩ : classFun G) : G → ℂ) ∈ Submodule.span ℤ (Irr G) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨T, hT⟩ := exists_isDadeSubsetTransversal hD
  have hTfin : T.Finite := Set.toFinite _
  have hsum : (fun g => ∑ᶠ B ∈ T, dadeExpansionTerm hD f B g)
      = ∑ B ∈ hTfin.toFinset, dadeExpansionTerm hD f B := by
    funext g
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_apply]
  rw [hD.dadeMap_apply_eq_finsum_dadeExpansionTerm hT ⟨f, hfD⟩, hsum]
  refine Submodule.sum_mem _ fun B hB => ?_
  obtain ⟨hB1, hB2⟩ := mem_dadeNonemptySubsets_iff.1 (hT.subset (hTfin.mem_toFinset.1 hB))
  exact dadeExpansionTerm_mem_span_Irr hD hf hB1 hB2

theorem IsDadeData.dadeMap_mem_virtualChars [Finite G] (hD : IsDadeData L A H) {f : ↥L → ℂ}
    (hfD : f ∈ dadeDomain L A) (hf : f ∈ Submodule.span ℤ (Irr ↥L)) :
    ((dadeMap hD ⟨f, hfD⟩ : classFun G) : G → ℂ) ∈ virtualChars G :=
  span_Irr_le_virtualChars (hD.dadeMap_mem_span_Irr hfD hf)

theorem IsDadeData.dadeMap_mem_span_Irr_of_eq_zero [Finite G] (hD : IsDadeData L A H) {f : ↥L → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr ↥L)) (hf0 : ∀ x : ↥L, (x : G) ∉ A → f x = 0) :
    ((dadeMap hD ⟨f, mem_dadeDomain_of_mem_span_Irr hf hf0⟩ : classFun G) : G → ℂ)
      ∈ Submodule.span ℤ (Irr G) :=
  hD.dadeMap_mem_span_Irr _ hf

end CFSG.FeitThompson
