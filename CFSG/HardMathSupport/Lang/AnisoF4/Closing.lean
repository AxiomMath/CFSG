module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4B4
public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


@[expose] def f4Delta : Fin (Tag.rank .F4) → ℤ := ![1, 2, 3, 1]

theorem isRoot_f4Delta : IsRoot .F4 f4Delta := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

theorem reflect_word_f4Delta :
    reflect .F4 (f4Node 2) (reflect .F4 (f4Node 1) (reflect .F4 (f4Node 2)
      (reflect .F4 (f4Node 0) (reflect .F4 (f4Node 1) (reflect .F4 (f4Node 2) f4Delta))))) =
      Pi.single (f4Node 3) 1 := by
  decide

variable {K : Type} [Field K]

abbrev rootPairF4 (K : Type) [Field K] (γ : Fin (Tag.rank .F4) → ℤ) :
    Subgroup (adjointGroup .F4 K) :=
  (f4Datum K).rootGroup γ ⊔ (f4Datum K).rootGroup (-γ)

theorem rootPairF4_reflect_le {M : Subgroup (adjointGroup .F4 K)} (i : Fin (Tag.rank .F4))
    (hn : Chevalley.weylElement .F4 K i ∈ M) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (h : rootPairF4 K γ ≤ M) : rootPairF4 K (reflect .F4 i γ) ≤ M := by
  rw [rootPairF4, ← map_conj_weylElement_rootPair_F4 i hγ]
  rintro _ ⟨y, hy, rfl⟩
  exact M.mul_mem (M.mul_mem hn (h hy)) (M.inv_mem hn)

theorem eq_top_of_b4Chain_le_of_delta_le (M : Subgroup (adjointGroup .F4 K))
    (hX : ⨆ k, b4Chain K k ≤ M) (hδ : rootPairF4 K f4Delta ≤ M) : M = ⊤ := by
  have hb : ∀ k, b4Chain K k ≤ M := fun k => (le_iSup (b4Chain K) k).trans hX
  have hr0 : rankOne (f4Datum K).rootGroup (f4Node 0) ≤ M := hb 1
  have hr1 : rankOne (f4Datum K).rootGroup (f4Node 1) ≤ M := hb 2
  have hr2 : rankOne (f4Datum K).rootGroup (f4Node 2) ≤ M := hb 3
  have hn : ∀ i : Fin (Tag.rank .F4), rankOne (f4Datum K).rootGroup i ≤ M →
      Chevalley.weylElement .F4 K i ∈ M := fun i hi =>
    hi (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .F4) i)
  have h1 := isRoot_f4Delta
  have h2 := IsRoot.reflect (f4Node 2) h1
  have h3 := IsRoot.reflect (f4Node 1) h2
  have h4 := IsRoot.reflect (f4Node 0) h3
  have h5 := IsRoot.reflect (f4Node 2) h4
  have h6 := IsRoot.reflect (f4Node 1) h5
  have s1 := rootPairF4_reflect_le (f4Node 2) (hn _ hr2) h1 hδ
  have s2 := rootPairF4_reflect_le (f4Node 1) (hn _ hr1) h2 s1
  have s3 := rootPairF4_reflect_le (f4Node 0) (hn _ hr0) h3 s2
  have s4 := rootPairF4_reflect_le (f4Node 2) (hn _ hr2) h4 s3
  have s5 := rootPairF4_reflect_le (f4Node 1) (hn _ hr1) h5 s4
  have s6 := rootPairF4_reflect_le (f4Node 2) (hn _ hr2) h6 s5
  rw [reflect_word_f4Delta] at s6
  have hr3 : rankOne (f4Datum K).rootGroup (f4Node 3) ≤ M := s6
  have hall : ⨆ i, rankOne (f4Datum K).rootGroup i ≤ M := by
    refine iSup_le fun i => ?_
    fin_cases i
    · exact hr0
    · exact hr1
    · exact hr2
    · exact hr3
  rw [CFSG.ClassicalInvolution.RouteD.iSup_rankOne_eq_top (f4_isCTGroupDatum K)] at hall
  exact eq_top_iff.2 hall

end CFSG.HardMathSupport.Lang.AnisoF4
