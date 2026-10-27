module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaPSL
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.Assembly.LowTwoRank

theorem congr_apply_apply {A B : Type*} [Group A] [Group B] (e : A ≃* B) (f : MulAut A) (w : A) :
    MulAut.congr e f (e w) = e (f w) := by
  simp [MulAut.congr_apply]

theorem exists_conjAut_of_isConjByGL (F : Type) [Field F]
    (φ : MulAut (StatedProj (StatedSL 3 F))) (h : LocalBalance.Lemma53Ns.IsConjByGL (StatedSL 3 F) φ) :
    ∃ A : GL (Fin 3) F, MulAut.congr (psiPSL F) φ = conjAut 3 F A := by
  obtain ⟨g, hg, hgφ⟩ := h
  refine ⟨g, ?_⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨s, rfl⟩ := proj_surjective 3 F x
  have h1 : (psiPSL F).symm (proj 3 F s) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s) := by
    rw [MulEquiv.symm_apply_eq, psiPSL_mk]
  have hmem : g * ((specialLinearGroupEquivStatedSL 3 F s : ↥(StatedSL 3 F)) : GL (Fin 3) F) *
      g⁻¹ ∈ StatedSL 3 F :=
    (Subgroup.mem_normalizer_iff.1 hg _).1 (specialLinearGroupEquivStatedSL 3 F s).2
  show psiPSL F (φ ((psiPSL F).symm (proj 3 F s))) = conjAut 3 F g (proj 3 F s)
  rw [h1]
  have key := hgφ (specialLinearGroupEquivStatedSL 3 F s) ⟨_, hmem⟩ rfl
  refine (congrArg (psiPSL F) key).trans ?_
  obtain ⟨s', hs'⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective ⟨_, hmem⟩
  rw [← hs']
  refine (psiPSL_mk F s').trans ?_
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have := congrArg (fun u : ↥(StatedSL 3 F) => ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hs'
  simpa [Units.val_mul, specialLinearGroupEquivStatedSL_coe] using this

theorem isInnDiagPSL3_eq_one {Y : Type*} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    {D H : Subgroup (MulAut Y)} (hD : IsEkIn 3 2 ⊤ D) (hH : innerAut Y ≤ H) {α : MulAut Y}
    (hα : α ∈ localDeltaIn 3 H D)
    (hinn : LocalBalance.Lemma53Ns.IsInnDiagPSL3 α) : α = 1 := by
  obtain ⟨F, _, _, θ, φ, hφ, hcomp⟩ := hinn
  obtain ⟨A, hA⟩ := exists_conjAut_of_isConjByGL F φ hφ
  let e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F := θ.trans (psiPSL F)
  refine eq_one_of_transport hperf e hD hH hα
    (φ := MulAut.congr (psiPSL F) φ) (fun y => ?_) (fun D' H' hD' hc hH' hmem => ?_)
  · exact (congrArg (psiPSL F) (hcomp y)).trans (congr_apply_apply (psiPSL F) φ _).symm
  · rw [hA] at hmem ⊢
    exact conjAut_eq_one_of_mem_localDeltaIn hD' hc hH' hmem

end CFSG.HardMathSupport.Solomon.Coordinator
