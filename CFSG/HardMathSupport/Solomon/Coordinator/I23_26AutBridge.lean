module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

section Bridge

variable {Y : Type*} [Group Y]

theorem isInnDiagPSL3_of_diagProp {F : Type} [Field F] [Finite F]
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))
    (A : GL (Fin 3) F) (α : MulAut Y)
    (h : ∀ (y : Y) (M M' : ↥(CFSG.Open.StatedSL 3 F)), θ (QuotientGroup.mk y) = QuotientGroup.mk M →
      (M' : GL (Fin 3) F) = A * M * A⁻¹ → θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M') :
    Lemma54Ns.IsInnDiagPSL3 α := by
  refine ⟨F, inferInstance, inferInstance, θ, MulAut.congr θ (centerDescend Y α),
    ⟨A, mem_normalizer_statedSL A, ?_⟩, fun y => (descend_apply_mk θ α y).symm⟩
  intro M M' hM'
  obtain ⟨z, hz⟩ := θ.surjective (QuotientGroup.mk M)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 := descend_apply_mk θ α y
  rw [hz] at h1
  rw [h1]
  exact h y M M' hz hM'

theorem isInnDiagPSL3_of_model {K : Type} [Field K] [Finite K]
    (ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K) {α : MulAut Y}
    (hD : MulAut.congr ε (centerDescend Y α) ∈ linearAutGroup 3 K) :
    Lemma54Ns.IsInnDiagPSL3 α := by
  rw [linearAutGroup_eq_range] at hD
  obtain ⟨A, hA⟩ := hD
  refine isInnDiagPSL3_of_diagProp (ε.trans (psiO K).symm) A α ?_
  apply diagProp_of_congr_eq_conjAut
  have : (ε.trans (psiO K).symm).trans (psiO K) = ε := by
    ext x; simp
  rw [this]
  exact hA.symm

theorem isInnDiagPSU3_of_model {p f : ℕ} {K : Type} [Field K] (hF : UnitaryFieldData p f K)
    (ε : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3) {α : MulAut Y}
    (hD : MulAut.congr ε (centerDescend Y α) ∈ (psuConj hF).range) :
    Lemma54Ns.IsInnDiagPSU3 α := by
  have hfin := hF.finite
  obtain ⟨A, hA⟩ := hD
  have hdp := diagPropU_of_congr_eq_psuConj hF (ε.trans (psuO hF)) α A (by
    have : (ε.trans (psuO hF)).trans (psuO hF).symm = ε := by
      ext x; simp
    rw [this]
    exact hA.symm)
  have hnorm : (A : GL (Fin 3) K) ∈ Subgroup.normalizer
      (unitarySU p f K 3 : Set (GL (Fin 3) K)) :=
    mem_normalizer_of_forall hF fun M =>
      ⟨⟨(A : GL (Fin 3) K) * (M : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹,
        conj_mem_unitarySU A.2 M.2⟩, rfl⟩
  refine ⟨K, inferInstance, hfin, p ^ f, ε.trans (psuO hF),
    MulAut.congr (ε.trans (psuO hF)) (centerDescend Y α), by rw [hF.card, pow_mul'],
    ⟨(A : GL (Fin 3) K), hnorm, ?_⟩, fun y => (descend_apply_mk _ α y).symm⟩
  intro M M' hM'
  obtain ⟨z, hz⟩ := (ε.trans (psuO hF)).surjective (QuotientGroup.mk M)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 := descend_apply_mk (ε.trans (psuO hF)) α y
  rw [hz] at h1
  rw [h1]
  exact hdp y M M' hz hM'

end Bridge

end CFSG.HardMathSupport.Solomon.Coordinator
