module

public import CFSG.Quasithin.Background.I4Recognition
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem nonempty_psl2_seven_equiv_projectiveSL_three_two :
    Nonempty (PSL2 (ZMod 7) ≃* projectiveSL 3 (ZMod 2)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.I4.nonempty_psl3_two_equiv_psl2_seven
  exact ⟨e.symm.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod 2))⟩

noncomputable abbrev psl2StatedEquiv (K : Type) [Field K] :
    PSL2 K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K) :=
  CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K

open scoped commutatorElement in
theorem mem_commutator_of_conj_eq_inv {G : Type*} [Group G] {σ τ : G}
    (hστ : σ * τ * σ⁻¹ = τ⁻¹) (h3 : τ ^ 3 = 1) : τ ∈ commutator G := by
  have h : ⁅σ, τ⁆ = τ := by
    rw [commutatorElement_def, hστ]
    calc τ⁻¹ * τ⁻¹ = τ⁻¹ * τ⁻¹ * τ ^ 3 := by rw [h3, mul_one]
      _ = τ := by group
  rw [← h, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ)

end CFSG.HardMathSupport.Solomon.Coordinator
