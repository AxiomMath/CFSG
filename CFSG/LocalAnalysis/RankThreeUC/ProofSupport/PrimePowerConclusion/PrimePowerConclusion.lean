module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOperatorPrime.OddOperatorPrime
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleImageReduction.IrreducibleImageReduction
public import CFSG.GroupTheory.CoprimeActionSupport.ShultPrimeGeneratedGroupConclusion

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimePowerConclusion

theorem conclusion {G : Type} [Group G] [Finite G] {p : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}
    (hS : CFSG.LocalAnalysis.RankThreeUC.FaithfulPrimeFieldKGroupModule G p V ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule (ZMod p) V))
    (Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) (hQ1 : Q ≠ ⊥) (hQq : IsPGroup q Q) :
    q = 2 ∧ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hr2 : r ≠ 2 :=
    CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOperatorPrime.ne_two hS hq hr hqp hrp hqr D hD hCV Q hQD hQ1 hQq
  obtain ⟨H, _, _, W, _, _, _, _, τ, hfaith, hirr, E, D', hE1, hEq, hD', hDE, hsup, hCV',
    hqF, hrF, hHF⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleImageReduction.exists_image hS hq hr hqp hrp hqr D hD hCV
      Q hQD hQ1 hQq
  exact CFSG.GroupTheory.CoprimeActionSupport.ShultPrimeGeneratedGroupConclusion.conclusion τ hfaith hirr hq hr hr2
    hqr D' E hE1 hEq hD' hDE hsup hCV' hqF hrF hHF

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimePowerConclusion
