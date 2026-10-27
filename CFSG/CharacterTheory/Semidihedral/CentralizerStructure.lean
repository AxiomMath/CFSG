module

public import CFSG.CharacterTheory.Semidihedral.ReducedQuotients
public import CFSG.CharacterTheory.Semidihedral.CentralizerAlternatives

public section

namespace CFSG.Semidihedral.CentralizerStructure

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.ReducedQuotients CFSG.Semidihedral.CentralizerAlternatives

variable {G : Type*} [Group G] [Finite G]

@[expose] def StructuralAlternatives (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Prop :=
  let Γ := involutionCentralizer n S f ⧸ centralizerFullKernel n S f
  let J := reducedResidual n S f
  (n = 4 ∧ ∃ φ : Γ ≃* Equiv.Perm (Fin 4),
    J.map φ.toMonoidHom = alternatingGroup (Fin 4)) ∨
  (IsSimpleGroup (CFSG.generalizedFitting Γ) ∧
    (∃ x y : CFSG.generalizedFitting Γ, x * y ≠ y * x) ∧
    CFSG.generalizedFitting Γ ≤ J ∧
    Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥ ∧
    (∀ U : Sylow 2 (CFSG.generalizedFitting Γ),
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ n - 2 ∧ Nonempty (U ≃* DihedralGroup (2 ^ (m - 1)))) ∧
    Function.Injective (actualConjugation Γ) ∧
    (MulAut.conj : CFSG.generalizedFitting Γ →* MulAut (CFSG.generalizedFitting Γ)).range ≤
      (actualConjugation Γ).range)

theorem centered_structural_alternatives
    (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : StructuralAlternatives n S f := by
  apply generic_structural_alternatives n hn (reducedCentralizer_oddCore_eq_bot n hn S f)
    (reducedCentralizerSylow n hn S f) (reducedCentralizerDihedralEquiv n hn S f).symm
    (reducedResidual n S f) (reducedResidual_index n hn S f hG)
    (reducedResidualSylow n hn S f hG) (reducedResidualDihedralEquiv n hn S f hG).symm
  intro P _ _ hP φ
  exact reducedResidual_hom_eq_one n S f hP φ

theorem involution_centralizer_structural_alternatives
    (n : ℕ) (hn : 4 ≤ n)
    (S₀ : Sylow 2 G) (f₀ : SemidihedralGroup n ≃* S₀)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    ∀ t : G, orderOf t = 2 →
      (∃ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t) ∧
      (∀ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t →
        involutionCentralizer n S f = Subgroup.centralizer {t} ∧
        (centralInvolution n S f : G) = t ∧ StructuralAlternatives n S f) := by
  intro t ht
  obtain ⟨S, f, hz, _⟩ :=
    (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG t ht).2
  refine ⟨⟨S, f, hz⟩, ?_⟩
  intro S f hz
  refine ⟨?_, hz, centered_structural_alternatives n hn S f hG⟩
  change Subgroup.centralizer {centeredInvolution n S f} = Subgroup.centralizer {t}
  rw [hz]

end CFSG.Semidihedral.CentralizerStructure
