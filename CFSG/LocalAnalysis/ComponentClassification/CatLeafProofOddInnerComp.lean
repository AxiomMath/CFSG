module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpCert

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.OddInner

open CFSG Subgroup

theorem not_isComponent_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G]
    (L : Subgroup G) : ¬ IsComponent L := by
  intro hL
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem oddLieCentralQuotient_of_centerQuotient_equiv {p : ℕ} {L M : Type} [Group L] [Group M]
    (e : L ⧸ center L ≃* M ⧸ center M) (h : OddLieCentralQuotient p M) :
    OddLieCentralQuotient p L := by
  obtain ⟨τ', n', f', hadm, hM⟩ := h
  exact ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hM⟩

theorem oddLie_of_isQuasisimple {G : Type} [Group G] (hG : IsQuasisimple G) {p : ℕ}
    (h : OddLieCentralQuotient p G) {L : Subgroup G} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple hG hL
  exact oddLieCentralQuotient_of_mulEquiv Subgroup.topEquiv h

theorem oddLie_of_commutator_le {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsQuasisimple S) (hSX : _root_.commutator X ≤ S) {p : ℕ}
    (h : OddLieCentralQuotient p S) {L : Subgroup X} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  obtain rfl := LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
    hS hSX hL
  exact h

theorem oddLie_prod {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {p : ℕ}
    (h₁ : ∀ M : Subgroup G₁, IsComponent M → OddLieCentralQuotient p M)
    (h₂ : ∀ M : Subgroup G₂, IsComponent M → OddLieCentralQuotient p M)
    {L : Subgroup (G₁ × G₂)} (hL : IsComponent L) : OddLieCentralQuotient p L := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    exact oddLieCentralQuotient_of_mulEquiv (MonoidHom.ofInjective hρi) (h₁ _ hρc)
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    exact oddLieCentralQuotient_of_mulEquiv (MonoidHom.ofInjective hρi) (h₂ _ hρc)

end CFSG.ComponentClassification.CatLeafProof.OddInner
