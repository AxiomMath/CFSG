module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpCert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG Subgroup CFSG.Blueprint

@[expose] def Psl2CQ (ℓ : ℕ) (M : Type) [Group M] : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ LieModel (M ⧸ center M) .PSL 2 ℓ j

theorem Psl2CQ.of_mulEquiv {ℓ : ℕ} {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : Psl2CQ ℓ L') : Psl2CQ ℓ L := by
  obtain ⟨j, hj, hL⟩ := h
  exact ⟨j, hj, LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hL⟩

theorem Psl2CQ.of_centerQuotient_equiv {ℓ : ℕ} {L M : Type} [Group L] [Group M]
    (e : L ⧸ center L ≃* M ⧸ center M) (h : Psl2CQ ℓ M) : Psl2CQ ℓ L := by
  obtain ⟨j, hj, hM⟩ := h
  exact ⟨j, hj, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hM⟩

theorem psl2CQ_of_component_equiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y) {ℓ : ℕ}
    (h : ∀ M : Subgroup Y, IsComponent M → Psl2CQ ℓ M) {L : Subgroup X} (hL : IsComponent L) :
    Psl2CQ ℓ L :=
  Psl2CQ.of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (h _ (LocalCores.isComponent_map_mulEquiv Φ hL))

theorem psl2CQ_of_isQuasisimple {G : Type} [Group G] (hG : IsQuasisimple G) {ℓ : ℕ}
    (h : Psl2CQ ℓ G) {L : Subgroup G} (hL : IsComponent L) : Psl2CQ ℓ L := by
  obtain rfl := CFSG.ComponentClassification.OddClassSelector.eq_top_of_isComponent_of_quasisimple
    hG hL
  exact Psl2CQ.of_mulEquiv Subgroup.topEquiv h

theorem psl2CQ_of_commutator_le {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsQuasisimple S) (hSX : _root_.commutator X ≤ S) {ℓ : ℕ} (h : Psl2CQ ℓ S)
    {L : Subgroup X} (hL : IsComponent L) : Psl2CQ ℓ L := by
  obtain rfl := LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
    hS hSX hL
  exact h

theorem psl2CQ_prod {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {ℓ : ℕ}
    (h₁ : ∀ M : Subgroup G₁, IsComponent M → Psl2CQ ℓ M)
    (h₂ : ∀ M : Subgroup G₂, IsComponent M → Psl2CQ ℓ M) {L : Subgroup (G₁ × G₂)}
    (hL : IsComponent L) : Psl2CQ ℓ L := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ :=
      CFSG.ComponentClassification.OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    exact Psl2CQ.of_mulEquiv (MonoidHom.ofInjective hρi) (h₁ _ hρc)
  · obtain ⟨ρ, hρi, hρc, -⟩ :=
      CFSG.ComponentClassification.OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    exact Psl2CQ.of_mulEquiv (MonoidHom.ofInjective hρi) (h₂ _ hρc)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
