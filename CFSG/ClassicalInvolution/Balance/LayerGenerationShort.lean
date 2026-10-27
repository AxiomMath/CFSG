module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimple

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.LocalCores CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Layer

variable {Y : Type} [Group Y]

theorem le_centralizerLayer_of_isComponentOf {L Q : Subgroup Y} {f : Y} (hL : IsSubnormal L ⊤)
    (hQ : IsComponentOf Q (L ⊓ Subgroup.centralizer ({f} : Set Y))) : Q ≤ centralizerLayer f := by
  set C : Subgroup Y := Subgroup.centralizer ({f} : Set Y) with hC
  set W : Subgroup Y := L ⊓ C with hW
  have hWC : W ≤ C := inf_le_right
  have hWsub : IsSubnormal W C := by
    refine (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hWC).mp ?_
    have h := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hL C
    rwa [Subgroup.top_subgroupOf, ← Subgroup.inf_subgroupOf_right L C] at h
  have h2 := layer_map_le_of_isSubnormal hWC hWsub
  obtain ⟨hQW, hQsub, hQq⟩ := hQ
  have h1 : Q.subgroupOf W ≤ Layer.subgroup ↥W := by
    refine Layer.component_le ⟨le_top, ?_, ?_⟩
    · exact (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hQW).mpr hQsub
    · exact Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hQW) hQq
  have h3 : Q ≤ (Layer.subgroup ↥W).map W.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQW]
    exact Subgroup.map_mono h1
  exact h3.trans h2

end Layer

@[expose] def InComponentOfCentralizer {Y : Type*} [Group Y] (L R : Subgroup Y) (f : Y) : Prop :=
  ∃ Q : Subgroup Y, R ≤ Q ∧ IsComponentOf Q (L ⊓ Subgroup.centralizer ({f} : Set Y))

theorem InComponentOfCentralizer.le_centralizerLayer {Y : Type} [Group Y]
    {L R : Subgroup Y} {f : Y} (hL : IsSubnormal L ⊤) (h : InComponentOfCentralizer L R f) :
    R ≤ centralizerLayer f := by
  obtain ⟨Q, hRQ, hQ⟩ := h
  exact hRQ.trans (le_centralizerLayer_of_isComponentOf hL hQ)

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem LayerGenerationLie.of_toralSimpleRoots_components (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ g : (compModel D j).K,
          (∀ i : Fin (compModel D j).D.rank, IndexTwoCentralizes (modOdd a F₀)
            (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1))) ∧
          ∀ i : Fin (compModel D j).D.rank, ¬ IsInvolutionMember
              (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1)) →
            ∃ f ∈ modOdd a F₀, f ≠ 1 ∧
              InComponentOfCentralizer (componentHom hΩ D j).range
                (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1)) f) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralSimpleRoots hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hL hF
  obtain ⟨g, hT, hS⟩ := htor D j F₀ hL hF
  refine ⟨g, hT, fun i hnm => ?_⟩
  obtain ⟨f, hf, hf1, hcomp⟩ := hS i hnm
  exact ⟨f, hf, hf1, hcomp.le_centralizerLayer ((CFSG.isComponent_iff_open _).mp hL).2.1⟩

end Provider

end CFSG.ClassicalInvolution.Balance
