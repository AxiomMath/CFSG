module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFooteBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit

section

variable {G : Type*} [Group G]

theorem GSWeakReach.isInvolutionTwoComponent {J M : Subgroup G}
    (hJ : ∃ a : G, orderOf a = 2 ∧ J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (h : GSWeakReach J M) :
    ∃ b : G, orderOf b = 2 ∧ M ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) :=
  GSGrammar.Reach.vertex_right (vertex := fun J => ∃ a : G, orderOf a = 2 ∧
      J ≤ centralizer ({a} : Set G) ∧ IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    ⟨hJ, h⟩ fun _ _ b _ hC => ⟨b, hC.2.1, hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1⟩

theorem GSWeakMaximalComponent.of_weakReach {J L : Subgroup G} (hJ : GSWeakMaximalComponent J)
    (hJL : GSWeakReach J L) : GSWeakMaximalComponent L :=
  gsWeakMaximalComponent_iff_grammar.2 <| (gsWeakMaximalComponent_iff_grammar.1 hJ).of_rel
    (fun _ _ _ h₁ h₂ => GSWeakReach.trans h₁ h₂) hJL
    (GSWeakReach.isInvolutionTwoComponent hJ.1 hJL)

variable [Finite G]

theorem gsWeakMaximalComponent_of_b2Setting {a : G} {J S : Subgroup G} (h : B2Setting a J S) :
    GSWeakMaximalComponent J :=
  ⟨⟨a, h.orderOf_eq, h.le_centralizer, h.isPComponent⟩, fun _ hM => zStar_equiv_of_weakReach h hM⟩

theorem gsWeakMaximalComponent_of_B2 {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hiso : ∀ b : G, orderOf b = 2 → b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      ∃ K : Subgroup G, GSIsoCorr a J b K)
    (hcentral : ∀ (b : G) (K : Subgroup G), orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      GSIsoCorr a J b K →
      ∀ S : Subgroup G, S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
        (∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
          (P : Subgroup _) =
            S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
        b ∈ S → (∀ s ∈ S, s * b = b * s) →
        S ≤ centralizer ({b} : Set G) ⊓ normalizer (K : Set G) ∧
          ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (K : Set G)),
            (P : Subgroup _) =
              S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G))) :
    GSWeakMaximalComponent J :=
  ⟨⟨a, ha, hJa, hJ⟩, fun _ hM => zStar_equiv_of_weakReach_of_B2 ha hJa hJ hiso hcentral hM⟩

end

variable {G : Type} [Group G] [Finite G]

theorem GSWeakMaximalComponent.footeMaximal {J : Subgroup G} (h : GSWeakMaximalComponent J) :
    FooteLit.FooteMaximal J :=
  ⟨h.1, fun M hM => h.2 M (gsWeakReach_of_footeReach hM)⟩

end CFSG.ComponentClassification.GrSLit
