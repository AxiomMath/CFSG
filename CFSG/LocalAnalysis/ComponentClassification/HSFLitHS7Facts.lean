module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Inner

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def HS7OddLieFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Blueprint.OddLieType X → ∀ t : X, orderOf t = 2 → ∀ L : Subgroup X,
      L ≤ centralizer ({t} : Set X) → IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) →
      ¬ Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7))

@[expose] def HS7OuterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup ↥(generalizedFitting G) →
    Blueprint.Catalog ↥(generalizedFitting G) →
    ∀ t : G, orderOf t = 2 → t ∉ generalizedFitting G → ∀ L : Subgroup G,
      L ≤ centralizer ({t} : Set G) → IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))) →
      Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7)) →
      (∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L))) →
      Nonempty (↥(generalizedFitting G) ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (↥(generalizedFitting G) ≃* Blueprint.NativeSporadic.He)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem catalog_generalizedFitting_of_kProper (hKP : Assembly.KProper Blueprint.Catalog G)
    (hF : IsSimpleGroup ↥(generalizedFitting G))
    (hnab : ∃ a b : ↥(generalizedFitting G), a * b ≠ b * a) (hne : generalizedFitting G ≠ ⊤) :
    Blueprint.Catalog ↥(generalizedFitting G) :=
  UnbalancingLocal.catalog_of_kProper_of_surjective
    (fun e h => (SectionRank.catalog_congr e).mpr h) hKP _ hne hnab (MonoidHom.id _)
    Function.surjective_id

theorem harrisSolomonA7_of_facts (hHSF : GSLit.HarrisSolomonFritzA7Input)
    (hF1 : HS7OddLieFact) (hF2 : HS7OuterFact) (hKP : Assembly.KProper Blueprint.Catalog G)
    (hF : IsSimpleGroup ↥(generalizedFitting G)) {t : G} (ht : orderOf t = 2) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7)))
    (hcyc : ∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L))) :
    Nonempty (↥(generalizedFitting G) ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (↥(generalizedFitting G) ≃* Blueprint.NativeSporadic.He) := by
  have hnab := generalizedFitting_nonabelian hF h7
  by_cases htF : t ∈ generalizedFitting G
  · exfalso
    have hodd := oddLieType_of_mem hHSF hF ht htF hLt hL h7 hcyc
    have hLN := le_generalizedFitting hF hnab ht hLt hL
    let t' : ↥(generalizedFitting G) := ⟨t, htF⟩
    have ht' : orderOf t' = 2 := by rw [orderOf_mk]; exact ht
    exact hF1 _ hnab hodd t' ht' (L.subgroupOf (generalizedFitting G))
      (le_centralizer_restrict (t := t') hLt) (isPComponent_restrict (t := t') hLN hLt hL)
      (nonempty_oddBar_restrict hLN h7)
  · have hne : generalizedFitting G ≠ ⊤ := fun h => htF (h ▸ mem_top t)
    exact hF2 G hF (catalog_generalizedFitting_of_kProper hKP hF hnab hne) t ht htF L hLt hL h7
      hcyc

end CFSG.ComponentClassification.HSFLit.HS7
