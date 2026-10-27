module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux

public section

namespace CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem perfectCyclicSylow_barM {M S L : Subgroup G} (hLM : L ≤ M) {p : ℕ} (hp : p.Prime)
    (hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y', Y'⁆ = Y' →
      ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A) :
    PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  have := Fact.mk hp
  intro V hV hVp A hAV hA
  have hWM : Subgroup.normalizer (S : Set G) ⊓ L ≤ M := inf_le_right.trans hLM
  obtain ⟨V', hV'W, hV'p, hV'eq⟩ := exists_perfect_le_of_le_barM hWM hV hVp
  have hV'K : V' ≤ M ⊓ Subgroup.normalizer (S : Set G) :=
    le_inf (hV'W.trans hWM) (hV'W.trans inf_le_left)
  refine isCyclic_of_le_map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (B := V'.subgroupOf M) ?_
    (hAV.trans hV'eq.symm.le) hA
  intro A' hA' hA'p
  have hc : IsCyclic (A'.map M.subtype) :=
    hcyc V' hV'K hV'p _ (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hx
      exact Subgroup.mem_subgroupOf.mp (hA' ha)) (hA'p.map _)
  exact isCyclic_of_injective
    ((Subgroup.equivMapOfInjective _ _ M.subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ M.subtype_injective).injective

omit [Finite G] in
theorem isPGroup_barM {M Y : Subgroup G} {p : ℕ} (hYp : IsPGroup p Y) : IsPGroup p (barM M Y) :=
  (hYp.comap_of_injective M.subtype M.subtype_injective).map _

omit [Finite G] in
theorem relIndex_blockCentralizer_eq {M L Y : Subgroup G} (hYM : Y ≤ M) :
    (Y ⊓ blockCentralizer M L).relIndex Y =
      (barM M Y ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex
        (barM M Y) := by
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left,
    ← Subgroup.relIndex_subgroupOf hYM]
  have h : (blockCentralizer M L).subgroupOf M =
      (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  rw [h, Subgroup.relIndex_comap]
  rfl

end CFSG.AGLEmbedding
