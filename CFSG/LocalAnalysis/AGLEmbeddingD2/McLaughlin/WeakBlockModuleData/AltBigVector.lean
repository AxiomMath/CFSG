module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.McLaughlin
open scoped commutatorElement

section Hom

variable {G : Type} [Group G]

@[expose] def barMHom {M L : Subgroup G} (hLM : L ≤ M) : ↥L →* ↥(barM M L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM : ↥L →* ↥M)).codRestrict
    (barM M L) (fun l => by
      simp only [barM, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.mem_map,
        Subgroup.mem_subgroupOf]
      exact ⟨⟨l, hLM l.2⟩, l.2, rfl⟩)

theorem barMHom_apply {M L : Subgroup G} (hLM : L ≤ M) (l : ↥L) :
    ((barMHom hLM l : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM l.2⟩ := rfl

theorem barMHom_surjective {M L : Subgroup G} (hLM : L ≤ M) :
    Function.Surjective (barMHom hLM) := by
  rintro ⟨z, hz⟩
  simp only [barM, Subgroup.mem_map, Subgroup.mem_subgroupOf] at hz
  obtain ⟨m, hm, rfl⟩ := hz
  exact ⟨⟨m, hm⟩, Subtype.ext rfl⟩

end Hom

theorem rankDropModel_of_altPermSubImage {Γ W : Type*} [Group Γ] [MulAction Γ W] {N : ℕ}
    (hN : 5 ≤ N) (h : IsAltPermSubImage Γ W N) [Finite Γ] : RankDropModel Γ W := by
  obtain ⟨e, X, π, hπ, hequiv⟩ := h
  intro w
  obtain ⟨f, hfX, rfl⟩ := hπ w
  obtain ⟨E, k, hE, hcard, hfix, hrank⟩ := rankDropModel_altPerm hN f
  refine ⟨E.map e.toMonoidHom, k, elementary_map_injective 3 E e.toMonoidHom e.injective hE,
    ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · rintro _ ⟨g, hg, rfl⟩
    have := hequiv g f hfX
    rw [hfix g hg] at this
    exact this.symm
  · have := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
    rw [← this]
    exact hrank

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
