module

public import CFSG.LocalAnalysis.QuasithinUnique.ComponentEmbeddingAmbient

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.ComponentClassification OuterAutomorphisms

@[expose] def ComponentSchreier : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M U : Subgroup G) (z : G),
    UniqueFusionDatum T M U z → ∀ v ∈ U, v ≠ 1 →
    CFSG.oddCore (Subgroup.centralizer ({v} : Set G)) = ⊥ →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({v} : Set G)) →
      Group.IsSolvable (Outer (K ⧸ Subgroup.center K))

theorem componentEmbeddingUnderInvolution_of_schreier (h : ComponentSchreier) :
    ComponentEmbeddingUnderInvolution := by
  intro G _ _ T M U z hd v hv hv1 hcore hnorm u hu L hL
  by_cases hu1 : u = 1
  ·
    subst hu1
    refine ⟨L, ?_, le_rfl⟩
    have htop : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop, inf_top_eq] at hL
    exact hL
  · have hu2 : u ^ 2 = 1 := hd.elem.2 u hu
    have huC : u ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hd.elem.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    exact ComponentEmbedding.exists_isComponentIn_of_isComponentIn_inf_centralizer hcore huC hu1
      hu2 (fun K hK => hnorm K hK hu) (fun K hK => h G T M U z hd v hv hv1 hcore K hK) hL

end CFSG.QuasithinUnique
