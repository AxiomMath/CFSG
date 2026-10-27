module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParEngine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParND

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Conn

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K S : Type*} [Group K] [Finite K] [Group S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

theorem diagram_connected (h : BorelQuotient D n H π M) [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) : (TauCeti.diagramGraph D.cartan).Connected := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
    · exact hb
    · obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center S := by
        rw [ht]
        exact Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab
  have hne : Nonempty (Fin D.rank) := by
    by_contra hem
    have hE : IsEmpty (Fin D.rank) := not_nonempty_iff.1 hem
    have hbot : (⨆ i, rankOne D.rootGroup i) = ⊥ := iSup_of_empty _
    have htop : (⊥ : Subgroup K) = ⊤ := by
      rw [← hbot]
      exact iSup_rankOne_eq_top h.ct h.extras
    have hK : ∀ x : K, x = 1 := by
      intro x
      have hx : x ∈ (⊥ : Subgroup K) := by
        rw [htop]
        exact Subgroup.mem_top x
      exact Subgroup.mem_bot.1 hx
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    obtain ⟨x, rfl⟩ := h.surj a
    obtain ⟨y, rfl⟩ := h.surj b
    rw [hK x, hK y]
  rw [SimpleGraph.connected_iff]
  refine ⟨fun i₀ j => ?_, hne⟩
  by_contra hj
  obtain ⟨a, ha, b, hb, hab⟩ := exists_adj_of_proper h inferInstance hZ
    (J := {k | (TauCeti.diagramGraph D.cartan).Reachable i₀ k})
    ⟨i₀, SimpleGraph.Reachable.refl i₀⟩ ⟨j, hj⟩
  have ha' : (TauCeti.diagramGraph D.cartan).Reachable i₀ a := ha
  have hadj : (TauCeti.diagramGraph D.cartan).Adj a b :=
    D.isFiniteType.diagramGraph_adj_iff.2 ⟨fun e => hb (e ▸ ha), hab⟩
  exact hb (ha'.trans hadj.reachable)

theorem diagram_isTree (h : BorelQuotient D n H π M) [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) : (TauCeti.diagramGraph D.cartan).IsTree :=
  D.isFiniteType.isTree_diagramGraph (diagram_connected h hnc)

end CFSG.AGLEmbeddingD2.Tits.GN516.Conn
