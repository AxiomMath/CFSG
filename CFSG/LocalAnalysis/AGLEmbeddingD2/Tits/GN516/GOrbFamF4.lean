module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistLevi
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.CurtisTits CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_sl3_range (κ : F4A2Kind) :
    ∃ l : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup Tag.F4 K), Function.Injective l ∧
      l.range = rankOne (f4Datum K).rootGroup κ.i ⊔ rankOne (f4Datum K).rootGroup κ.j := by
  have hSle : subsystemGroup Tag.F4 K {κ.i, κ.j} ≤ adjointGroup Tag.F4 K := by
    rw [subsystemGroup, Subgroup.closure_le]
    rintro g ⟨k, -, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup k c
    · exact yUnit_mem_adjointGroup k c
  obtain ⟨l, hl⟩ : ∃ l : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup Tag.F4 K),
      l = (Subgroup.inclusion hSle).comp (f4A2Equiv K κ).symm.toMonoidHom := ⟨_, rfl⟩
  have hl_inj : Function.Injective l := by
    subst hl
    exact (Subgroup.inclusion_injective hSle).comp (f4A2Equiv K κ).symm.injective
  have hlapp : ∀ s, ((l s : ↥(adjointGroup Tag.F4 K)) : ModGL Tag.F4 K) =
      (((f4A2Equiv K κ).symm s : ↥(subsystemGroup Tag.F4 K {κ.i, κ.j})) : ModGL Tag.F4 K) := by
    intro s
    subst hl
    rfl
  have hxP : ∀ (k : Fin Tag.F4.rank) (c : K),
      xPar (rootOperatorFamily Tag.F4) (Pi.single k 1) c = xElement k c := by
    intro k c
    rw [xPar_simple, eltElement_simpleRoot]
  have hyP : ∀ (k : Fin Tag.F4.rank) (c : K),
      xPar (rootOperatorFamily Tag.F4) (-Pi.single k 1) c = yElement k c := by
    intro k c
    rw [xPar_neg_simple]
    exact Subtype.ext ((rootOperatorFamily Tag.F4).eltUnit_neg_simple k c)
  set J := rankOne (f4Datum K).rootGroup κ.i ⊔ rankOne (f4Datum K).rootGroup κ.j with hJ
  have hgenJ : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)), ∀ c : K,
      xElement k c ∈ J ∧ yElement k c ∈ J := by
    intro k hk c
    have hkJ : rankOne (f4Datum K).rootGroup k ≤ J := by
      rcases hk with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    have hx : xElement k c ∈ rankOne (f4Datum K).rootGroup k := by
      rw [← hxP k c]
      exact xPar_single_mem_rankOne (F := rootOperatorFamily Tag.F4) k c
    have hy : yElement k c ∈ rankOne (f4Datum K).rootGroup k := by
      rw [← hyP k c]
      exact xPar_neg_single_mem_rankOne (F := rootOperatorFamily Tag.F4) k c
    exact ⟨hkJ hx, hkJ hy⟩
  have hle : subsystemGroup Tag.F4 K {κ.i, κ.j} ≤ J.map (adjointGroup Tag.F4 K).subtype := by
    rw [subsystemGroup, Subgroup.closure_le]
    rintro g ⟨k, hk, c, rfl | rfl⟩
    · exact ⟨xElement k c, (hgenJ k hk c).1, rfl⟩
    · exact ⟨yElement k c, (hgenJ k hk c).2, rfl⟩
  have hlle : l.range ≤ J := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨j, hj, hjg⟩ := hle ((f4A2Equiv K κ).symm s).2
    have hjl : j = l s := Subtype.ext (hjg.trans (hlapp s).symm)
    rw [← hjl]
    exact hj
  have hgenS : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)), ∀ c : K,
      xElement k c ∈ l.range ∧ yElement k c ∈ l.range := by
    intro k hk c
    have hx : ((xElement k c : ↥(adjointGroup Tag.F4 K)) : ModGL Tag.F4 K) ∈
        subsystemGroup Tag.F4 K {κ.i, κ.j} :=
      Subgroup.subset_closure ⟨k, hk, c, Or.inl rfl⟩
    have hy : ((yElement k c : ↥(adjointGroup Tag.F4 K)) : ModGL Tag.F4 K) ∈
        subsystemGroup Tag.F4 K {κ.i, κ.j} :=
      Subgroup.subset_closure ⟨k, hk, c, Or.inr rfl⟩
    obtain ⟨s, hs⟩ := (f4A2Equiv K κ).symm.surjective ⟨_, hx⟩
    obtain ⟨t, ht⟩ := (f4A2Equiv K κ).symm.surjective ⟨_, hy⟩
    exact ⟨MonoidHom.mem_range.2 ⟨s, Subtype.ext ((hlapp s).trans (congrArg Subtype.val hs))⟩,
      MonoidHom.mem_range.2 ⟨t, Subtype.ext ((hlapp t).trans (congrArg Subtype.val ht))⟩⟩
  have hsub : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      rankOne (f4Datum K).rootGroup k ≤ l.range := by
    intro k hk
    unfold CFSG.LieType.CurtisTits.rankOne
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily Tag.F4)
        (isRoot_single Tag.F4 k) _).1 hg
      rw [hxP k c]
      exact (hgenS k hk c).1
    · intro g hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily Tag.F4)
        (isRoot_neg_single Tag.F4 k) _).1 hg
      rw [hyP k c]
      exact (hgenS k hk c).2
  refine ⟨l, hl_inj, le_antisymm hlle ?_⟩
  exact sup_le (hsub κ.i (Set.mem_insert _ _))
    (hsub κ.j (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem edgeLevi_f4A2 (κ : F4A2Kind) :
    Edge.EdgeLevi (f4Datum K) κ.i κ.j := by
  obtain ⟨l, hl, hr⟩ := exists_sl3_range (K := K) κ
  exact EdgeLev.edgeLevi_of_sl3 l hl hr

theorem edgeLevi_f4B2 : Edge.EdgeLevi (f4Datum K) 1 2 := by
  refine EdgeLev.edgeLevi_of_sp4 (CFSG.SeitzReduction.F4Pilot.b2LeviHom K)
    CFSG.SeitzReduction.F4Pilot.b2LeviHom_injective ?_
  rw [CFSG.SeitzReduction.F4Pilot.range_b2LeviHom, ← CFSG.SeitzReduction.F4Pilot.levi_one_two_eq_B2Levi,
    CFSG.SeitzReduction.F4Pilot.levi_pair, levi_singleton, levi_singleton]

theorem f4_edge_of_adj : ∀ u v : Fin 4, u ≠ v → (Tag.cartan .F4 u v : ℤ) ≠ 0 →
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide

theorem edgeCond_f4
    (H : Fin (f4Datum K).rank → Subgroup ↥(adjointGroup .F4 K)) (hrank : 3 ≤ (f4Datum K).rank)
    (u v : Fin (f4Datum K).rank) (hadj : (TauCeti.diagramGraph (f4Datum K).cartan).Adj u v) :
    Core.EdgeCond (f4Datum K) H u v := by
  have hne := (f4Datum K).isFiniteType.diagramGraph_adj_iff.1 hadj
  unfold Core.EdgeCond
  refine Or.inl ?_
  rcases f4_edge_of_adj u v hne.1 hne.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact edgeLevi_f4A2 F4A2Kind.long
  · exact EdgeLev.edgeLevi_symm (edgeLevi_f4A2 F4A2Kind.long)
  · exact edgeLevi_f4B2
  · exact EdgeLev.edgeLevi_symm edgeLevi_f4B2
  · exact edgeLevi_f4A2 F4A2Kind.short
  · exact EdgeLev.edgeLevi_symm (edgeLevi_f4A2 F4A2Kind.short)

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
