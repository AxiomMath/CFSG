module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeter

public section

namespace CFSG.AGLEmbedding.BCox

@[expose] def pdA : PairData 3 7 where
  bp := ![(0, 1), (6, 7), (8, 9)]
  acts := ![0, 1, 3, 6, 7, 8, 9]
  adj_ok := by decide
  cross_ok := by decide
  act_ok := by decide
  coord := by decide

@[expose] def pdBC : PairData 2 3 where
  bp := ![(6, 7), (8, 9)]
  acts := ![2, 6, 8]
  adj_ok := by decide
  cross_ok := by decide
  act_ok := by decide
  coord := by decide

@[expose] def pdAB : PairData 2 4 where
  bp := ![(0, 1), (6, 7)]
  acts := ![4, 10, 0, 6]
  adj_ok := by decide
  cross_ok := by decide
  act_ok := by decide
  coord := by decide

@[expose] def pdAC : PairData 2 3 where
  bp := ![(0, 1), (8, 9)]
  acts := ![5, 0, 8]
  adj_ok := by decide
  cross_ok := by decide
  act_ok := by decide
  coord := by decide

variable {G : Type} [Group G]

noncomputable abbrev modA (gs : Gens G) (hc : 2 < Nat.card G) : ModuleSpec G 3 :=
  pdA.module gs hc

noncomputable abbrev modBC (gs : Gens G) (hc : 2 < Nat.card G) : ModuleSpec G 3 :=
  pdBC.module gs hc

noncomputable abbrev modAB (gs : Gens G) (hc : 2 < Nat.card G) : ModuleSpec G 3 :=
  pdAB.module gs hc

noncomputable abbrev modAC (gs : Gens G) (hc : 2 < Nat.card G) : ModuleSpec G 3 :=
  pdAC.module gs hc

theorem modA_noFun (gs : Gens G) (hc : 2 < Nat.card G) : (modA gs hc).NoFun :=
  pdA.noFun gs hc (by decide)

@[expose] noncomputable def mods (gs : Gens G) (hc : 2 < Nat.card G) : Fin 4 → ModuleSpec G 3 :=
  ![modA gs hc, modBC gs hc, modAB gs hc, modAC gs hc]

theorem span_le (gs : Gens G) (hc : 2 < Nat.card G) (i : Fin 4) :
    (mods gs hc i).span ≤ (modA gs hc).span := by
  fin_cases i
  · exact le_rfl
  · exact pdBC.span_le gs hc pdA (by decide)
  · exact pdAB.span_le gs hc pdA (by decide)
  · exact pdAC.span_le gs hc pdA (by decide)

theorem mem_acting (gs : Gens G) (hc : 2 < Nat.card G) (m : Fin 11) :
    gs.t m ∈ ⋃ i, Set.range (mods gs hc i).g := by
  rw [Set.mem_iUnion]
  fin_cases m
  · exact ⟨0, (0 : Fin 7), rfl⟩
  · exact ⟨0, (1 : Fin 7), rfl⟩
  · exact ⟨1, (0 : Fin 3), rfl⟩
  · exact ⟨0, (2 : Fin 7), rfl⟩
  · exact ⟨2, (0 : Fin 4), rfl⟩
  · exact ⟨3, (0 : Fin 3), rfl⟩
  · exact ⟨0, (3 : Fin 7), rfl⟩
  · exact ⟨0, (4 : Fin 7), rfl⟩
  · exact ⟨0, (5 : Fin 7), rfl⟩
  · exact ⟨0, (6 : Fin 7), rfl⟩
  · exact ⟨2, (1 : Fin 4), rfl⟩

theorem closure_acting (gs : Gens G) (hc : 2 < Nat.card G) :
    Subgroup.closure (⋃ i, Set.range (mods gs hc i).g) = ⊤ := by
  rw [eq_top_iff, ← gs.gen]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨m, rfl⟩
  exact mem_acting gs hc m

end CFSG.AGLEmbedding.BCox
