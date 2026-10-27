module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixIsoCheck
public import CFSG.Sporadic.SmallOddCore.HeLocal
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.PSL3Four
  CFSG.GH74.KGroups CFSG.Assembly.LowTwoRank

@[expose] def heldFixG (i : ℕ) : Equiv.Perm (Fin 42) := [g₁, g₂, g₃].getD i 1

theorem tabRep_gensS : ∀ i < gensS.size, TabRep gensS[i]! (heldFixG i) := by
  intro i hi
  have hi' : i < 3 := hi
  interval_cases i
  · exact tabRep_g₁
  · exact tabRep_g₂
  · exact tabRep_g₃

theorem heldFixG_mem {i : ℕ} (hi : i < 3) : heldFixG i ∈ S := by
  interval_cases i
  · exact g₁_mem_S
  · exact g₂_mem_S
  · exact g₃_mem_S

@[expose] def heldFixX (i : ℕ) : Equiv.Perm (Fin 105) :=
  ((heldFixXWords.getD i []).map heDPerm).prod

@[expose] def heldFixS (j : ℕ) : Equiv.Perm (Fin 42) :=
  ((heldFixSWords.getD j []).map heldFixG).prod

@[expose] def heldFixPair (k : ℕ) : Equiv.Perm (Fin 105) × Equiv.Perm (Fin 42) :=
  if k < 5 then (heDPerm k, heldFixS k) else (heldFixX (k - 5), heldFixG (k - 5))

@[expose] def heldFixPairs : Set (Equiv.Perm (Fin 105) × Equiv.Perm (Fin 42)) :=
  {p | ∃ k < 8, heldFixPair k = p}

theorem heDGens_size : heDGens.size = 5 := by simp [heDGens]

theorem heldFixGraphGens_size : heldFixGraphGens.size = 8 := by simp [heldFixGraphGens]

theorem tabRep_heldFixGraphGens : ∀ k < heldFixGraphGens.size,
    TabRep heldFixGraphGens[k]! (blockHom 105 42 (heldFixPair k)) := by
  intro k hk
  have hk8 : k < 8 := heldFixGraphGens_size ▸ hk
  rw [heldFixGraphGens, getElem!_pos _ k (by simpa using hk8), Array.getElem_ofFn]
  simp only [heldFixPair]
  by_cases h5 : k < 5
  · simp only [h5, ↓reduceIte]
    exact tabRep_catTab (tabRep_heDGens k (heDGens_size ▸ h5))
      (tabRep_wordTabS tabRep_gensS _ fun i hi => heldFix_words_lt.2 k h5 i hi)
  · simp only [h5, ↓reduceIte]
    exact tabRep_catTab (tabRep_wordTabS tabRep_heDGens _ fun j hj =>
        heDGens_size ▸ heldFix_words_lt.1 (k - 5) (by omega) j hj)
      (tabRep_gensS (k - 5) (show k - 5 < 3 by omega))

theorem card_heldFix_graph :
    Nat.card (Subgroup.closure (blockHom 105 42 '' heldFixPairs)) = 20160 := by
  have hset : blockHom 105 42 '' heldFixPairs =
      {g | ∃ k < heldFixGraphGens.size, blockHom 105 42 (heldFixPair k) = g} := by
    ext g
    simp only [heldFixPairs, Set.mem_image, Set.mem_ofPred_eq, heldFixGraphGens_size]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [hset, (enumerates_closure (genGroup_hA tabRep_heldFixGraphGens)
    (genGroup_hgens tabRep_heldFixGraphGens) heldFix_graph_check.1).card, Array.length_toList,
    heldFix_graph_check.2]

theorem heldFixX_mem {i : ℕ} (hi : i < 3) : heldFixX i ∈ genGroup 105 heDGens heDPerm := by
  refine (genGroup 105 heDGens heDPerm).list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨j, heDGens_size ▸ heldFix_words_lt.1 i hi j hj, rfl⟩

theorem heldFixS_mem {j : ℕ} (hj : j < 5) : heldFixS j ∈ S := by
  refine S.list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact heldFixG_mem (heldFix_words_lt.2 j hj i hi)

theorem closure_fst_heldFixPairs :
    Subgroup.closure (Prod.fst '' heldFixPairs) = genGroup 105 heDGens heDPerm := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    simp only [heldFixPair]
    split_ifs with h5
    · exact Subgroup.subset_closure ⟨k, heDGens_size ▸ h5, rfl⟩
    · exact heldFixX_mem (by omega)
  · apply Subgroup.closure_mono
    rintro _ ⟨j, hj, rfl⟩
    have hj5 : j < 5 := heDGens_size ▸ hj
    exact ⟨heldFixPair j, ⟨j, by omega, rfl⟩, by simp [heldFixPair, hj5]⟩

theorem closure_snd_heldFixPairs : Subgroup.closure (Prod.snd '' heldFixPairs) = S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    simp only [heldFixPair]
    split_ifs with h5
    · exact heldFixS_mem h5
    · exact heldFixG_mem (by omega)
  · rw [S]
    apply Subgroup.closure_mono
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨heldFixPair 5, ⟨5, by norm_num, rfl⟩, rfl⟩
    · exact ⟨heldFixPair 6, ⟨6, by norm_num, rfl⟩, rfl⟩
    · exact ⟨heldFixPair 7, ⟨7, by norm_num, rfl⟩, rfl⟩

theorem nonempty_heD_equiv_S : Nonempty (genGroup 105 heDGens heDPerm ≃* S) :=
  nonempty_mulEquiv_of_graph closure_fst_heldFixPairs closure_snd_heldFixPairs
    (by rw [card_heldFix_graph, heD_facts.2.1]) (by rw [card_heldFix_graph, card_S])

theorem statedClassicalModel_heD :
    StatedClassicalModel (genGroup 105 heDGens heDPerm) .PSL 3 2 2 := by
  obtain ⟨e⟩ := nonempty_heD_equiv_S
  exact ⟨admissible, F4, inferInstance, inferInstance, natCard_F4', ⟨e.trans equivStated⟩⟩

end CFSG.ComponentClassification.GrSLit.HeldFix
