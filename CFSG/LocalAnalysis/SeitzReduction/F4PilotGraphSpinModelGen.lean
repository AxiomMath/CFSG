module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2B2
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusEmbed

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective elt mat_elt E)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed suppGroup mem_suppGroup
  range_spEmbed)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

variable {K : Type} [Field K]

theorem sp_x_single_one (c : K) :
    Sp.x 3 K (Pi.single 1 1) c = elt (.difference 1 2 (by decide)) c :=
  Sp.x_eq (by decide) c

theorem sp_x_neg_single_one (c : K) :
    Sp.x 3 K (-Pi.single 1 1) c = elt (.difference 2 1 (by decide)) c :=
  Sp.x_eq (by decide) c

theorem sp_x_single_two (c : K) : Sp.x 3 K (Pi.single 2 1) c = elt (.positiveLong 2) c :=
  Sp.x_eq (by decide) c

theorem sp_x_neg_single_two (c : K) : Sp.x 3 K (-Pi.single 2 1) c = elt (.negativeLong 2) c :=
  Sp.x_eq (by decide) c

theorem mat_sp_x_single_one (c : K) :
    mat 3 K (Sp.x 3 K (Pi.single 1 1) c) =
      1 + c • (single (.inl 1) (.inl 2) 1 - single (.inr 2) (.inr 1) 1) := by
  rw [sp_x_single_one, mat_elt]
  rfl

theorem mat_sp_x_neg_single_one (c : K) :
    mat 3 K (Sp.x 3 K (-Pi.single 1 1) c) =
      1 + c • (single (.inl 2) (.inl 1) 1 - single (.inr 1) (.inr 2) 1) := by
  rw [sp_x_neg_single_one, mat_elt]
  rfl

theorem mat_sp_x_single_two (c : K) :
    mat 3 K (Sp.x 3 K (Pi.single 2 1) c) = 1 + c • single (.inl 2) (.inr 2) 1 := by
  rw [sp_x_single_two, mat_elt]
  rfl

theorem mat_sp_x_neg_single_two (c : K) :
    mat 3 K (Sp.x 3 K (-Pi.single 2 1) c) = 1 + c • single (.inr 2) (.inl 2) 1 := by
  rw [sp_x_neg_single_two, mat_elt]
  rfl

variable (K) in
@[expose] def sp4Gens : Set (StatedSp 3 K) :=
  {g | ∃ c : K, Sp.x 3 K (Pi.single 1 1) c = g ∨ Sp.x 3 K (-Pi.single 1 1) c = g ∨
    Sp.x 3 K (Pi.single 2 1) c = g ∨ Sp.x 3 K (-Pi.single 2 1) c = g}

theorem range_spEmbed_succ_le_closure_sp4Gens :
    (spEmbed (K := K) (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)).range ≤
      closure (sp4Gens K) := by
  set H := (closure (sp4Gens K)).comap
    (spEmbed (K := K) (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)) with hH
  have htop : H = ⊤ := by
    refine SymplecticPilot.eq_top_of_adjacent_of_long_statedSp H 1 ?_ ?_ ?_
    · intro i j hij c hadj
      rw [hH, mem_comap, spEmbed_elt]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact subset_closure ⟨c, .inl (sp_x_single_one c)⟩
      · exact subset_closure ⟨c, .inr (.inl (sp_x_neg_single_one c))⟩
      · exact absurd rfl hij
    · intro c
      rw [hH, mem_comap, spEmbed_elt]
      exact subset_closure ⟨c, .inr (.inr (.inl (sp_x_single_two c)))⟩
    · intro c
      rw [hH, mem_comap, spEmbed_elt]
      exact subset_closure ⟨c, .inr (.inr (.inr (sp_x_neg_single_two c)))⟩
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ H := by
    rw [htop]
    exact mem_top g
  exact hg

theorem mem_range_succ_of_sp6ToSLIdx_mem :
    ∀ r : Fin 3 ⊕ Fin 3, sp6ToSLIdx r ∈ lin6BlockA →
      r ∈ Set.range (Sum.map (Fin.succ : Fin 2 → Fin 3) Fin.succ) := by
  intro r hr
  rcases r with r | r <;> fin_cases r
  · exact absurd hr (by decide)
  · exact ⟨.inl 0, rfl⟩
  · exact ⟨.inl 1, rfl⟩
  · exact absurd hr (by decide)
  · exact ⟨.inr 0, rfl⟩
  · exact ⟨.inr 1, rfl⟩

theorem coe_sp6ToSL6_apply (s : StatedSp 3 K) (r t : Fin 3 ⊕ Fin 3) :
    (sp6ToSL6 s : Matrix (Fin 6) (Fin 6) K) (sp6ToSLIdx r) (sp6ToSLIdx t) = mat 3 K s r t := by
  rw [coe_sp6ToSL6, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem mem_suppGroup_of_sp6ToSL6_mem {s : StatedSp 3 K}
    (hs : sp6ToSL6 s ∈ blockSpecialLinear (K := K) lin6BlockA) :
    s ∈ suppGroup (Set.range (Sum.map (Fin.succ : Fin 2 → Fin 3) Fin.succ)) := by
  rw [mem_suppGroup]
  intro r t hrt
  have h := (mem_blockSpecialLinear.1 hs) (sp6ToSLIdx r) (sp6ToSLIdx t) (by
    by_contra hne
    push Not at hne
    exact hrt ⟨mem_range_succ_of_sp6ToSLIdx_mem r hne.1,
      mem_range_succ_of_sp6ToSLIdx_mem t hne.2⟩)
  rw [coe_sp6ToSL6_apply] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  simp only [sp6ToSLIdx.injective.eq_iff]

theorem mem_closure_sp4Gens_of_sp6ToSL6_mem {s : StatedSp 3 K}
    (hs : sp6ToSL6 s ∈ blockSpecialLinear (K := K) lin6BlockA) : s ∈ closure (sp4Gens K) := by
  apply range_spEmbed_succ_le_closure_sp4Gens
  rw [range_spEmbed]
  exact mem_suppGroup_of_sp6ToSL6_mem hs

end CFSG.SeitzReduction.F4Pilot
