module

public import CFSG.ClassicalInvolution.Q3.Q3T7Exit
public import CFSG.ClassicalInvolution.Phan.Phan3D4Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TW CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Phan.Q3G CFSG.ClassicalInvolution.PhanD4
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

section Phan

variable {G : Type} [Group G]

@[expose] def D4PhanChain3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
    (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
    (∀ i j : Fin 4, edgeD 4 i j →
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j)) ∧
    ⨆ k, U k = ⊤ ∧ ¬ 3 ∣ Nat.card (Subgroup.center ↥(U 0 ⊔ U 1 ⊔ U 2))

end Phan

section Exits

variable {G : Type} [Group G] [IsSimpleGroup G]

theorem range_ι_le_closure_gens6 (F : PhanFamilyD4 K9 3 1 G) (i : Fin 4) (hi : i.val < 3) :
    (F.ι i).range ≤ Subgroup.closure (Set.range (d4Gens6 F)) := by
  rw [MonoidHom.range_eq_map, ← closure_gen2, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨⟨2 * i.val + b.val, by omega⟩, ?_⟩
  fin_cases i <;> fin_cases b <;> rfl

theorem closure_gens6_eq (F : PhanFamilyD4 K9 3 1 G) :
    Subgroup.closure (Set.range (d4Gens6 F)) =
      (F.ι 0).range ⊔ (F.ι 1).range ⊔ (F.ι 2).range := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have : ∀ j : Fin 6, d4Gens6 F j ∈
        (F.ι 0).range ⊔ (F.ι 1).range ⊔ (F.ι 2).range := by
      intro j
      fin_cases j
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, rfl⟩)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, rfl⟩)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨_, rfl⟩)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨_, rfl⟩)
      · exact Subgroup.mem_sup_right ⟨_, rfl⟩
      · exact Subgroup.mem_sup_right ⟨_, rfl⟩
    exact this j
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact range_ι_le_closure_gens6 F 0 (by decide)
    · exact range_ι_le_closure_gens6 F 1 (by decide)
    · exact range_ι_le_closure_gens6 F 2 (by decide)

theorem closure_gens_eq (F : PhanFamilyD4 K9 3 1 G) :
    Subgroup.closure (Set.range (d4Gens F)) = ⨆ i, (F.ι i).range := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_iSup_of_mem (genIdx8 j) ⟨genElt8 j, rfl⟩
  · refine iSup_le fun i => ?_
    rw [MonoidHom.range_eq_map, ← closure_gen2, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨⟨2 * i.val + b.val, by omega⟩, ?_⟩
    fin_cases i <;> fin_cases b <;> rfl

theorem conclusionD_of_d4PhanChain3
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)}
    (h : D4PhanChain3 Ω) : ConclusionD G := by
  obtain ⟨U, -, hcomm, hpair, hgen, h3⟩ := h
  obtain ⟨F, hFr, -, -⟩ := exists_family (K := K9) (p := 3) (f := 1) card_K9 U
    (fun i j h1 h2 h3 => hcomm i j h1 h2 h3) hpair
  have hsup : ⨆ i, (F.ι i).range = ⊤ := by
    rw [← hgen]
    exact iSup_congr hFr
  have hgen' : Subgroup.closure (Set.range (d4Gens F)) = ⊤ := by
    rw [closure_gens_eq, hsup]
  have h3' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (d4Gens6 F)))) := by
    rw [closure_gens6_eq, hFr 0, hFr 1, hFr 2]
    exact h3
  obtain ⟨U', hc, hp, hg⟩ := exists_ctChain_of_family hnab F h3' hgen'
    (K := GaloisField 3 1) card_gf3
  exact conclusionD_of_d4Chain3 hnab (Ω := Set.range U') ⟨U', fun k => ⟨k, rfl⟩, hc, hp, hg⟩

end Exits

end CFSG.ClassicalInvolution.Q3.Q3T7
