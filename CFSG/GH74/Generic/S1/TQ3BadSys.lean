module

public import CFSG.GH74.Generic.S1.TQ3BadCfg

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

section System

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

namespace Q3FrameB

variable (Fr : Q3FrameB G F)

@[expose] noncomputable def symJB : Fin 4 → Subgroup G
  | 0 => (blkLin (F := F) 3 0).map (Fr.D 2).ι
  | 1 => (blkLin (F := F) 0 1).map (Fr.D 4).ι
  | 2 => (blkLin (F := F) 1 2).map (Fr.D 4).ι
  | 3 => (blkLin (F := F) 2 3).map (Fr.D 4).ι

omit [Finite F] in
theorem symJB_zero : Fr.symJB 0 = (blkLin (F := F) 3 0).map (Fr.D 2).ι := rfl

omit [Finite F] in
theorem symJB_one : Fr.symJB 1 = (blkLin (F := F) 0 1).map (Fr.D 4).ι := rfl

omit [Finite F] in
theorem symJB_two : Fr.symJB 2 = (blkLin (F := F) 1 2).map (Fr.D 4).ι := rfl

omit [Finite F] in
theorem symJB_three : Fr.symJB 3 = (blkLin (F := F) 2 3).map (Fr.D 4).ι := rfl

theorem J0_layer3 (hF3 : Nat.card F = 3) :
    Fr.symJB 0 = (blkLin (F := F) 3 0).map (Fr.D 3).ι :=
  Fr.blk_eq_of_layers hF3 (e := 2) (f := 3) (a := 3) (b := 0) (c := 2) (d := 1) (a' := 3)
    (b' := 0) (c' := 2) (d' := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem J0_layer1 (hF3 : Nat.card F = 3) :
    Fr.symJB 0 = (blkLin (F := F) 3 0).map (Fr.D 1).ι :=
  Fr.blk_eq_of_layers hF3 (e := 2) (f := 1) (a := 3) (b := 0) (c := 1) (d := 2) (a' := 3)
    (b' := 0) (c' := 1) (d' := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem J1_layer2 (hF3 : Nat.card F = 3) :
    Fr.symJB 1 = (blkLin (F := F) 0 1).map (Fr.D 2).ι :=
  (Fr.blk_eq_of_layers hF3 (e := 2) (f := 4) (a := 0) (b := 1) (c := 3) (d := 2) (a' := 0)
    (b' := 1) (c' := 2) (d' := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).symm

theorem J2_layer3 (hF3 : Nat.card F = 3) :
    Fr.symJB 2 = (blkLin (F := F) 1 2).map (Fr.D 3).ι :=
  Fr.blk_eq_of_layers hF3 (e := 4) (f := 3) (a := 1) (b := 2) (c := 3) (d := 0) (a' := 1)
    (b' := 2) (c' := 3) (d' := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem J3_layer1 (hF3 : Nat.card F = 3) :
    Fr.symJB 3 = (blkLin (F := F) 1 2).map (Fr.D 1).ι :=
  Fr.blk_eq_of_layers hF3 (e := 4) (f := 1) (a := 2) (b := 3) (c := 1) (d := 0) (a' := 1)
    (b' := 2) (c' := 3) (d' := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem symJB_zero_sup_one (hF3 : Nat.card F = 3) : Fr.symJB 0 ⊔ Fr.symJB 1 = Fr.Ablk := by
  rw [Fr.J1_layer2 hF3, Fr.symJB_zero]
  exact (Subgroup.map_sup _ _ _).symm

theorem symJB_comm (hF3 : Nat.card F = 3) (i j : Fin 4) (hij : (i : ℕ) + 1 < j) :
    ∀ a ∈ Fr.symJB i, ∀ b ∈ Fr.symJB j, a * b = b * a := by
  have hcases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
    revert i j
    decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Fr.J0_layer3 hF3, Fr.J2_layer3 hF3]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, blkLin_commute 3 0 1 2 (by decide) (by decide) (by decide)
      (by decide) g hg h hh]
  · rw [Fr.J0_layer1 hF3, Fr.J3_layer1 hF3]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, blkLin_commute 3 0 1 2 (by decide) (by decide) (by decide)
      (by decide) g hg h hh]
  · rw [Fr.symJB_one, Fr.symJB_three]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, blkLin_commute 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) g hg h hh]

theorem symJB_pair (hF3 : Nat.card F = 3) (i j : Fin 4) (hij : (j : ℕ) = i + 1) :
    ∃ W : Subgroup G, (linKind F).Pair W (Fr.symJB i) (Fr.symJB j) := by
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) := by
    revert i j
    decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨W, hW⟩ := blkLin_standardPair (F := F) 3 0 1 (by decide) (by decide) (by decide)
    exact ⟨W.map (Fr.D 2).ι, by
      rw [Fr.symJB_zero, Fr.J1_layer2 hF3]
      exact (linKind F).pair_map hW _ (Fr.D 2).ι_injective⟩
  · obtain ⟨W, hW⟩ := blkLin_standardPair (F := F) 0 1 2 (by decide) (by decide) (by decide)
    exact ⟨W.map (Fr.D 4).ι, by
      rw [Fr.symJB_one, Fr.symJB_two]
      exact (linKind F).pair_map hW _ (Fr.D 4).ι_injective⟩
  · obtain ⟨W, hW⟩ := blkLin_standardPair (F := F) 1 2 3 (by decide) (by decide) (by decide)
    exact ⟨W.map (Fr.D 4).ι, by
      rw [Fr.symJB_two, Fr.symJB_three]
      exact (linKind F).pair_map hW _ (Fr.D 4).ι_injective⟩

omit [Finite F] in
theorem symJB_succ (i : Fin 3) :
    Fr.symJB i.succ = (blkLin (F := F) i.castSucc i.succ).map (Fr.D 4).ι := by
  fin_cases i
  · exact Fr.symJB_one
  · exact Fr.symJB_two
  · exact Fr.symJB_three

omit [Finite F] in
theorem symJB_linked :
    ∃ (U : Fin 3 → Subgroup ↥(Fr.D 4).K) (W : Fin 3 → Fin 3 → Subgroup ↥(Fr.D 4).K),
      (linKind F).Chain U W ∧ ∀ i : Fin 3, Fr.symJB i.succ ≤ centralizer ({Fr.X 4} : Set G) ∧
        ((Fr.symJB i.succ).subgroupOf (centralizer ({Fr.X 4} : Set G))).map (proj (Fr.X 4)) =
          (U i).map (Fr.D 4).K.subtype := by
  obtain ⟨W, hW⟩ := blkLin_chain (F := F)
  refine ⟨fun i => (blkLin (F := F) i.castSucc i.succ).map (Fr.D 4).iso.symm.toMonoidHom,
    fun i j => (W i j).map (Fr.D 4).iso.symm.toMonoidHom,
    (linKind F).chain_map hW (Fr.D 4).iso.symm, ?_⟩
  intro i
  have hJ := Fr.symJB_succ i
  refine ⟨?_, ?_⟩
  · rw [hJ]
    rintro _ ⟨s, _, rfl⟩
    exact (Fr.D 4).ι_mem_cent s
  · rw [hJ]
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨s, hs, hsc⟩ := hc
      have hcs : c = (Fr.D 4).ιC s := Subtype.ext hsc.symm
      refine ⟨(Fr.D 4).iso.symm s, ⟨s, hs, rfl⟩, ?_⟩
      rw [hcs, (Fr.D 4).proj_ιC s]
      rfl
    · rintro ⟨k, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨(Fr.D 4).ιC s, ⟨s, hs, rfl⟩, ?_⟩
      rw [(Fr.D 4).proj_ιC s]
      rfl

theorem symJB_center (hF3 : Nat.card F = 3) :
    ∃ z ∈ Fr.symJB 1, orderOf z = 2 ∧ ∀ g ∈ Fr.symJB 1, g * z = z * g := by
  obtain ⟨z, hz, hz2, hzc⟩ := lin_blk_center3 hF3
  rw [Fr.symJB_one]
  refine ⟨(Fr.D 4).ι z, ⟨z, hz, rfl⟩, ?_, ?_⟩
  · rw [orderOf_injective (Fr.D 4).ι (Fr.D 4).ι_injective z]
    exact hz2
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hzc g hg]

end Q3FrameB

end System

end CFSG.GH74.Generic.S1
