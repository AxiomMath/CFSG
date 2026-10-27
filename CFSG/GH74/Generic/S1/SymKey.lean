module

public import CFSG.GH74.Generic.S1.SymLayer
public import CFSG.GH74.Generic.S1.BlkOps

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)

variable {G : Type} [Group G]

@[expose] noncomputable def resCent (T : Set G) : Subgroup G :=
  perfectResidualOf (centralizer T)

theorem resCent_le (T : Set G) : resCent T ≤ centralizer T :=
  Subgroup.map_subtype_le _

theorem le_resCent {T : Set G} {P : Subgroup G} (hP : P ≤ centralizer T) (hperf : ⁅P, P⁆ = P) :
    P ≤ resCent T :=
  le_perfectResidualOf hP hperf

theorem resCent_perfect [Finite G] (T : Set G) : ⁅resCent T, resCent T⁆ = resCent T :=
  perfectResidualOf_perfect _

@[expose] noncomputable def pairRes (X : Fin 5 → G) (A B : Fin 5) : Subgroup G :=
  resCent (X '' {k | k ≠ A ∧ k ≠ B})

section Key

variable {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)} [Finite G]

theorem resCent_eq_map (ops : BlockOps F S) {y : G} (D : LayerData y S) (w : Fin 4 → G)
    (hw : ∀ j, w j ∈ centralizer ({y} : Set G))
    (hact : ∀ j, ActsAsReflOn D.iso (barOf (hw j)) (reflDiag F j))
    {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    resCent ({y, w c, w d} : Set G) = (ops.blk a b).map D.ι := by
  apply le_antisymm
  ·
    intro g hg
    have hRperf := resCent_perfect ({y, w c, w d} : Set G)
    have hRle := resCent_le ({y, w c, w d} : Set G)
    have hRy : resCent ({y, w c, w d} : Set G) ≤ centralizer ({y} : Set G) :=
      le_trans hRle (Subgroup.centralizer_le (by simp))
    have hrange := D.le_range_ι hRperf hRy
    set P : Subgroup ↥S := (resCent ({y, w c, w d} : Set G)).comap D.ι with hP
    have hmapP : P.map D.ι = resCent ({y, w c, w d} : Set G) := by
      rw [hP, Subgroup.map_comap_eq]
      exact inf_eq_right.2 hrange
    have hPperf : ⁅P, P⁆ = P := by
      apply Subgroup.map_injective D.ι_injective
      rw [Subgroup.map_commutator, hmapP, hRperf]
    have hPcomm : ∀ t ∈ P, (t : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (t : GL (Fin 4) F) ∧
        (t : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (t : GL (Fin 4) F) := by
      intro t ht
      have ht' : D.ι t ∈ centralizer ({y, w c, w d} : Set G) := hRle ht
      refine ⟨D.comm_of_ι_comm (hw c) (hact c) ?_, D.comm_of_ι_comm (hw d) (hact d) ?_⟩
      · exact (mem_centralizer_iff.1 ht' (w c) (by simp)).symm
      · exact (mem_centralizer_iff.1 ht' (w d) (by simp)).symm
    have hPle : P ≤ ops.blk a b := ops.perfect_le a b c d hab hac had hbc hbd hcd P hPcomm hPperf
    rw [← hmapP] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    exact ⟨t, hPle ht, rfl⟩
  ·
    have hperf : ⁅(ops.blk a b).map D.ι, (ops.blk a b).map D.ι⁆ = (ops.blk a b).map D.ι := by
      rw [← Subgroup.map_commutator, ops.perfect a b hab]
    apply le_resCent _ hperf
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl | rfl
    · exact (D.ι_comm_self s).symm
    · exact (D.ι_comm_of (hw c) (hact c) (ops.comm_refl a b c hab hac.symm hbc.symm s hs)).symm
    · exact (D.ι_comm_of (hw d) (hact d) (ops.comm_refl a b d hab had.symm hbd.symm s hs)).symm

end Key

theorem fin4_mem_pair {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (j : Fin 4) (hja : j ≠ a) (hjb : j ≠ b) : j = c ∨ j = d := by
  revert a b c d j
  decide

omit [Group G] in
theorem image_compl_succAbove (X : Fin 5 → G) (e : Fin 5) {a b c d : Fin 4} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    X '' {k | k ≠ e.succAbove a ∧ k ≠ e.succAbove b} =
      {X e, X (e.succAbove c), X (e.succAbove d)} := by
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, ⟨hka, hkb⟩, rfl⟩
    by_cases hke : k = e
    · exact Or.inl (by rw [hke])
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hke
      have hja : j ≠ a := fun h => hka (by rw [h])
      have hjb : j ≠ b := fun h => hkb (by rw [h])
      rcases fin4_mem_pair hab hac had hbc hbd hcd j hja hjb with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨e, ⟨(Fin.succAbove_ne e a).symm, (Fin.succAbove_ne e b).symm⟩, rfl⟩
    · exact ⟨e.succAbove c, ⟨fun h => hac (Fin.succAbove_right_injective h).symm,
        fun h => hbc (Fin.succAbove_right_injective h).symm⟩, rfl⟩
    · exact ⟨e.succAbove d, ⟨fun h => had (Fin.succAbove_right_injective h).symm,
        fun h => hbd (Fin.succAbove_right_injective h).symm⟩, rfl⟩

section Pairs

variable {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)} [Finite G]

theorem pairRes_eq_map (ops : BlockOps F S) (X : Fin 5 → G) (D : ∀ e, LayerData (X e) S)
    (hw : ∀ e j, X (e.succAbove j) ∈ centralizer ({X e} : Set G))
    (hact : ∀ e j, ActsAsReflOn (D e).iso (barOf (hw e j)) (reflDiag F j)) (e : Fin 5)
    {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    pairRes X (e.succAbove a) (e.succAbove b) = (ops.blk a b).map (D e).ι := by
  unfold pairRes
  rw [image_compl_succAbove X e hab hac had hbc hbd hcd]
  exact resCent_eq_map ops (D e) (fun j => X (e.succAbove j)) (hw e) (hact e) hab hac had hbc hbd hcd

end Pairs

end CFSG.GH74.Generic.S1
