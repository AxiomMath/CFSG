module

public import CFSG.GH74.Generic.S1.SymKey
public import CFSG.GH74.L5U5.ModelsPairsUnitary

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic

structure PairKind where
  Pair : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop
  pair_map : ∀ {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}, Pair W U V →
    ∀ φ : X →* Y, Function.Injective φ → Pair (W.map φ) (U.map φ) (V.map φ)
  Chain : ∀ {X : Type} [Group X], (Fin 3 → Subgroup X) → (Fin 3 → Fin 3 → Subgroup X) → Prop
  chain_map : ∀ {X Y : Type} [Group X] [Group Y] {U : Fin 3 → Subgroup X}
    {W : Fin 3 → Fin 3 → Subgroup X}, Chain U W → ∀ e : X ≃* Y,
      Chain (fun i => (U i).map e.toMonoidHom) (fun i j => (W i j).map e.toMonoidHom)

@[expose] def linKind (F : Type) [Field F] : PairKind where
  Pair := fun {X : Type} [Group X] (W U V : Subgroup X) =>
    CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F W U V
  pair_map := fun h φ hφ => linearBlockStandardPair_map' h φ hφ
  Chain := fun {X : Type} [Group X] (U : Fin 3 → Subgroup X) (W : Fin 3 → Fin 3 → Subgroup X) =>
    CFSG.ClassicalInvolution.WeakCT.WeakCTSystem F 3 U W
  chain_map := fun h e => weakCTSystem_map_equiv h e

@[expose] def uniKind (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p] : PairKind where
  Pair := fun {X : Type} [Group X] (W U V : Subgroup X) =>
    CFSG.ClassicalInvolution.Phan.UnitaryBlockStandardPair F p f W U V
  pair_map := fun h φ hφ => unitaryBlockStandardPair_map' h φ hφ
  Chain := fun {X : Type} [Group X] (U : Fin 3 → Subgroup X) (W : Fin 3 → Fin 3 → Subgroup X) =>
    CFSG.ClassicalInvolution.Phan.WeakPhanA F p f 3 U W
  chain_map := fun h e => weakPhanA_map_equiv h e

variable {G : Type} [Group G]

@[expose] noncomputable def symJ (X : Fin 5 → G) : Fin 4 → Subgroup G
  | 0 => pairRes X 4 0
  | 1 => pairRes X 0 1
  | 2 => pairRes X 1 2
  | 3 => pairRes X 2 3

section System

variable {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)} [Finite G]

variable (ops : BlockOps F S) (X : Fin 5 → G) (D : ∀ e, LayerData (X e) S)
  (hw : ∀ e j, X (e.succAbove j) ∈ centralizer ({X e} : Set G))
  (hact : ∀ e j, ActsAsReflOn (D e).iso (barOf (hw e j)) (reflDiag F j))

include ops hact

theorem pairRes_eq_map' (e : Fin 5) {a b c d : Fin 4} {A B : Fin 5} (hA : e.succAbove a = A)
    (hB : e.succAbove b = B) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : pairRes X A B = (ops.blk a b).map (D e).ι := by
  subst hA hB
  exact pairRes_eq_map ops X D hw hact e hab hac had hbc hbd hcd

theorem symJ_one : symJ X 1 = (ops.blk 0 1).map (D 4).ι :=
  pairRes_eq_map' ops X D hw hact 4 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem symJ_two : symJ X 2 = (ops.blk 1 2).map (D 4).ι :=
  pairRes_eq_map' ops X D hw hact 4 (a := 1) (b := 2) (c := 0) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem symJ_three : symJ X 3 = (ops.blk 2 3).map (D 4).ι :=
  pairRes_eq_map' ops X D hw hact 4 (a := 2) (b := 3) (c := 0) (d := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem symSystem_comm (i j : Fin 4) (hij : (i : ℕ) + 1 < j) :
    ∀ a ∈ symJ X i, ∀ b ∈ symJ X j, a * b = b * a := by
  have hcases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
    revert i j
    decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have h1 : symJ X 0 = (ops.blk 3 0).map (D 3).ι :=
      pairRes_eq_map' ops X D hw hact 3 (a := 3) (b := 0) (c := 1) (d := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h2 : symJ X 2 = (ops.blk 1 2).map (D 3).ι :=
      pairRes_eq_map' ops X D hw hact 3 (a := 1) (b := 2) (c := 0) (d := 3) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [h1, h2]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, ops.commute 3 0 1 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) g hg h hh]
  ·
    have h1 : symJ X 0 = (ops.blk 3 0).map (D 1).ι :=
      pairRes_eq_map' ops X D hw hact 1 (a := 3) (b := 0) (c := 1) (d := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h2 : symJ X 3 = (ops.blk 1 2).map (D 1).ι :=
      pairRes_eq_map' ops X D hw hact 1 (a := 1) (b := 2) (c := 0) (d := 3) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [h1, h2]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, ops.commute 3 0 1 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) g hg h hh]
  ·
    rw [symJ_one ops X D hw hact, symJ_three ops X D hw hact]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, ops.commute 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) g hg h hh]

variable (κ : PairKind)

theorem symSystem_pair
    (hstd : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥S, κ.Pair W (ops.blk a b) (ops.blk b c))
    (i j : Fin 4) (hij : (j : ℕ) = i + 1) : ∃ W : Subgroup G, κ.Pair W (symJ X i) (symJ X j) := by
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) := by
    revert i j
    decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have h1 : symJ X 0 = (ops.blk 3 0).map (D 2).ι :=
      pairRes_eq_map' ops X D hw hact 2 (a := 3) (b := 0) (c := 1) (d := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h2 : symJ X 1 = (ops.blk 0 1).map (D 2).ι :=
      pairRes_eq_map' ops X D hw hact 2 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨W, hW⟩ := hstd 3 0 1 (by decide) (by decide) (by decide)
    exact ⟨W.map (D 2).ι, by rw [h1, h2]; exact κ.pair_map hW _ (D 2).ι_injective⟩
  · obtain ⟨W, hW⟩ := hstd 0 1 2 (by decide) (by decide) (by decide)
    exact ⟨W.map (D 4).ι, by
      rw [symJ_one ops X D hw hact, symJ_two ops X D hw hact]
      exact κ.pair_map hW _ (D 4).ι_injective⟩
  · obtain ⟨W, hW⟩ := hstd 1 2 3 (by decide) (by decide) (by decide)
    exact ⟨W.map (D 4).ι, by
      rw [symJ_two ops X D hw hact, symJ_three ops X D hw hact]
      exact κ.pair_map hW _ (D 4).ι_injective⟩

theorem symJ_succ (i : Fin 3) : symJ X i.succ = (ops.blk i.castSucc i.succ).map (D 4).ι := by
  fin_cases i
  · exact symJ_one ops X D hw hact
  · exact symJ_two ops X D hw hact
  · exact symJ_three ops X D hw hact

theorem symSystem_linked
    (hchain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥S,
      κ.Chain (fun i : Fin 3 => ops.blk i.castSucc i.succ) W) :
    ∃ (U : Fin 3 → Subgroup ↥(D 4).K) (W : Fin 3 → Fin 3 → Subgroup ↥(D 4).K), κ.Chain U W ∧
      ∀ i : Fin 3, symJ X i.succ ≤ centralizer ({X 4} : Set G) ∧
        ((symJ X i.succ).subgroupOf (centralizer ({X 4} : Set G))).map (proj (X 4)) =
          (U i).map (D 4).K.subtype := by
  obtain ⟨W, hW⟩ := hchain
  refine ⟨fun i => (ops.blk i.castSucc i.succ).map (D 4).iso.symm.toMonoidHom,
    fun i j => (W i j).map (D 4).iso.symm.toMonoidHom, κ.chain_map hW (D 4).iso.symm, ?_⟩
  intro i
  have hJ := symJ_succ ops X D hw hact i
  refine ⟨?_, ?_⟩
  · rw [hJ]
    rintro _ ⟨s, _, rfl⟩
    exact (D 4).ι_mem_cent s
  · rw [hJ]
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨s, hs, hsc⟩ := hc
      have hcs : c = (D 4).ιC s := Subtype.ext hsc.symm
      refine ⟨(D 4).iso.symm s, ⟨s, hs, rfl⟩, ?_⟩
      rw [hcs, (D 4).proj_ιC s]
      rfl
    · rintro ⟨k, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨(D 4).ιC s, ⟨s, hs, rfl⟩, ?_⟩
      rw [(D 4).proj_ιC s]
      rfl

theorem symSystem_center
    (hcen : ∃ z ∈ ops.blk 0 1, orderOf z = 2 ∧ ∀ g ∈ ops.blk 0 1, g * z = z * g) :
    ∃ z ∈ symJ X 1, orderOf z = 2 ∧ ∀ g ∈ symJ X 1, g * z = z * g := by
  obtain ⟨z, hz, hz2, hzc⟩ := hcen
  rw [symJ_one ops X D hw hact]
  refine ⟨(D 4).ι z, ⟨z, hz, rfl⟩, ?_, ?_⟩
  · rw [orderOf_injective (D 4).ι (D 4).ι_injective z, hz2]
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hzc g hg]

theorem symSystem
    (hstd : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥S, κ.Pair W (ops.blk a b) (ops.blk b c))
    (hchain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥S,
      κ.Chain (fun i : Fin 3 => ops.blk i.castSucc i.succ) W)
    (hcen : ∃ z ∈ ops.blk 0 1, orderOf z = 2 ∧ ∀ g ∈ ops.blk 0 1, g * z = z * g) :
    (∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ symJ X i, ∀ b ∈ symJ X j, a * b = b * a) ∧
      (∀ i j : Fin 4, (j : ℕ) = i + 1 → ∃ W : Subgroup G, κ.Pair W (symJ X i) (symJ X j)) ∧
      (∃ (U : Fin 3 → Subgroup ↥(D 4).K) (W : Fin 3 → Fin 3 → Subgroup ↥(D 4).K), κ.Chain U W ∧
        ∀ i : Fin 3, symJ X i.succ ≤ centralizer ({X 4} : Set G) ∧
          ((symJ X i.succ).subgroupOf (centralizer ({X 4} : Set G))).map (proj (X 4)) =
            (U i).map (D 4).K.subtype) ∧
      ∃ z ∈ symJ X 1, orderOf z = 2 ∧ ∀ g ∈ symJ X 1, g * z = z * g :=
  ⟨symSystem_comm ops X D hw hact, symSystem_pair ops X D hw hact κ hstd,
    symSystem_linked ops X D hw hact κ hchain, symSystem_center ops X D hw hact hcen⟩

end System

end CFSG.GH74.Generic.S1
