module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)

local instance f4PilotMainKindsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def Sp6KindType (S : Type) [Group S] (f : ℕ) : Sp6Kind → Prop
  | .field => LieModel S .PSp 3 2 (2 * f)
  | .swap => False
  | .linear6 => LieModel S .PSL 6 2 f
  | .unitary6 => LieModel S .PSU 6 2 f
  | .linear7 => LieModel S .PSL 7 2 f
  | .unitary7 => LieModel S .PSU 7 2 f
  | .omegaPlus8 => LieModel S .POmegaPlus 4 2 f
  | .omegaMinus8 => LieModel S .POmegaMinus 4 2 f

theorem exists_sp6KindType_of_sp6OvergroupType {S : Type} [Group S] {f : ℕ}
    (h : Sp6OvergroupType S f) : ∃ κ : Sp6Kind, κ ≠ .swap ∧ Sp6KindType S f κ := by
  rcases h with h | h | h | h | h | h | h
  · exact ⟨.field, by decide, h⟩
  · exact ⟨.linear6, by decide, h⟩
  · exact ⟨.unitary6, by decide, h⟩
  · exact ⟨.linear7, by decide, h⟩
  · exact ⟨.unitary7, by decide, h⟩
  · exact ⟨.omegaPlus8, by decide, h⟩
  · exact ⟨.omegaMinus8, by decide, h⟩

@[expose] def NeighbourOvergroupKind {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (f : ℕ)
    (κ : Sp6Kind) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((κ ≠ .swap ∧ Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Sp6Overgroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) f ∧ Sp6KindType (Kc ⧸ center Kc) f κ) ∨
      (κ = .swap ∧ Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)))

theorem exists_neighbourOvergroupKind {Y : Type} [Group Y] {s : Y} {D : Subgroup Y} {f : ℕ}
    (h : NeighbourOvergroup s D f) : ∃ κ : Sp6Kind, NeighbourOvergroupKind s D f κ := by
  obtain ⟨Kc, hKc, hDK, h1 | h2⟩ := h
  · obtain ⟨hfix, hlt, hsK, hsN, hov⟩ := h1
    obtain ⟨κ, hκ, hty⟩ := exists_sp6KindType_of_sp6OvergroupType hov.2.2.1
    exact ⟨κ, Kc, hKc, hDK, .inl ⟨hκ, hfix, hlt, hsK, hsN, hov, hty⟩⟩
  · exact ⟨.swap, Kc, hKc, hDK, .inr ⟨rfl, h2⟩⟩

section Neighbours

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def neighbourTorusG (e : L ≃* adjointGroup .F4 K) (N : AmalgamNeighbour) :
    Subgroup G :=
  modelToG e (N.torus K)

@[expose] noncomputable def neighbourLeviG (e : L ≃* adjointGroup .F4 K) (N : AmalgamNeighbour) :
    Subgroup G :=
  ((N.levi K).map e.symm.toMonoidHom).map L.subtype

theorem mem_centralizer_neighbourTorusG (e : L ≃* adjointGroup .F4 K) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (N : AmalgamNeighbour) :
    t ∈ centralizer (neighbourTorusG e N : Set G) :=
  centralizer_le (modelToG_le e _) ht

@[expose] def HR8Kind (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ) (N : AmalgamNeighbour)
    (κ : Sp6Kind) : Prop :=
  ∃ htX : t ∈ centralizer (neighbourTorusG e N : Set G),
    NeighbourOvergroupKind
      (QuotientGroup.mk' (oddCore (centralizer (neighbourTorusG e N : Set G))) ⟨t, htX⟩)
      (((neighbourLeviG e N).subgroupOf (centralizer (neighbourTorusG e N : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (neighbourTorusG e N : Set G))))) f κ

theorem exists_hr8Kind_of_neighbourOvergroup (e : L ≃* adjointGroup .F4 K) {t : G} {f : ℕ}
    {N : AmalgamNeighbour} (htX : t ∈ centralizer (neighbourTorusG e N : Set G))
    (h : NeighbourOvergroup
      (QuotientGroup.mk' (oddCore (centralizer (neighbourTorusG e N : Set G))) ⟨t, htX⟩)
      (((neighbourLeviG e N).subgroupOf (centralizer (neighbourTorusG e N : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (neighbourTorusG e N : Set G))))) f) :
    ∃ κ : Sp6Kind, HR8Kind e t f N κ := by
  obtain ⟨κ, hκ⟩ := exists_neighbourOvergroupKind h
  exact ⟨κ, htX, hκ⟩

@[expose] def HR8YInput : Prop :=
  Sp6CatalogueClauses → ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (t : G) (f : ℕ) (e : L ≃* adjointGroup .F4 K), F4Work L K t f → 2 ≤ f →
    ∀ htY : t ∈ centralizer (neighbourTorusG e .Y : Set G),
      NeighbourOvergroup
        (QuotientGroup.mk' (oddCore (centralizer (neighbourTorusG e .Y : Set G))) ⟨t, htY⟩)
        (((neighbourLeviG e .Y).subgroupOf (centralizer (neighbourTorusG e .Y : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (neighbourTorusG e .Y : Set G))))) f

theorem exists_hr8Kind_Y (hY : HR8YInput) (hcat : Sp6CatalogueClauses) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) : ∃ κ : Sp6Kind, HR8Kind e t f .Y κ := by
  have htY := mem_centralizer_neighbourTorusG e hw.mem_centralizer .Y
  exact exists_hr8Kind_of_neighbourOvergroup e htY (hY hcat G L K t f e hw hf htY)

end Neighbours

section HR8

theorem exists_hr8Kind_X (hcat : Sp6CatalogueClauses) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) : ∃ κ : Sp6Kind, HR8Kind e t f .X κ := by
  have htX := mem_centralizer_neighbourTorusG e hw.mem_centralizer .X
  exact exists_hr8Kind_of_neighbourOvergroup e htX
    (neighbour_overgroup_torusLineR hcat hw.standard hf hw.card_eq e hw.orderOf_eq hw.inf_eq rfl
      htX rfl)

end HR8

section Pieces

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def leviTorusG (e : L ≃* adjointGroup .F4 K)
    (J : Finset (Fin (Tag.rank .F4))) : Subgroup G :=
  modelToG e (leviTorus K J)

@[expose] noncomputable def pieceCard (E T : Subgroup G) : ℕ :=
  Nat.card (perfectCore (E ⊓ centralizer (T : Set G)))

@[expose] noncomputable def neighbourPieceCards (e : L ≃* adjointGroup .F4 K) :
    AmalgamNeighbour → ℕ × ℕ × ℕ
  | .Y => (pieceCard (neighbourCore e .Y) (leviTorusG e {1, 2}),
      pieceCard (neighbourCore e .Y) (leviTorusG e {2}),
      pieceCard (neighbourCore e .Y) (leviTorusG e {1}))
  | N => (pieceCard (neighbourCore e N) (leviTorusG e {1, 2}),
      pieceCard (neighbourCore e N) (leviTorusG e {1}),
      pieceCard (neighbourCore e N) (leviTorusG e {2}))

theorem pieceCard_neighbourCore_eq [Finite G] (e : L ≃* adjointGroup .F4 K)
    {N N' : AmalgamNeighbour} {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) :
    pieceCard (neighbourCore e N) (leviTorusG e J) = pieceCard (neighbourCore e N') (leviTorusG e J) := by
  unfold pieceCard leviTorusG
  rw [perfectCore_neighbourCore_inf_eq e hJ hJ']

theorem mem_consistentKindPairs_of_pieces [Finite G] (e : L ≃* adjointGroup .F4 K) {q : ℕ}
    (hq : 2 ≤ q) {κX κY : Sp6Kind} (hX : neighbourPieceCards e .X = pieceOrders κX q)
    (hY : neighbourPieceCards e .Y = pieceOrders κY q) : (κX, κY) ∈ consistentKindPairs := by
  refine mem_consistentKindPairs_of_pieceOrders hq hX ?_
  rw [← hY]
  have h12 := pieceCard_neighbourCore_eq e (N := .X) (N' := .Y) (J := {1, 2}) (by decide)
    (by decide)
  have h1 := pieceCard_neighbourCore_eq e (N := .X) (N' := .Y) (J := {1}) (by decide) (by decide)
  have h2 := pieceCard_neighbourCore_eq e (N := .X) (N' := .Y) (J := {2}) (by decide) (by decide)
  simp only [neighbourPieceCards, swapPieces, h12, h1, h2]

@[expose] def FieldSwapPieceTablesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' → ∀ κ : Sp6Kind, (κ = .field ∨ κ = .swap) →
      HR8Kind e t f N κ → neighbourPieceCards e N = pieceOrders κ (2 ^ f)

@[expose] def GraphPieceTablesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' → ∀ κ : Sp6Kind, κ ≠ .field → κ ≠ .swap →
      HR8Kind e t f N κ → neighbourPieceCards e N = pieceOrders κ (2 ^ f)

theorem neighbourPieceCards_eq_of_inputs (hFS : FieldSwapPieceTablesInput)
    (hG : GraphPieceTablesInput) [Finite G] [Finite K] [CharP K 2] {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour}
    (hN : N ≠ .X') {κ : Sp6Kind} (h : HR8Kind e t f N κ) :
    neighbourPieceCards e N = pieceOrders κ (2 ^ f) := by
  by_cases hκ : κ = .field ∨ κ = .swap
  · exact hFS G L K e t f hw hf N hN κ hκ h
  · exact hG G L K e t f hw hf N hN κ (fun h' => hκ (.inl h')) (fun h' => hκ (.inr h')) h

theorem mem_consistentKindPairs_of_inputs (hFS : FieldSwapPieceTablesInput)
    (hG : GraphPieceTablesInput) [Finite G] [Finite K] [CharP K 2] {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {κX κY : Sp6Kind}
    (hX : HR8Kind e t f .X κX) (hY : HR8Kind e t f .Y κY) : (κX, κY) ∈ consistentKindPairs :=
  mem_consistentKindPairs_of_pieces e (q := 2 ^ f) (Nat.le_self_pow (by omega) 2)
    (neighbourPieceCards_eq_of_inputs hFS hG hw hf e (by decide) hX)
    (neighbourPieceCards_eq_of_inputs hFS hG hw hf e (by decide) hY)

end Pieces

end CFSG.SeitzReduction.F4Pilot
