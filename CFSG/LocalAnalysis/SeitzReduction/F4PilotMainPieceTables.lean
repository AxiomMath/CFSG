module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapNormalize
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

local instance f4PilotMainPieceTablesNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem natCard_SL_two {K : Type} [Field K] [Finite K] : Nat.card SL(2, K) = ordSL 2 (Nat.card K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  rfl

theorem one_two_subset_nodes {N : AmalgamNeighbour} (hN : N ≠ .X') :
    ({1, 2} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes := by
  cases N
  · decide
  · decide
  · exact absurd rfl hN

theorem singleton_subset_nodes {N : AmalgamNeighbour} (hN : N ≠ .X') {j : Fin (Tag.rank .F4)}
    (hj : j = 1 ∨ j = 2) : ({j} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes :=
  (Finset.singleton_subset_iff.2 (by rcases hj with rfl | rfl <;> simp)).trans
    (one_two_subset_nodes hN)

section Orders


variable {K : Type} [Field K]

theorem natCard_leviPiece {N : AmalgamNeighbour} {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ N.nodes) :
    Nat.card (leviPiece K N J) =
      Nat.card (CFSG.LieType.CurtisTits.levi (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup J) := by
  have hle := levi_le_neighbourLevi (K := K) hJ
  rw [leviPiece, ← levi_f4Datum_eq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem levi_singleton_eq_rankOne (j : Fin (Tag.rank .F4)) :
    CFSG.LieType.CurtisTits.levi (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup {j} =
      CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j := by
  simp [CFSG.LieType.CurtisTits.levi]

variable
  [Finite K] [CharP K 2]

theorem natCard_levi_one_two :
    Nat.card (CFSG.LieType.CurtisTits.levi (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup
      {1, 2}) = ordSp 2 (Nat.card K) := by
  rw [levi_one_two_eq_B2Levi, ← Nat.card_congr (b2LeviEquiv K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  rfl

theorem map_b2LeviHom_rankOne {i : Fin 2} {j : Fin (Tag.rank .F4)}
    (hij : c2ToF4 (Pi.single i 1) = Pi.single j 1) (hi : Pi.single i 1 ∈ c2Roots)
    (hi' : -Pi.single i 1 ∈ c2Roots) :
    (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Symplectic.rootGroup 2 K) i).map
        (b2LeviHom K) =
      CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j := by
  rw [CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
    map_b2LeviHom_rootGroup (mem_roots_of_mem_c2Roots hi),
    map_b2LeviHom_rootGroup (mem_roots_of_mem_c2Roots hi'), map_neg, hij]

theorem natCard_rankOne_one :
    Nat.card (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup
      1) = ordSL 2 (Nat.card K) := by
  have hc1 : c2ToF4 (Pi.single 1 1) = Pi.single 1 1 := by decide
  rw [← map_b2LeviHom_rankOne (i := 1) hc1 (by decide) (by decide),
    Subgroup.card_map_of_injective b2LeviHom_injective,
    ← CFSG.ClassicalInvolution.Models.SymplecticPairs.range_longBlock_eq_rankOne
      (k := (1 : Fin 2)) (by decide),
    ← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_injective (K := K) (n := 2)
        (1 : Fin 2))).toEquiv, natCard_SL_two]

theorem natCard_rankOne_two :
    Nat.card (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup
      2) = ordSL 2 (Nat.card K) := by
  have hc0 : c2ToF4 (Pi.single 0 1) = Pi.single 2 1 := by decide
  rw [← map_b2LeviHom_rankOne (i := 0) hc0 (by decide) (by decide),
    Subgroup.card_map_of_injective b2LeviHom_injective,
    ← CFSG.ClassicalInvolution.Models.SymplecticPairs.range_shortBlock_eq_rankOne
      (k := (0 : Fin 2)) (by decide),
    ← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_injective (K := K)
        (CFSG.LieType.Universal.Symplectic.SpExtras.ne_succ' (k := (0 : Fin 2))
          (by decide)))).toEquiv, natCard_SL_two]

theorem natCard_leviPiece_one_two {N : AmalgamNeighbour} (hN : N ≠ .X') :
    Nat.card (leviPiece K N {1, 2}) = ordSp 2 (Nat.card K) := by
  rw [natCard_leviPiece (one_two_subset_nodes hN), natCard_levi_one_two]

theorem natCard_leviPiece_one {N : AmalgamNeighbour} (hN : N ≠ .X') :
    Nat.card (leviPiece K N {1}) = ordSL 2 (Nat.card K) := by
  rw [natCard_leviPiece ((Finset.singleton_subset_iff.2 (by simp)).trans (one_two_subset_nodes hN)),
    levi_singleton_eq_rankOne, natCard_rankOne_one]

theorem natCard_leviPiece_two {N : AmalgamNeighbour} (hN : N ≠ .X') :
    Nat.card (leviPiece K N {2}) = ordSL 2 (Nat.card K) := by
  rw [natCard_leviPiece ((Finset.singleton_subset_iff.2 (by simp)).trans (one_two_subset_nodes hN)),
    levi_singleton_eq_rankOne, natCard_rankOne_two]

end Orders

section Pieces


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem pieceCard_neighbourCore_eq_natCard_pieceCore {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ N.nodes) :
    pieceCard (neighbourCore e N) (leviTorusG e J) = Nat.card (pieceCore e J) := by
  rw [pieceCard, leviTorusG, ← pieceCore_eq e N hJ]

theorem FieldNeighbourIso.natCard_pieceCore {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2]
    {σ : K₂ ≃+* K₂} {e : L ≃* adjointGroup .F4 (fixSubfield σ)} {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    Nat.card (pieceCore e J) = Nat.card (leviPiece K₂ N J) := by
  rw [← h.map_leviPiece hq hJ hJ2,
    Subgroup.card_map_of_injective (neighbourCore e N).subtype_injective,
    Subgroup.card_map_of_injective h.Φ.injective]

theorem SwapNeighbourIso.natCard_pieceCore {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : L ≃* adjointGroup .F4 K} {t : G} {N : AmalgamNeighbour} (h : SwapNeighbourIso e t N)
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) : Nat.card (pieceCore e J) = Nat.card (leviPiece K N J) ^ 2 := by
  have hinj : Function.Injective ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) :=
    (neighbourCore e N).subtype_injective.comp h.Φ.injective
  rw [← h.map_leviPiece hq hJ hJ2, Subgroup.card_map_of_injective hinj,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, sq]

theorem neighbourPieceCards_of_fieldNeighbourIso {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2]
    {σ : K₂ ≃+* K₂} {e : L ≃* adjointGroup .F4 (fixSubfield σ)} {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) (hN : N ≠ .X') (hq : 4 ≤ Nat.card (fixSubfield σ))
    (hK₂ : Nat.card K₂ = Nat.card (fixSubfield σ) ^ 2) :
    neighbourPieceCards e N = pieceOrders .field (Nat.card (fixSubfield σ)) := by
  have e12 : pieceCard (neighbourCore e N) (leviTorusG e {1, 2}) =
      ordSp 2 (Nat.card (fixSubfield σ) ^ 2) := by
    rw [pieceCard_neighbourCore_eq_natCard_pieceCore e (one_two_subset_nodes hN),
      h.natCard_pieceCore hq (one_two_subset_nodes hN) (by decide), natCard_leviPiece_one_two hN,
      hK₂]
  have e1 : pieceCard (neighbourCore e N) (leviTorusG e {1}) =
      ordSL 2 (Nat.card (fixSubfield σ) ^ 2) := by
    rw [pieceCard_neighbourCore_eq_natCard_pieceCore e (singleton_subset_nodes hN (.inl rfl)),
      h.natCard_pieceCore hq (singleton_subset_nodes hN (.inl rfl)) (by decide),
      natCard_leviPiece_one hN, hK₂]
  have e2 : pieceCard (neighbourCore e N) (leviTorusG e {2}) =
      ordSL 2 (Nat.card (fixSubfield σ) ^ 2) := by
    rw [pieceCard_neighbourCore_eq_natCard_pieceCore e (singleton_subset_nodes hN (.inr rfl)),
      h.natCard_pieceCore hq (singleton_subset_nodes hN (.inr rfl)) (by decide),
      natCard_leviPiece_two hN, hK₂]
  cases N
  · simp only [neighbourPieceCards, e12, e1, e2, pieceOrders]
  · simp only [neighbourPieceCards, e12, e1, e2, pieceOrders]
  · exact absurd rfl hN

theorem neighbourPieceCards_of_swapNeighbourIso {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : L ≃* adjointGroup .F4 K} {t : G} {N : AmalgamNeighbour} (h : SwapNeighbourIso e t N)
    (hN : N ≠ .X') (hq : 4 ≤ Nat.card K) :
    neighbourPieceCards e N = pieceOrders .swap (Nat.card K) := by
  have e12 : pieceCard (neighbourCore e N) (leviTorusG e {1, 2}) = ordSp 2 (Nat.card K) ^ 2 := by
    rw [pieceCard_neighbourCore_eq_natCard_pieceCore e (one_two_subset_nodes hN),
      h.natCard_pieceCore hq (one_two_subset_nodes hN) (by decide), natCard_leviPiece_one_two hN]
  have e1 : pieceCard (neighbourCore e N) (leviTorusG e {1}) = ordSL 2 (Nat.card K) ^ 2 := by
    rw [pieceCard_neighbourCore_eq_natCard_pieceCore e (singleton_subset_nodes hN (.inl rfl)),
      h.natCard_pieceCore hq (singleton_subset_nodes hN (.inl rfl)) (by decide),
      natCard_leviPiece_one hN]
  have e2 : pieceCard (neighbourCore e N) (leviTorusG e {2}) = ordSL 2 (Nat.card K) ^ 2 := by
    rw [pieceCard_neighbourCore_eq_natCard_pieceCore e (singleton_subset_nodes hN (.inr rfl)),
      h.natCard_pieceCore hq (singleton_subset_nodes hN (.inr rfl)) (by decide),
      natCard_leviPiece_two hN]
  cases N
  · simp only [neighbourPieceCards, e12, e1, e2, pieceOrders]
  · simp only [neighbourPieceCards, e12, e1, e2, pieceOrders]
  · exact absurd rfl hN

end Pieces

section Transport


variable {G : Type} [Group G] {L : Subgroup G} {K K' : Type} [Field K] [Field K']

theorem modelToG_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K')
    {H : Subgroup (ModGL .F4 K)} {H' : Subgroup (ModGL .F4 K')}
    (h₁ : ∀ g ∈ H, baseChangeGL (ε : K →+* K') g ∈ H')
    (h₂ : ∀ g ∈ H', baseChangeGL (ε.symm : K' →+* K) g ∈ H) :
    modelToG (e.trans (adjointGroupF4RingEquiv ε)) H' = modelToG e H := by
  ext g
  rw [mem_modelToG, mem_modelToG]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(adjointGroupF4RingEquiv ε).symm y, h₂ _ hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨adjointGroupF4RingEquiv ε x, h₁ _ hx, ?_⟩
    rw [MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply]

theorem neighbourTorusG_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K')
    (N : AmalgamNeighbour) :
    neighbourTorusG (e.trans (adjointGroupF4RingEquiv ε)) N = neighbourTorusG e N :=
  modelToG_trans_ringEquiv e ε (fun _ hg => baseChangeGL_mem_torus _ N hg)
    (fun _ hg => baseChangeGL_mem_torus _ N hg)

theorem leviTorusG_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K')
    (J : Finset (Fin (Tag.rank .F4))) :
    leviTorusG (e.trans (adjointGroupF4RingEquiv ε)) J = leviTorusG e J :=
  modelToG_trans_ringEquiv e ε (fun _ hg => baseChangeGL_mem_leviTorus _ hg)
    (fun _ hg => baseChangeGL_mem_leviTorus _ hg)

theorem neighbourLeviG_eq_modelToG (e : L ≃* adjointGroup .F4 K) (N : AmalgamNeighbour) :
    neighbourLeviG e N = modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype) := by
  have h : ((N.levi K).map (adjointGroup .F4 K).subtype).subgroupOf (adjointGroup .F4 K) =
      N.levi K :=
    Subgroup.comap_map_eq_self_of_injective (adjointGroup .F4 K).subtype_injective _
  rw [neighbourLeviG, modelToG, h]

theorem neighbourLeviG_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K')
    (N : AmalgamNeighbour) :
    neighbourLeviG (e.trans (adjointGroupF4RingEquiv ε)) N = neighbourLeviG e N := by
  rw [neighbourLeviG_eq_modelToG, neighbourLeviG_eq_modelToG]
  exact modelToG_trans_ringEquiv e ε (fun _ hg => baseChangeGL_mem_map_levi _ N hg)
    (fun _ hg => baseChangeGL_mem_map_levi _ N hg)

theorem neighbourCore_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K')
    (N : AmalgamNeighbour) :
    neighbourCore (e.trans (adjointGroupF4RingEquiv ε)) N = neighbourCore e N := by
  have h := neighbourTorusG_trans_ringEquiv e ε N
  unfold neighbourTorusG at h
  rw [neighbourCore, neighbourCore, h]

@[expose] def HR8KindAt (t : G) (f : ℕ) (X D : Subgroup G) (κ : Sp6Kind) : Prop :=
  ∃ htX : t ∈ centralizer (X : Set G),
    NeighbourOvergroupKind
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f κ

theorem hr8Kind_iff_hr8KindAt (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ)
    (N : AmalgamNeighbour) (κ : Sp6Kind) :
    HR8Kind e t f N κ ↔ HR8KindAt t f (neighbourTorusG e N) (neighbourLeviG e N) κ :=
  Iff.rfl

theorem hr8Kind_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K') (t : G) (f : ℕ)
    (N : AmalgamNeighbour) (κ : Sp6Kind) :
    HR8Kind (e.trans (adjointGroupF4RingEquiv ε)) t f N κ ↔ HR8Kind e t f N κ := by
  rw [hr8Kind_iff_hr8KindAt, hr8Kind_iff_hr8KindAt, neighbourTorusG_trans_ringEquiv,
    neighbourLeviG_trans_ringEquiv]

theorem neighbourPieceCards_trans_ringEquiv (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K')
    (N : AmalgamNeighbour) :
    neighbourPieceCards (e.trans (adjointGroupF4RingEquiv ε)) N = neighbourPieceCards e N := by
  cases N <;>
    simp only [neighbourPieceCards, neighbourCore_trans_ringEquiv, leviTorusG_trans_ringEquiv]

end Transport

section SwapInput


@[expose] def SwapNeighbourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' → HR8Kind e t f N .swap →
      ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
        Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
        Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e N ∧
        neighbourCore e N ⊓ centralizer ({t} : Set G) =
          modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype)

end SwapInput

theorem four_le_two_pow_of_two_le {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

section Assembly


theorem neighbourPieceCards_field_of_input (hF : FieldNeighbourInput) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : L ≃* adjointGroup .F4 K} {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    {N : AmalgamNeighbour} (hN : N ≠ .X') (h : HR8Kind e t f N .field) :
    neighbourPieceCards e N = pieceOrders .field (2 ^ f) := by
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, hσc, hk⟩ := exists_quadraticFrobenius_F4 hw.one_le
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hw.card_eq, hk]
  set ε : K ≃+* fixSubfield σ := FiniteField.ringEquivOfCardEq hc
  have hw' : F4Work L (fixSubfield σ) t f :=
    ⟨hw.standard, hw.center_eq_bot, hw.one_le, hk, hw.orderOf_eq, hw.inf_eq⟩
  have h' : HR8Kind (e.trans (adjointGroupF4RingEquiv ε)) t f N .field :=
    (hr8Kind_trans_ringEquiv e ε t f N .field).2 h
  obtain ⟨hiso, hfix⟩ := hF G L K₂ σ f ⟨hK₂, hσ, hσc⟩ hf _ t hw' N hN h'
  obtain ⟨Φ⟩ := nonempty_fieldNeighbourIso N hiso hw.mem_centralizer hw.orderOf_eq hσ hfix
  have hq : 4 ≤ Nat.card (fixSubfield σ) := hk ▸ four_le_two_pow_of_two_le hf
  have hK₂' : Nat.card K₂ = Nat.card (fixSubfield σ) ^ 2 := by
    rw [hK₂, hk, ← pow_mul, mul_comm]
  rw [← neighbourPieceCards_trans_ringEquiv e ε N,
    neighbourPieceCards_of_fieldNeighbourIso Φ hN hq hK₂', hk]

theorem neighbourPieceCards_swap_of_input (hS : SwapNeighbourInput) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : L ≃* adjointGroup .F4 K} {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    {N : AmalgamNeighbour} (hN : N ≠ .X') (h : HR8Kind e t f N .swap) :
    neighbourPieceCards e N = pieceOrders .swap (2 ^ f) := by
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := hS G L K e t f hw hf N hN h
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨Φ⟩ := nonempty_swapNeighbourIso N htt hc hd hE hfix
  rw [neighbourPieceCards_of_swapNeighbourIso Φ hN (hw.card_eq ▸ four_le_two_pow_of_two_le hf), hw.card_eq]

theorem fieldSwapPieceTablesInput_of_inputs (hF : FieldNeighbourInput)
    (hS : SwapNeighbourInput) : FieldSwapPieceTablesInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN κ hκ h
  rcases hκ with rfl | rfl
  · exact neighbourPieceCards_field_of_input hF hw hf hN h
  · exact neighbourPieceCards_swap_of_input hS hw hf hN h

theorem swapRowCTInput_of_swapNeighbourInput (hS : SwapNeighbourInput) : SwapRowCTInput := by
  intro G _ _ L K _ _ _ e t f hw hf hX hY
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hq : 4 ≤ Nat.card K := hw.card_eq ▸ four_le_two_pow_of_two_le hf
  obtain ⟨KX, hcX, hdX, hEX, hfX⟩ := hS G L K e t f hw hf .X (by decide) hX
  obtain ⟨KY, hcY, hdY, hEY, hfY⟩ := hS G L K e t f hw hf .Y (by decide) hY
  obtain ⟨G₁, G₂, ε, hC, hmap, hsup, -⟩ := exists_swapFactors_of_decomposition hw.mem_centralizer
    htt hq hcX hdX hEX hfX hcY hdY hEY hfY
  refine ⟨G₁, ⟨ε⟩, hmap ▸ hC, ?_⟩
  rw [hmap]
  exact hsup

end Assembly

end CFSG.SeitzReduction.F4Pilot
