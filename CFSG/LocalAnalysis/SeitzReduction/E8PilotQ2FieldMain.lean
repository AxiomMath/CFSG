module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldCT
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldNormalize

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance e8PilotQ2FieldMainNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Congr

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] {ι : K →+* K₂} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K}

@[expose] noncomputable def TwoFieldParam.congr {N : E8Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam ι e N E) (hE : E = E') : TwoFieldParam ι e N E' where
  Φ := h.Φ.trans (MulEquiv.subgroupCongr hE)
  fix x := h.fix x

end Congr

section Input

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def q2NeighbourG (e : L ≃* adjointGroup .E8 K)
    (A : Subgroup (adjointGroup .E8 K)) (N : E8Neighbour) : Subgroup G :=
  ((A.map (MulAut.conj (N.rep K)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype

@[expose] def E8TwoFieldPieceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (e : L ≃* adjointGroup .E8 K) (t : G), E8Work L K t 1 →
    ∀ (K₂ : Type) [Field K₂] [Finite K₂] [CharP K₂ 2] (ι : K →+* K₂), Nat.card K₂ = 2 ^ 2 →
    ∀ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K → Nat.card A = Nat.card K + 1 →
    ∀ (N N' : E8Neighbour) (h : TwoFieldParam ι e N (centralizerPerfectCore (q2NeighbourG e A N)))
      (h' : TwoFieldParam ι e N' (centralizerPerfectCore (q2NeighbourG e A N'))),
      ((leviPiece K₂ N {0}).map h.Φ.toMonoidHom).map
          (centralizerPerfectCore (q2NeighbourG e A N)).subtype =
        ((leviPiece K₂ N' {0}).map h'.Φ.toMonoidHom).map
          (centralizerPerfectCore (q2NeighbourG e A N')).subtype

end Input

section Triple

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] {ι : K →+* K₂} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K}

theorem twoFieldAligned_ofTriple {E₁ E₂ E₃ : Subgroup G} {hX : TwoFieldParam ι e .high E₁}
    {hY : TwoFieldParam ι e .two E₂} {hZ : TwoFieldParam ι e .six E₃}
    (h1 : hX.TwistOn hY 1 {0, 2, 4, 5, 6}) (h2 : hX.TwistOn hZ 1 {0, 1, 2, 3})
    (h3 : hY.TwistOn hZ 1 {0, 2, 7}) : TwoFieldAligned (twoFieldOfTriple hX hY hZ) := by
  intro N N' J hJ hJ' x x' hxx' hx
  have hx' : x' ∈ leviPiece K₂ N' J := mem_leviPiece.2 (hxx' ▸ mem_leviPiece.1 hx)
  have hS : ∀ {A B : E8Neighbour}, J ⊆ A.nodes → J ⊆ B.nodes →
      (A = .high → B = .two → J ⊆ {0, 2, 4, 5, 6}) ∧ (A = .high → B = .six → J ⊆ {0, 1, 2, 3}) ∧
        (A = .two → B = .six → J ⊆ {0, 2, 7}) := fun hA hB =>
    ⟨fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.2 ha hb⟩
  have e1 : ∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 4, 5, 6} →
      ∀ (x : E8Neighbour.high.levi K₂) (x' : E8Neighbour.two.levi K₂),
        (x : adjointGroup .E8 K₂) = x' → x ∈ leviPiece K₂ .high J →
          ((hX.Φ x : E₁) : G) = hY.Φ x' := fun hJ x x' hxx' hx =>
    hX.eq_on_leviPiece hY (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h1 j (hJ hj)) hxx' hx
  have e2 : ∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 1, 2, 3} →
      ∀ (x : E8Neighbour.high.levi K₂) (x' : E8Neighbour.six.levi K₂),
        (x : adjointGroup .E8 K₂) = x' → x ∈ leviPiece K₂ .high J →
          ((hX.Φ x : E₁) : G) = hZ.Φ x' := fun hJ x x' hxx' hx =>
    hX.eq_on_leviPiece hZ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h2 j (hJ hj)) hxx' hx
  have e3 : ∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 7} →
      ∀ (x : E8Neighbour.two.levi K₂) (x' : E8Neighbour.six.levi K₂),
        (x : adjointGroup .E8 K₂) = x' → x ∈ leviPiece K₂ .two J →
          ((hY.Φ x : E₂) : G) = hZ.Φ x' := fun hJ x x' hxx' hx =>
    hY.eq_on_leviPiece hZ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h3 j (hJ hj)) hxx' hx
  cases N <;> cases N'
  · exact congrArg (fun z => ((hX.Φ z : E₁) : G)) (Subtype.ext hxx')
  · exact e1 ((hS hJ hJ').1 rfl rfl) x x' hxx' hx
  · exact e2 ((hS hJ hJ').2.1 rfl rfl) x x' hxx' hx
  · exact (e1 ((hS hJ' hJ).1 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => ((hY.Φ z : E₂) : G)) (Subtype.ext hxx')
  · exact e3 ((hS hJ hJ').2.2 rfl rfl) x x' hxx' hx
  · exact (e2 ((hS hJ' hJ).2.1 rfl rfl) x' x hxx'.symm hx').symm
  · exact (e3 ((hS hJ' hJ).2.2 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => ((hZ.Φ z : E₃) : G)) (Subtype.ext hxx')

end Triple

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G}

omit [Finite G] in
theorem map_conj_map_map_symm_q2 (e : L ≃* adjointGroup .E8 K) (A : Subgroup (adjointGroup .E8 K))
    (n : adjointGroup .E8 K) :
    ((A.map e.symm.toMonoidHom).map L.subtype).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom =
      ((A.map (MulAut.conj n).toMonoidHom).map e.symm.toMonoidHom).map L.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem false_of_fieldRow_E8_two_of_pieceInput (hP : E8TwoFieldPieceInput)
    (hw : E8Work L K t 1) (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)}
    (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    (htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))
    (hF : NeighbourOvergroupE7Field
      (QuotientGroup.mk' (oddCore (centralizer
        (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
      (((((e7Levi K).map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))))) 1) :
    False := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, -, hk⟩ := F4Pilot.exists_quadraticFrobenius_F4 (f := 1) le_rfl
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hw.card_eq]
  set ε : K ≃+* fixSubfield σ := FiniteField.ringEquivOfCardEq hc with hε
  set ι : K →+* K₂ := (fixSubfield σ).subtype.comp (ε : K →+* fixSubfield σ) with hι
  have hfix : ∀ x : K₂, σ x = x ↔ x ∈ Set.range ι := by
    intro x
    rw [F4Pilot.apply_eq_iff_mem_range_fixSubfield_subtype σ]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ε.symm y, by simp [hι]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ε y, rfl⟩
  have hK₂' : Nat.card K₂ = 2 ^ 2 := by rw [hK₂]
  set X : Subgroup G := (A.map e.symm.toMonoidHom).map L.subtype with hXdef
  obtain ⟨Φ₀, hΦ₀⟩ := exists_normalized_nonsplit_two hw e hAJ hA rfl htX rfl hF hK₂' ι hσ hfix
  let P₀ : TwoFieldParam ι e .high (centralizerPerfectCore X) := ⟨Φ₀, hΦ₀⟩
  have hE : ∀ N : E8Neighbour, (centralizerPerfectCore X).map
      (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom =
        centralizerPerfectCore (q2NeighbourG e A N) := by
    intro N
    rw [F4Pilot.map_centralizerPerfectCore, hXdef, map_conj_map_map_symm_q2]
    rfl
  let PN : ∀ N : E8Neighbour, TwoFieldParam ι e N (centralizerPerfectCore (q2NeighbourG e A N)) :=
    fun N => (P₀.toNeighbour N).congr (hE N)
  have hPN := hP G L K e t hw K₂ ι hK₂' A hAJ hA
  obtain ⟨ρht, hρht, h1p, h1n⟩ := (PN .high).exists_twistAt_single_of_map_eq (PN .two)
    (j := 0) (by decide) (by decide) (hPN .high .two (PN .high) (PN .two))
  obtain ⟨ρhs, hρhs, h2p, h2n⟩ := (PN .high).exists_twistAt_single_of_map_eq (PN .six)
    (j := 0) (by decide) (by decide) (hPN .high .six (PN .high) (PN .six))
  obtain ⟨ρts, -, h3p, h3n⟩ := (PN .two).exists_twistAt_single_of_map_eq (PN .six)
    (j := 0) (by decide) (by decide) (hPN .two .six (PN .two) (PN .six))
  obtain ⟨a1, a2, a3⟩ := exists_aligned_twoFieldParam (PN .high) (PN .two) (PN .six) hρht hρhs
    ⟨h1p, h1n⟩ ⟨h2p, h2n⟩ ⟨h3p, h3n⟩
  have hal := twoFieldAligned_ofTriple a1 a2 a3
  obtain ⟨e₀⟩ := nonempty_mulEquiv_twoFieldSup hal
  have hLG := le_twoFieldSup hal
  have hCN : centralizer (L : Set G) ≤ normalizer
      (twoFieldSup (twoFieldOfTriple (PN .high) ((PN .two).twist ρht hρht)
        ((PN .six).twist ρhs hρhs)) : Set G) := by
    intro c hc
    refine mem_normalizer_twoFieldSup_of_mem_centralizer hσ hfix _ hc fun N => ?_
    have hcN : ∀ M : E8Neighbour,
        c ∈ normalizer (centralizerPerfectCore (q2NeighbourG e A M) : Set G) := fun M =>
      F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
        (centralizer_le_normalizer _ (centralizer_le (map_subtype_le _) hc))
    cases N
    exacts [hcN .high, hcN .two, hcN .six]
  exact false_of_E8_two_of_fieldRow_subgroup hw e (by rw [hK₂]) e₀ hLG hCN

end Main

end CFSG.SeitzReduction.E8Pilot
