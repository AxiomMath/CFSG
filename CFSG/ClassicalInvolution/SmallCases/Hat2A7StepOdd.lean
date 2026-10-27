module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Induction
public import CFSG.ClassicalInvolution.Generic.StepBasic
public import CFSG.ClassicalInvolution.Generic.StepOdd

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Basic

variable {F : Type*} [Group F] {Y L : Subgroup F} {u : F}

theorem IsClassical2A7.not_le_center (h : IsClassical2A7 Y L u) : ¬ L ≤ Subgroup.center F := by
  intro hle
  have hcomm : ∀ a b : L, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b.1).symm
  have hperf : commutator L = ⊤ := h.perfect.commutator_eq_top
  have hz : (⟨u, h.mem⟩ : L) ∈ commutator L := by rw [hperf]; exact Subgroup.mem_top _
  have hbot : commutator L ≤ ⊥ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a b
  have hu1 : u = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp (hbot hz))
  have := h.orderOf_eq_two
  rw [hu1, orderOf_one] at this
  omega

end Basic

section Member

variable {Y : Type} [Group Y] [Finite Y]

theorem IsClassical2A7.map_oddQuotient {L : Subgroup Y} {z : Y} (h : IsClassical2A7 ⊤ L z) :
    IsClassical2A7 ⊤ (L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) where
  orderOf_eq_two := orderOf_mk_oddCore_eq_two h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))
  subnormal := by
    have h1 := h.subnormal
    rw [top_inf_eq] at h1 ⊢
    rw [← centralizer_map_oddCore h.orderOf_eq_two]
    exact CFSG.ComponentClassification.Components.chain_map _ h1
  witness := A7Witness.of_surjective
    ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L)
    (MonoidHom.subgroupMap_surjective _ L) (oddCore_restriction_ker_odd L) h.witness

omit [Finite Y] in
theorem ConjInvariant2A7.toConjInvariant {Λ : Set (Subgroup Y)} (h : ConjInvariant2A7 Λ) :
    ConjInvariant Λ := h

theorem inClass2A7_oddQuotient {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ) :
    InClass2A7 (oddQuotientFamily2A7 Λ) where
  nonempty := hΛ.nonempty.image _
  conjInvariant := conjInvariant_oddQuotientFamily hΛ.conjInvariant.toConjInvariant
  generated := by
    set π := QuotientGroup.mk' (classicalInvolutionOddCore Y)
    have h : ⨆ M ∈ oddQuotientFamily2A7 Λ, M = (⨆ L ∈ Λ, L).map π := by
      refine le_antisymm (iSup₂_le fun M hM => ?_) ?_
      · obtain ⟨L, hL, rfl⟩ := hM
        exact Subgroup.map_mono (le_iSup₂ (f := fun (L : Subgroup Y) (_ : L ∈ Λ) => L) L hL)
      · rw [Subgroup.map_le_iff_le_comap]
        refine iSup₂_le fun L hL => ?_
        exact Subgroup.map_le_iff_le_comap.mp (le_iSup₂
          (f := fun (M : Subgroup (Y ⧸ classicalInvolutionOddCore Y))
            (_ : M ∈ oddQuotientFamily2A7 Λ) => M) (L.map π) ⟨L, hL, rfl⟩)
    rw [h, hΛ.generated, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  classical := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    exact ⟨_, hz.map_oddQuotient⟩

end Member

section Transport

variable {X X' : Type} [Group X] [Group X'] {Φ : Set (Subgroup X)}

noncomputable def A7SystemData.congr (e : X ≃* X') (D : A7SystemData X Φ) :
    A7SystemData X' (Subgroup.map e.toMonoidHom '' Φ) where
  card := D.card
  comp i := (D.comp i).map e.toMonoidHom
  perfect i := by
    have := D.perfect i
    exact Group.IsPerfect.ofSurjective
      (f := ((D.comp i).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (MulEquiv.surjective _)
  witness i := A7Witness.of_mulEquiv ((D.comp i).equivMapOfInjective e.toMonoidHom e.injective)
    (D.witness i)
  commute i j h := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, D.commute i j h a ha b hb]
  generate := by
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top_of_surjective _ e.surjective]
  members := by
    have h : Subgroup.map e.toMonoidHom '' Φ = Subgroup.map e.toMonoidHom '' Set.range D.comp :=
      congrArg _ D.members
    rw [h, ← Set.range_comp]
    rfl

theorem A7System.congr (e : X ≃* X') (h : A7System X Φ) :
    A7System X' (Subgroup.map e.toMonoidHom '' Φ) :=
  h.map (A7SystemData.congr e)

end Transport

section Corefree

variable {Y : Type} [Group Y]

theorem a7SystemMod_of_a7System_corefree (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (h : A7System Y Λ) : A7SystemMod Λ :=
  A7System.congr (oddQuotientEquivOfCorefree hO) h

theorem a7System_of_a7SystemMod_corefree (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (h : A7SystemMod Λ) : A7System Y Λ := by
  have key : Subgroup.map (oddQuotientEquivOfCorefree hO).symm.toMonoidHom ''
      oddQuotientFamily2A7 Λ = Λ := by
    ext L
    constructor
    · rintro ⟨_, ⟨L', hL', rfl⟩, rfl⟩
      rw [Subgroup.map_map]
      have : (oddQuotientEquivOfCorefree hO).symm.toMonoidHom.comp
          (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = MonoidHom.id Y := by
        ext x
        exact (oddQuotientEquivOfCorefree hO).symm_apply_apply x
      rw [this, Subgroup.map_id]
      exact hL'
    · intro hL
      refine ⟨L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)), ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_map]
      have : (oddQuotientEquivOfCorefree hO).symm.toMonoidHom.comp
          (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = MonoidHom.id Y := by
        ext x
        exact (oddQuotientEquivOfCorefree hO).symm_apply_apply x
      rw [this, Subgroup.map_id]
  have := A7System.congr (oddQuotientEquivOfCorefree hO).symm h
  rwa [key] at this

end Corefree

theorem a7SystemMod_of_oddQuotient {Y : Type} [Group Y] [Finite Y]
    (hBelow : CITBelow2A7 (Nat.card Y)) (hO : classicalInvolutionOddCore Y ≠ ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ) : A7SystemMod Λ := by
  have hlt : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < Nat.card Y := by
    have hmul := (classicalInvolutionOddCore Y).card_eq_card_quotient_mul_card_subgroup
    have h1 : 1 < Nat.card (classicalInvolutionOddCore Y) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hO
    have h2 : 0 < Nat.card (Y ⧸ classicalInvolutionOddCore Y) := Nat.card_pos
    nlinarith
  have hmod := hBelow _ hlt (oddQuotientFamily2A7 Λ) (inClass2A7_oddQuotient hΛ)
  exact a7System_of_a7SystemMod_corefree
    (CFSG.ComponentClassification.OddCore.quotient_corefree Y) hmod

end CFSG.ClassicalInvolution.Hat2A7
