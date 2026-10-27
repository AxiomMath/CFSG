module

public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverDecomp
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public noncomputable section

namespace CFSG.LieType.Chevalley.SimplyLacedCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem coe_commutatorElement_adjointGroup (a b : adjointGroup τ K) :
    ((⁅a, b⁆ : adjointGroup τ K) : ModGL τ K) = ⁅(a : ModGL τ K), (b : ModGL τ K)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

variable [CharP K 2]

@[expose] def adjointRoots
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    BinaryRoots (adjointGroup τ K) τ where
  x α := ⟨pinnedX τ K α 1, pinnedX_mem_adjointGroup α 1⟩
  mul_self α _ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero])
  comm α β hα hβ hne h0 := by
    have hsl := simplyLaced_of_tag hτ
    have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
    by_cases hab : α = β
    · rw [hab]
    · have h := (simply_laced_root_commutator_unit τ hτ' hα hβ hab hne).2
        (not_isRoot_add hsl hα hβ h0) K _ (Subgroup.subset_closure ⟨1, rfl⟩) _
        (Subgroup.subset_closure ⟨1, rfl⟩)
      exact Subtype.ext h.eq
  commutator α β hα hβ h := by
    have hsl := simplyLaced_of_tag hτ
    have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
    have hab : α ≠ β := fun e => by
      rw [e, iform_self_eq_two hsl hβ] at h
      exact absurd h (by decide)
    have hne : α ≠ -β := ne_neg_of_iform hsl hβ (by omega)
    obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit τ hτ' hα hβ hab hne).1
      (isRoot_add hsl hα hβ h)
    refine Subtype.ext ?_
    rw [coe_commutatorElement_adjointGroup, hF K 1 1, mul_one, mul_one]
    congr 1
    rcases hC with hC | hC <;> rw [hC]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

theorem adjointRoots_x
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (α : Fin τ.rank → ℤ) :
    (((adjointRoots (K := K) hτ).x α : adjointGroup τ K) : ModGL τ K) = pinnedX τ K α 1 :=
  rfl

variable [Finite K]

theorem posUnipotent_le_closure
    (hK : Nat.card K = 2) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (posUnipotent τ K).subgroupOf (adjointGroup τ K) ≤ Subgroup.closure
      {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ (adjointRoots (K := K) hτ).x α = g} := by
  have : Fintype K := Fintype.ofFinite K
  have hc : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases h0 : c = 0
    · exact Or.inl h0
    · right
      have h := FiniteField.pow_card_sub_one_eq_one c h0
      rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h
  set L := Subgroup.closure
    {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ (adjointRoots (K := K) hτ).x α = g}
  have hU : posUnipotent τ K ≤ L.map (adjointGroup τ K).subtype := by
    rw [posUnipotent, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨α, ⟨hα, hαp⟩, c, rfl⟩
    rcases hc c with rfl | rfl
    · rw [pinnedX_zero]
      exact one_mem _
    · exact ⟨(adjointRoots (K := K) hτ).x α, Subgroup.subset_closure ⟨α, hα, hαp, rfl⟩, rfl⟩
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hU (Subgroup.mem_subgroupOf.1 hu)
  have : v = u := Subtype.ext hvu
  rwa [← this]

theorem ker_eq_bot_of_adjointGroup_two
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* adjointGroup τ K) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have := finite_modGL (τ := τ) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  refine (adjointRoots hτ).ker_eq_bot (simplyLaced_of_tag hτ) (hasDecomp hτ)
    ((posUnipotent τ K).subgroupOf (adjointGroup τ K)) ⟨hUp.toSylow hUi, by simp⟩
    (posUnipotent_le_closure hK hτ) ?_ hη hC h2
  rw [card_subgroupOf_of_le (posUnipotent_le_adjointGroup (K := K)), card_posUnipotent, hK]

end CFSG.LieType.Chevalley.SimplyLacedCover

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley SimplyLacedCover
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem untwisted_field_two_central_two_cover_trivial
    {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {E : Type*} {J : Type} [Group E] [Group J] [Finite E]
    [Group.IsPerfect E] (η : E →* J) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : UntwistedChevalleyModel J τ (2 ^ 1)) : η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hJ
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK
  set η' : E →* adjointGroup τ K := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_adjointGroup_two hτ (by rw [hK]; rfl) η' (e.surjective.comp hη)
    (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

theorem simply_laced_exceptional_field_two_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hJ : LieModel J t 0 2 1) : η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · rcases ht with rfl | rfl | rfl <;> exact absurd hc (by decide)
  · rcases ht with rfl | rfl | rfl
    · exact untwisted_field_two_central_two_cover_trivial (Or.inl rfl) η hη hC h2 hX.2
    · exact untwisted_field_two_central_two_cover_trivial (Or.inr (Or.inl rfl)) η hη hC h2 hX.2
    · exact untwisted_field_two_central_two_cover_trivial (Or.inr (Or.inr rfl)) η hη hC h2 hX.2
  · rcases ht with rfl | rfl | rfl <;> exact absurd hr (by decide)
  · rcases ht with rfl | rfl | rfl <;> exact absurd hs (by decide)

end CFSG.LieType.Chevalley
