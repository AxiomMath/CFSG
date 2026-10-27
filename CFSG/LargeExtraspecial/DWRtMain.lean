module

public import CFSG.LargeExtraspecial.DWFldMain
public import CFSG.LargeExtraspecial.DWRtUntwisted
public import CFSG.LargeExtraspecial.DWRtTwisted
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LargeExtraspecial.DW

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

theorem not_isTransClass34_of_untwistedChevalleyModel
    {X : Type} [Group X] {τ : Tag} {f : ℕ} (hf : 2 ≤ f) (h : UntwistedChevalleyModel X τ (2 ^ f))
    (D : Set X) : ¬ IsTransClass34 D := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have hZ := center_adjointGroup_eq_bot (τ := τ) (K := K)
  let e' : X ≃* adjointGroup τ K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have := charP_two_of_card_eq hcard
  have hK : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  intro hD
  exact not_isTransClass34_adjointGroup hK _ (hD.image e')

theorem not_isTransClass34_of_twistedChevalleyModel
    {X : Type} [Group X] {t : TwistTag} {f : ℕ} (hf : 2 ≤ f)
    (h : TwistedChevalleyModel X t (2 ^ f)) (D : Set X) : ¬ IsTransClass34 D := by
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card t Nat.prime_two (by omega) h
  obtain ⟨σ', hσ', -, hL, -⟩ :=
    finite_graph_field_parameter_fields t Nat.prime_two (by omega) K hcard
  obtain rfl : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  have hcard' : Nat.card K = 2 ^ (f * t.order) := by rw [hcard, ← pow_mul]
  have := charP_two_of_card_eq hcard'
  have hL4 : ∀ a, 4 ≤ Nat.card (orbitField t K σ'.toRingHom a) := fun a => by
    rw [hL a]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      _ ≤ (2 ^ f) ^ (t.orbit a).card :=
        Nat.le_self_pow (Nat.pos_iff_ne_zero.1 (t.card_orbit_pos a)) _
  intro hD
  exact not_isTransClass34_graphFixedRootGroup σ' hL4 _ (hD.image e)

theorem not_isTransClass34_of_lieModel_exceptional
    {X : Type} [Group X] {t : StatedLieTag} {f : ℕ} (hf : 2 ≤ f)
    (ht : t ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (hX : LieModel X t 0 2 f) (D : Set X) : ¬ IsTransClass34 D := by
  have hm : ChevalleyExceptionalModel X t 2 f := by
    rcases hX with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by revert ht; cases t <;> decide)
    · exact h
    · exact absurd h (by revert ht; cases t <;> decide)
    · exact absurd h (by revert ht; cases t <;> decide)
  obtain ⟨-, hm⟩ := hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_isTransClass34_of_untwistedChevalleyModel hf hm D
  · exact not_isTransClass34_of_twistedChevalleyModel hf hm D
  · exact not_isTransClass34_of_untwistedChevalleyModel hf hm D
  · exact not_isTransClass34_of_untwistedChevalleyModel hf hm D
  · exact not_isTransClass34_of_twistedChevalleyModel hf hm D
  · exact not_isTransClass34_of_untwistedChevalleyModel hf hm D
  · exact not_isTransClass34_of_untwistedChevalleyModel hf hm D

theorem dw2RootSL2Input
    : DW2RootSL2Input := by
  intro X _ _ t f hf ht hX D hD
  exact absurd hD (not_isTransClass34_of_lieModel_exceptional hf ht hX D)

theorem dw2FieldInput
    : DW2FieldInput :=
  dw2FieldInput_of dw2RootSL2Input

end CFSG.LargeExtraspecial.DW
