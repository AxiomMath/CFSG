module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Chevalley
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank


theorem involutionCentralizersCharTwo_rootWeightDatum {K : Type} [Field K] [Finite K]
    [CharP K 2] (D : RootWeightDatum K) : InvolutionCentralizersCharTwo D.group :=
  fun _ ht => ClassicalInvolution.isCharacteristicP_centralizer_of_rootWeightDatum D ht

theorem involutionCentralizersCharTwo_adjointGroup {τ : Tag} {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    InvolutionCentralizersCharTwo (adjointGroup τ K) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact involutionCentralizersCharTwo_rootWeightDatum (RootWeightDatum.ordinary τ)

theorem involutionCentralizersCharTwo_graphFixedRootGroup (t : TwistTag) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InvolutionCentralizersCharTwo (graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields t Nat.prime_two hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  have hσo : σ ^ t.order = 1 := by
    rw [hσσ', ← hord]
    exact pow_orderOf_eq_one σ'
  have hm := t.order_pos
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      (show Nat.card K = 2 ^ (f * t.order) by rw [hK, ← pow_mul])
  exact involutionCentralizersCharTwo_rootWeightDatum (RootWeightDatum.fixed t σ hσo)

theorem involutionCentralizersCharTwo_exceptional {S : Type} [Group S] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {f : ℕ} (h : ChevalleyExceptionalModel S t 2 f) :
    InvolutionCentralizersCharTwo S := by
  have hf : 1 ≤ f := h.1.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_adjointGroup hf hK)
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 Nat.prime_two hf h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_graphFixedRootGroup _ hf hK σ hσ)
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf h.2
    exact .of_mulEquiv e (involutionCentralizersCharTwo_graphFixedRootGroup _ hf hK σ hσ)

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
