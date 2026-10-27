module

public import CFSG.LieType.Ree.LargeReeFixedGroupSchreier
public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.LieType.Ree.ReeGenericPerfect
public import CFSG.LieType.Chevalley.DiagramFixedModelSchreier

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem nonempty_derivedCentralQuotient_mulEquiv_reeGamma
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (DerivedCentralQuotient (F4.reeGamma K a) ≃* F4.reeGamma K a) := by
  have hperf : ⁅F4.reeGamma K a, F4.reeGamma K a⁆ = F4.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, (ree_generic_fixed_group_perfect F4 a ha K hK).2.1,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hZ := large_Ree_fixed_group_center_trivial a K hK
  have hZ' : Subgroup.center ↥⁅F4.reeGamma K a, F4.reeGamma K a⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL F4.tag K) ∈ F4.reeGamma K a := Subgroup.commutator_le_self _ x.2
    have hcen : (⟨x, hxC⟩ : F4.reeGamma K a) ∈ Subgroup.center (F4.reeGamma K a) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL F4.tag K) ∈ ⁅F4.reeGamma K a, F4.reeGamma K a⁆ := hperf.ge y.2
      have h1 := congrArg (Subtype.val : ↥⁅F4.reeGamma K a, F4.reeGamma K a⁆ → ModGL F4.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext
      (congrArg (Subtype.val : F4.reeGamma K a → ModGL F4.tag K) hcen))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf))⟩

theorem large_Ree_model_Schreier
    (G : Type) [Group G] (p f : ℕ)
    (h : ReeTitsModel G .twistedF4 p f) :
    Finite G ∧ derivedSeries (Outer G) 3 = ⊥ ∧ Group.IsSolvable (Outer G) ∧ p = 2 ∧
    (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧
    ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], f = 2 * a + 1 →
      Nat.card K = p ^ f →
      Nonempty (G ≃* DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then p ^ a else p ^ (a + 1))) →
      Nonempty (G ≃* F4.reeGamma K a) := by
  obtain ⟨hadm, a, hfa, hmodel⟩ := h
  have hp : p = 2 := hadm.2.2.2.1
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  subst hp
  have ha : 1 ≤ a := by omega
  have hiso : ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], f = 2 * a + 1 →
      Nat.card K = 2 ^ f →
      Nonempty (G ≃* DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))) →
      Nonempty (G ≃* F4.reeGamma K a) := by
    intro a' K _ _ _ hfa' hK ⟨e⟩
    have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hfa']
    obtain ⟨E⟩ := nonempty_derivedCentralQuotient_mulEquiv_reeGamma (by omega) hK'
    have e' : G ≃* DerivedCentralQuotient (F4.reeGamma K a') := e.trans (by
      rw [reeGamma_eq_reeFixedGroup]
      exact MulEquiv.refl _)
    exact ⟨e'.trans E⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have := finite_modGL (τ := F4.tag) (K := K)
  have hOut : derivedSeries (Outer G) 3 = ⊥ :=
    derivedSeries_outer_eq_bot_of_mulEquiv E (large_Ree_fixed_group_Schreier a ha K hK').2.2.2
  exact ⟨Finite.of_equiv _ E.symm.toEquiv, hOut, ⟨⟨3, hOut⟩⟩, rfl, ⟨a, ha, hfa⟩, hiso⟩

end ReeTag

end CFSG.LieType.Ree
