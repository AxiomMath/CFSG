module

public import CFSG.LieType.Ree.SmallReeFixedGroupSchreier
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem nonempty_derivedCentralQuotient_mulEquiv_of_perfect {M : Type} [Group M]
    {H : Subgroup M} (hperf : ⁅H, H⁆ = H) (hZ : Subgroup.center H = ⊥) :
    Nonempty (DerivedCentralQuotient H ≃* H) := by
  have hZ' : Subgroup.center ↥⁅H, H⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hcen : (⟨x, hperf.le x.2⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (Subtype.val : ↥⁅H, H⁆ → M)
        (Subgroup.mem_center_iff.1 hx ⟨y, hperf.ge y.2⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext (congrArg (Subtype.val : H → M) hcen))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf))⟩

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

theorem nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (DerivedCentralQuotient (G2.reeGamma K a) ≃* G2.reeGamma K a) := by
  refine nonempty_derivedCentralQuotient_mulEquiv_of_perfect ?_
    (small_Ree_fixed_group_center_trivial a K hK).1
  rw [← Subgroup.map_subtype_commutator, (ree_generic_fixed_group_perfect G2 a ha K hK).2.1,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end ReeTag

open ReeTag

theorem small_Ree_model_Schreier
    (G : Type) [Group G] (p f : ℕ)
    (h : ReeTitsModel G .twistedG2 p f) :
    Finite G ∧ Group.IsSolvable (Outer G) ∧ p = 3 ∧ (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧
    ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K G2.prime], f = 2 * a + 1 →
      Nat.card K = p ^ f →
      Nonempty (G ≃* DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
        fun i => if i ∈ reeG2Long then p ^ a else p ^ (a + 1))) →
      Nonempty (G ≃* G2.reeGamma K a) := by
  obtain ⟨hadm, a, hfa, hmodel⟩ := h
  have hp : p = 3 := hadm.2.2.2.1
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  subst hp
  have ha : 1 ≤ a := by omega
  have hiso : ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K G2.prime], f = 2 * a + 1 →
      Nat.card K = 3 ^ f →
      Nonempty (G ≃* DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
        fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1))) →
      Nonempty (G ≃* G2.reeGamma K a) := by
    intro a' K _ _ _ hfa' hK ⟨e⟩
    have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa']
    obtain ⟨E⟩ := nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 (by omega) hK'
    have e' : G ≃* DerivedCentralQuotient (G2.reeGamma K a') := e.trans (by
      rw [reeGamma_eq_reeFixedGroup]
      exact MulEquiv.refl _)
    exact ⟨e'.trans E⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hfa]
  have := finite_modGL (τ := G2.tag) (K := K)
  have hOut : Group.IsSolvable (Outer G) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism E).2.2
      (small_Ree_fixed_group_Schreier a ha K hK')
  exact ⟨Finite.of_equiv _ E.symm.toEquiv, hOut, rfl, ⟨a, ha, hfa⟩, hiso⟩

end CFSG.LieType.Ree
