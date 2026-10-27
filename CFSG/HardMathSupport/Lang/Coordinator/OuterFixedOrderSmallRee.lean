module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial

section


theorem card_reeGamma_G2_eq {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (ReeTag.G2.reeGamma K a) =
      (3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  rw [h, mul_right_comm]

theorem nonempty_derivedCentralQuotient_reeGamma_G2 {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (ReeTag.G2.reeGamma K a) ≃*
      ReeTag.G2.reeGamma K a) := by
  have hcomm := (ReeTag.ree_generic_fixed_group_perfect .G2 a ha K hK).2.1
  have hD : ⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ = ReeTag.G2.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e₁ : ↥⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ ≃* ReeTag.G2.reeGamma K a :=
    MulEquiv.subgroupCongr hD
  have hZ : Subgroup.center ↥⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center (ReeTag.G2.reeGamma K a) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e₁.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [ReeTag.center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e₁.injective (hz'.trans (map_one e₁).symm))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₁)⟩

private theorem card_fixedSubgroup_outer_smallRee (a : ℕ) (ha : 1 ≤ a) (F : Type) [Field F]
    [Finite F] [CharP F ReeTag.G2.prime] (hF : Nat.card F = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut (ReeTag.G2.reeGamma F a)) (hα : α ^ p = 1)
    (hαout : α ∉ inner (ReeTag.G2.reeGamma F a)) :
    ∃ b : ℕ, 2 * a + 1 = p * (2 * b + 1) ∧ Nat.card (fixedSubgroup α) =
      (3 ^ (2 * b + 1)) ^ 3 * ((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1) := by
  obtain ⟨⟨d, hd⟩, δ, σ, -, hδ, hk, hfix⟩ :=
    small_Ree_odd_prime_field_descent a ha F hF hp hp2 α hα hαout
  have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  have hbd : (d - 1) / 2 = b := by omega
  rw [hd'] at hk hfix
  rw [hbd] at hfix
  set k := fixSubfield σ
  have hkb : Nat.card k = 3 ^ (2 * b + 1) := by rw [hk, hb]
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkb]; exact (pow_pos (by norm_num) _).ne')
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP k ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hkb
  have hcard1 : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup
      (ReeTag.G2.reeGammaFieldAut F a σ)) :=
    card_fixedSubgroup_eq_of_intertwine δ α _ fun x => by
      rw [← hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hcard2 : Nat.card (fixedSubgroup (ReeTag.G2.reeGammaFieldAut F a σ)) =
      Nat.card (ReeTag.G2.reeGamma k b) := by
    have h1 := Subgroup.card_map_of_injective
      (K := (ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _))
      (Subgroup.subtype_injective (ReeTag.G2.reeGamma F a))
    have h2 := Subgroup.card_map_of_injective (K := ReeTag.G2.reeGamma k b)
      (baseChangeGL_injective k.subtype)
    rw [hfix, h2] at h1
    exact h1.symm
  exact ⟨b, by rw [hd, hb], by rw [hcard1, hcard2, card_reeGamma_G2_eq hkb]⟩

theorem small_Ree_outer_fixed_order (a : ℕ) (ha : 1 ≤ a) (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.G2.prime] (hF : Nat.card F = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (α : MulAut (ReeTag.G2.reeGamma F a)) (hα : α ^ p = 1)
    (hαout : α ∉ inner (ReeTag.G2.reeGamma F a)) :
    ∃ d : ℕ, 2 * a + 1 = p * d ∧
      Nat.card (fixedSubgroup α) ∣
        (3 ^ d) ^ 3 * ((3 ^ d) ^ 3 + 1) * (3 ^ d - 1) := by
  obtain ⟨b, hd, hcard⟩ := card_fixedSubgroup_outer_smallRee a ha F hF hp hp2 α hα hαout
  exact ⟨2 * b + 1, hd, by rw [hcard]⟩

theorem outerFixedOrderBoundAt_twistedG2 : OuterFixedOrderBoundAt .twistedG2 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  obtain ⟨-, -, -, hℓ, -, hf3⟩ := hadm
  subst hℓ
  have hR : ReeTitsModel K .twistedG2 3 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨-, a, hfa, hrel⟩ := hR
  obtain ⟨F, _, _, _, hF, ⟨e₁⟩⟩ := (reeTitsRelationModel_iff .G2 K f a).1 hrel
  have ha : 1 ≤ a := by omega
  have hF' : Nat.card F = 3 ^ (2 * a + 1) := hfa ▸ hF
  obtain ⟨e₂⟩ := nonempty_derivedCentralQuotient_reeGamma_G2 (K := F) ha hF'
  set e := e₁.trans e₂ with he
  set β := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ inner (ReeTag.G2.reeGamma F a) :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  obtain ⟨d, hd, hdvd⟩ := small_Ree_outer_fixed_order a ha F hF' hp hp2 β hβp hβout
  refine ⟨d, hfa ▸ hd, ?_⟩
  rw [← card_fixedSubgroup_congr e α]
  exact hdvd

end

end CFSG.HardMathSupport.Lang.Coordinator
