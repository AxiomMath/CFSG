module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic
import CFSG.FeitThompson.Local.RankTwoSectionChiefFactorCentralization
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem map_subtype_fittingRaw_top (G : Type*) [Group G] [Finite G] :
    (fittingRaw ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = fittingRaw G := by
  have h : ((⊤ : Subgroup G).subtype)
      = ((Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) : (⊤ : Subgroup G) →* G) := rfl
  rw [h, map_fittingRaw_of_mulEquiv]

theorem exists_prime_relIndex_eq_pow_of_isChiefFactor [Finite G] [Group.IsSolvable G]
    {U V : Subgroup G} (h : IsChiefFactor U V) :
    ∃ p : ℕ, p.Prime ∧ ∃ k : ℕ, V.relIndex U = p ^ k := by
  have := h.normal_num
  have := h.normal_den
  obtain ⟨r, d, hr, -, e, -⟩ := exists_prime_mulEquiv_isIrreducible_of_isChiefFactor U V h
  refine ⟨r, hr, d, ?_⟩
  have h2 : V.relIndex U = Nat.card (↥U ⧸ V.subgroupOf U) := Subgroup.index_eq_card _
  rw [h2, Nat.card_congr (quotientFactorMulEquiv U V).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem commutator_le_fittingRaw [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    (hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2) :
    _root_.commutator G ≤ fittingRaw G := by
  have key : _root_.commutator G ≤ (fittingRaw ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := by
    refine le_map_fittingRaw_subtype_of_forall_isChiefFactor le_top fun U V hUV hU => ?_
    rw [map_subtype_fittingRaw_top] at hU
    obtain ⟨p, hp, k, hk⟩ := exists_prime_relIndex_eq_pow_of_isChiefFactor hUV
    exact commutator_le_of_isChiefFactor_of_elementaryAbelianPRank_le_two hodd hp
      (N := fittingRaw G) (hrank p hp) hUV ⟨k, hk⟩ hU
  rwa [map_subtype_fittingRaw_top] at key

theorem closure_setOf_inv_mul_inv_mul_mul_le_fittingRaw [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G))
    (hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2) :
    Subgroup.closure {g : G | ∃ x y, x⁻¹ * y⁻¹ * x * y = g} ≤ fittingRaw G := by
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator]
  exact commutator_le_fittingRaw hodd hrank

theorem isNilpotent_commutator [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    (hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2) :
    Group.IsNilpotent ↥(_root_.commutator G) :=
  Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (commutator_le_fittingRaw hodd hrank))

end

end CFSG.FeitThompson
