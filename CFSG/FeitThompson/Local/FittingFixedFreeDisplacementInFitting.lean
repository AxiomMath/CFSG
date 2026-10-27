module

import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
public import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem map_fittingRaw_subtype_eq_fittingOfNormal [Finite G] (K : Subgroup G) :
    (fittingRaw ↥K).map K.subtype = fittingOfNormal K := by
  rw [← subgroupOf_fittingOfNormal K, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 (fittingOfNormal_le K)]

theorem commutator_le_fittingOfNormal [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R)) (hRprime : (Nat.card ↥R).Prime)
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    ⁅K, R⁆ ≤ fittingOfNormal K := by
  have hDnormal : (⁅K, R⁆ : Subgroup G).Normal :=
    commutator_normal_of_sup_eq_top hKR.sup_eq_top
  rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
  refine le_map_fittingRaw_subtype_of_forall_isChiefFactor
    (Subgroup.commutator_le_left K R) fun U V hchief hUF => ?_
  exact commutator_commutator_le_of_isChiefFactor_le_fitting hodd hKR hcop hRprime hp hKF hcent
    (by rwa [map_fittingRaw_subtype_eq_fittingOfNormal] at hUF) hchief

theorem commutator_le_fittingOfNormal_of_natCard_quotient [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R)) (hRprime : (Nat.card ↥R).Prime)
    {p a : ℕ} (hp : p.Prime) (hKF : Nat.card (↥K ⧸ fittingRaw ↥K) = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    ⁅K, R⁆ ≤ fittingOfNormal K :=
  commutator_le_fittingOfNormal hodd hKR hcop hRprime hp
    ((relIndex_fittingOfNormal K).trans hKF) hcent

theorem subgroupOf_commutator_le_fittingRaw [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R)) (hRprime : (Nat.card ↥R).Prime)
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    (⁅K, R⁆ : Subgroup G).subgroupOf K ≤ fittingRaw ↥K :=
  (le_map_fittingRaw_subtype_iff (Subgroup.commutator_le_left K R)).1
    (map_fittingRaw_subtype_eq_fittingOfNormal K ▸
      commutator_le_fittingOfNormal hodd hKR hcop hRprime hp hKF hcent)

end CFSG.FeitThompson
