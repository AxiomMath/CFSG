module

public import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
public import CFSG.FeitThompson.Local.BetaSylowNormalizerUniqueMaximal
import CFSG.FeitThompson.Local.LargeAbelianNormalNoComplementaryPrime
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {M : Subgroup G}

theorem prime_dvd_natCard_of_isPGroup {p : ℕ} [Finite G] (hp : p.Prime) {X : Subgroup G}
    (hX : X ≠ ⊥) (hXp : IsPGroup p ↥X) : p ∣ Nat.card ↥X :=
  have := Fact.mk hp
  hXp.card_eq_or_dvd.resolve_left fun h => hX (Subgroup.card_eq_one.1 h)

theorem normalizer_le_of_isPiSubgroup_betaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Z : Subgroup G, Z ≠ ⊤ → Group.IsSolvable ↥Z) (hM : IsCoatom M)
    {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y ≠ ⊥) (hYβ : IsPiSubgroup (betaPrimes ↥M) Y) :
    normalizer (Y : Set G) ≤ M := by
  have : Group.IsSolvable ↥Y := hsolv Y fun h => hM.1 (top_le_iff.1 (h ▸ hYM))
  obtain ⟨p, hp, hX⟩ : ∃ p, Nat.Prime p ∧ pCoreIn p Y ≠ ⊥ := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hY (eq_bot_of_forall_pCoreIn_eq_bot fun r hr => h r hr)
  set X := pCoreIn p Y with hXdef
  have hXY : X ≤ Y := pCoreIn_le p Y
  have hXM : X ≤ M := hXY.trans hYM
  have hXp : IsPGroup p ↥X := isPGroup_pCoreIn hp Y
  have hpdvd : p ∣ Nat.card ↥Y :=
    (prime_dvd_natCard_of_isPGroup hp hX hXp).trans (Subgroup.card_dvd_of_le hXY)
  have hpβM : p ∈ betaPrimes ↥M :=
    isPiSubgroup_iff.1 hYβ p (Nat.mem_primeFactors.2 ⟨hp, hpdvd, Nat.card_pos.ne'⟩)
  have hpσ : p ∈ sigmaPrimes M := betaPrimes_subset_sigmaPrimes hna hodd hsolv hM hpβM
  have hpβG : p ∈ betaPrimes G := (mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hpσ).1 hpβM
  have := Fact.mk hp
  obtain ⟨S, hS⟩ := (hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm).exists_le_sylow
  obtain ⟨T, hT⟩ := exists_sylow_coe_eq_map_subtype hpσ S
  have hXT : X ≤ (T : Subgroup G) := by
    rw [hT, ← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hS
  have hTM : (T : Subgroup G) ≤ M := hT ▸ Subgroup.map_subtype_le _
  obtain ⟨M', hM'⟩ := exists_isUniqueMaximalOvergroup_inf_normalizer_of_mem_betaPrimes
    hna hodd hsolv hpβG T hXT
  have hMM' : M = M' := hM'.eq_of_isCoatom hM (inf_le_left.trans hTM)
  have hne : normalizer (X : Set G) ≠ ⊤ := (normalizer_lt_top_of_isPGroup hna hp hX hXp).ne
  have hNX : normalizer (X : Set G) ≤ M := hMM' ▸ hM'.le_of_ne_top inf_le_right hne
  exact (normalizer_le_normalizer_pCoreIn p Y).trans hNX

theorem normalizer_le_of_forall_mem_betaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Z : Subgroup G, Z ≠ ⊤ → Group.IsSolvable ↥Z) (hM : IsCoatom M)
    {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y ≠ ⊥)
    (hYβ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥Y → q ∈ betaPrimes ↥M) :
    normalizer (Y : Set G) ≤ M :=
  normalizer_le_of_isPiSubgroup_betaPrimes hna hodd hsolv hM hYM hY
    (isPiSubgroup_iff.2 fun q hq =>
      hYβ q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq))

theorem normalizer_betaCore_le [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Z : Subgroup G, Z ≠ ⊤ → Group.IsSolvable ↥Z)
    (hM : IsCoatom M) (hB : betaCore M ≠ ⊥) :
    normalizer ((betaCore M : Subgroup G) : Set G) ≤ M :=
  normalizer_le_of_isPiSubgroup_betaPrimes hna hodd hsolv hM (betaCore_le M) hB
    (isPiSubgroup_betaCore M)

end

end CFSG.FeitThompson
