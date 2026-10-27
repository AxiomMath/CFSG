module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem eq_bot_of_perfect_of_le_odd {Y : Type*} [Group Y] [Finite Y] {P O : Subgroup Y}
    (hP : ⁅P, P⁆ = P) (hPO : P ≤ O) (hO : Odd (Nat.card O)) : P = ⊥ := by
  have hodd : Odd (Nat.card P) := Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le hPO)
  exact RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable (Subgroup.isPerfect_iff.mpr hP)
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem mem_normalizer_of_le_centralizer {Y : Type*} [Group Y] [Finite Y] {L K : Subgroup Y}
    (hL : IsComponent L) (hKL : K ≤ L) (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) {β : Y}
    (hβ : K ≤ centralizer ({β} : Set Y)) : β ∈ normalizer (L : Set Y) := by
  have hconj : ∀ g : Y, K ≤ centralizer ({g} : Set Y) →
      LocalAnalysis.ComponentInitial.conjSub g L = L := by
    intro g hg
    have hKc : K ≤ LocalAnalysis.ComponentInitial.conjSub g L := fun k hk => by
      refine ⟨k, hKL hk, ?_⟩
      have hc := mem_centralizer_singleton_iff.mp (hg hk)
      change g * k * g⁻¹ = k
      rw [← hc, mul_inv_cancel_right]
    rcases LocalCores.distinct_components_commute
      (LocalAnalysis.ComponentInitial.isComponent_conjSub hL g) hL with h | h
    · exact h
    · refine absurd ?_ hK1
      rw [← hK, eq_bot_iff, ← h]
      exact commutator_mono hKc hKL
  have hβ' : K ≤ centralizer ({β⁻¹} : Set Y) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (by
      have hc := mem_centralizer_singleton_iff.mp (hβ hk)
      calc k * β⁻¹ = β⁻¹ * (β * k) * β⁻¹ := by group
        _ = β⁻¹ * (k * β) * β⁻¹ := by rw [hc]
        _ = β⁻¹ * k := by group)
  exact LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le (hconj β hβ).le
    (hconj β⁻¹ hβ').le

theorem isPGroup_zpowers_of_pow {Y : Type*} [Group Y] {β : Y} (hβ : ∃ n : ℕ, β ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers β) := by
  obtain ⟨n, hn⟩ := hβ
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])

variable {X : Type*} [Group X] [Finite X]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 X)

omit [Finite X] in
theorem map_pLayer_le_layer : (pLayer X 2).map π ≤ layer (X ⧸ pPrimeCore 2 X) := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  rw [← map_le_iff_le_comap, hLK]
  exact le_sSup hK

theorem isPComponent_map_centralizer {β : X} (hβ : ∃ n : ℕ, β ^ 2 ^ n = 1) {M : Subgroup X}
    (hMC : M ≤ centralizer ({β} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({β} : Set X)))) :
    M.map π ≤ centralizer ({π β} : Set (X ⧸ pPrimeCore 2 X)) ∧
      IsPComponent 2 ((M.map π).subgroupOf (centralizer ({π β} : Set (X ⧸ pPrimeCore 2 X)))) := by
  have hc := OddQuot.centralizer_map_eq (isPGroup_zpowers_of_pow hβ)
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hc
  have h := OddQuot.isPComponent_map π OddQuot.not_two_dvd_card_ker hMC hM
  rw [← hc] at h
  exact ⟨(map_mono hMC).trans hc.ge, h⟩

theorem le_pLayer_of_isPComponent_centralizer (hX : LBalance.SchreierSections X) {β : X}
    (hβ : ∃ n : ℕ, β ^ 2 ^ n = 1) {M : Subgroup X} (hMC : M ≤ centralizer ({β} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({β} : Set X)))) : M ≤ pLayer X 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_centralizer_element_le hX hβ
  rw [LBalance.Asm.lBalancePLayer_top] at h1
  exact le_trans (le_sSup ((CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance 2 _ M
    hMC).mp hM)) h1

theorem exists_pComponent_of_map_eq {L₀ : Subgroup (X ⧸ pPrimeCore 2 X)} (hL₀ : IsComponent L₀)
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) (hKL : K.map π = L₀) :
    ∃ L : Subgroup X, IsPComponent 2 L ∧ K ≤ L ∧ L ≤ K ⊔ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL, hLm⟩ := CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 L₀ hL₀
  set L := CatalogueBPrimeJoin.canonicalPrimeLift 2 L₀ with hLdef
  have hsup : ∀ M N : Subgroup X, M.map π ≤ N.map π → M ≤ N ⊔ pPrimeCore 2 X := by
    intro M N h
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 X), ← comap_map_eq]
    exact (le_comap_map π M).trans (comap_mono h)
  have hsol : Group.IsSolvable (pPrimeCore 2 X) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ OddQuot.odd_card_pPrimeCore
  have hLs : L.IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).mp hL).1
  refine ⟨L, hL, ?_, hsup L K (by rw [hLm, hKL])⟩
  exact RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hLs
    (Subgroup.isPerfect_iff.mpr hK) (hsup K L (by rw [hLm, hKL]))

end CFSG.ComponentClassification.GSThmB.Pump516
