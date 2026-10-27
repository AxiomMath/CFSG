module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Local.OddFrobeniusComplementPrimeSubgroupsNormal
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

theorem FNI_tau_three_hall_fixed_centralizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau_three_hall_fixed_centralizer.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ hME hsplit X hXE₃ hXne
  have hGmin : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have := hG.isSimpleGroup
  have hE₃E : E₃ ≤ E := hsplit.le_E₃
  have hEM : E ≤ M := hME.le
  refine le_antisymm ?_
    (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hXE₃)))
  obtain ⟨p, hp, hpX⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card X := by
    have h1 : Nat.card X ≠ 1 := fun h => hXne (Subgroup.card_eq_one.1 h)
    exact ⟨(Nat.card X).minFac, Nat.minFac_prime h1, Nat.minFac_dvd _⟩
  obtain ⟨y, hyX, hy⟩ := exists_mem_orderOf_eq_of_dvd hp hpX
  have hYcard : Nat.card (zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have hYX : zpowers y ≤ X := zpowers_le.2 hyX
  have hpE₃ : p ∣ Nat.card E₃ := hpX.trans (Subgroup.card_dvd_of_le hXE₃)
  have hpτ₃ : p ∈ tau3Primes M := by
    refine (isHallPiSubgroup_iff.1 hsplit.isHall_E₃).1 p ?_
    rw [natCard_subgroupOf hE₃E]
    exact Nat.mem_primeFactors.2 ⟨hp, hpE₃, Nat.card_pos.ne'⟩
  have : IsCyclic ↥E₃ := hsplit.isCyclic_E₃
  have : ((zpowers y).subgroupOf E₃).Characteristic := characteristic_of_isCyclic _
  have hNE₃Y : normalizer (E₃ : Set G) ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
    have h := normalizer_le_normalizer_map_subtype E₃ ((zpowers y).subgroupOf E₃)
    rwa [Subgroup.map_subgroupOf_eq_of_le (hYX.trans hXE₃)] at h
  have hEN : E ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
    hsplit.outer.le_normalizer.trans hNE₃Y
  have hYne : (zpowers y : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    exact hp.one_lt.ne hYcard
  have hYp : IsPGroup p (zpowers y) := IsPGroup.of_card (by rw [pow_one, hYcard])
  obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hYne hYp).ne
  have hET : E ≤ T := hEN.trans hNT
  have hE₃T' : E₃ ≤ ⁅T, T⁆ := hsplit.le_commutator_E₃.trans (Subgroup.commutator_mono hET hET)
  have hτ₁T : ∀ s ∈ (Nat.card E₃).primeFactors, s ∉ tau1Primes T := by
    intro s hs hsτ
    exact not_dvd_natCard_commutator_of_mem_tau1Primes hsτ
      ((Nat.mem_primeFactors.1 hs).2.1.trans (Subgroup.card_dvd_of_le hE₃T'))
  obtain ⟨-, hcent, -⟩ := h₁ G hGmin M hME.isCoatom E hEM hME.isInternalSemidirectProduct
    p (Or.inr hpτ₃) (zpowers y) (hYX.trans (hXE₃.trans (hE₃E.trans hEM))) hYcard T hT hNT
  have hE₃cent : E₃ ≤ centralizer ((sigmaCore M ⊓ T : Subgroup G) : Set G) :=
    hcent E₃ (le_inf hE₃E (hE₃E.trans hET)) hτ₁T
  have hstep : sigmaCore M ⊓ centralizer (X : Set G) ≤ sigmaCore M ⊓ T :=
    inf_le_inf_left _ ((centralizer_le (SetLike.coe_subset_coe.2 hYX)).trans
      ((centralizer_le_normalizer _).trans hNT))
  exact le_inf inf_le_left (hstep.trans (le_centralizer_iff.1 hE₃cent))

end

end CFSG.FeitThompson.Proofs
