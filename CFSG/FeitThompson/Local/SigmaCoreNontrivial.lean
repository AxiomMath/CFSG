module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Local.LargestPrimeCharacteristicSylow
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem ne_bot_of_isCoatom (hna : ¬ IsMulCommutative G) [Nontrivial G] {M : Subgroup G}
    (hM : IsCoatom M) : M ≠ ⊥ := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hne : Subgroup.zpowers x ≠ ⊥ := fun h => hx (by simpa [h] using Subgroup.mem_zpowers x)
  have htop : Subgroup.zpowers x = ⊤ := hM.2 _ (bot_lt_iff_ne_bot.2 hne)
  have : IsCyclic G := ⟨x, fun y => by
    change y ∈ Subgroup.zpowers x
    rw [htop]; exact Subgroup.mem_top y⟩
  exact hna inferInstance

theorem sigmaPrimes_nonempty [Finite G] (hG : IsOddOrderMinimalSimple G)
    {M : Subgroup G} (hM : IsCoatom M) : (sigmaPrimes M).Nonempty := by
  have := hG.isSimpleGroup
  have := hG.nontrivial
  have hsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hMbot : M ≠ ⊥ := ne_bot_of_isCoatom hG.not_isMulCommutative hM
  have : Nontrivial ↥M := M.nontrivial_iff_ne_bot.2 hMbot
  rcases Set.eq_empty_or_nonempty (alphaPrimes ↥M) with hα | ⟨p, hp⟩
  ·
    have hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw ↥M) ≤ 2 := by
      intro p hp
      have hnot : p ∉ alphaPrimes ↥M := by rw [hα]; exact Set.notMem_empty p
      have h3 : ¬ (3 ≤ elementaryAbelianPRank p ↥M) := fun h => hnot (mem_alphaPrimes.2 ⟨hp, h⟩)
      exact le_trans (elementaryAbelianPRank_subgroup_le hp.one_lt _) (by omega)
    obtain ⟨hqp, hqM, hqmax⟩ := max'_primeFactors_natCard_spec ↥M
    obtain ⟨Q, hQchar, hQcard⟩ :=
      exists_characteristic_natCard_eq_pow_factorization
        (odd_natCard_subgroup hG.odd_natCard M) hrank hqp hqM hqmax
    have := hQchar
    set q := (Nat.card ↥M).primeFactors.max' (primeFactors_natCard_nonempty ↥M) with hqdef
    set P : Subgroup G := Q.map M.subtype with hPdef
    have hPM : P ≤ M := Subgroup.map_subtype_le _
    have hPcard : Nat.card ↥P = q ^ (Nat.card ↥M).factorization q := by
      rw [hPdef, Subgroup.card_map_of_injective M.subtype_injective, hQcard]
    have hv : 0 < (Nat.card ↥M).factorization q :=
      hqp.factorization_pos_of_dvd Nat.card_pos.ne' hqM
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hPcard
      have : q ∣ 1 := hPcard ▸ dvd_pow_self q hv.ne'
      exact hqp.one_lt.ne' (Nat.dvd_one.1 this)
    have hMN : M ≤ normalizer (P : Set G) :=
      le_trans Subgroup.le_normalizer (normalizer_le_normalizer_map_subtype M Q)
    have hlt : normalizer (P : Set G) < ⊤ :=
      normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hqp hPbot (IsPGroup.of_card hPcard)
    have hNM : normalizer (P : Set G) = M := by
      by_contra hne
      exact hlt.ne (hM.2 _ (lt_of_le_of_ne hMN (Ne.symm hne)))
    exact ⟨q, (mem_sigmaPrimes_iff_exists_subgroup hqp).2 ⟨hqM, P, hPM, hPcard, hNM.le⟩⟩
  · exact ⟨p, alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hp⟩

theorem sigmaCore_ne_bot_of_mem_sigmaPrimes [Finite G] {M : Subgroup G} {p : ℕ}
    (hp : p ∈ sigmaPrimes M)
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M) :
    sigmaCore M ≠ ⊥ := by
  have hpp : p.Prime := prime_of_mem_sigmaPrimes hp
  have hdvd : p ∣ Nat.card ↥M := dvd_natCard_of_mem_sigmaPrimes hp
  set S := (sigmaCore M).subgroupOf M with hSdef
  have hmul : Nat.card ↥S * S.index = Nat.card ↥M := S.card_mul_index
  have hcard : Nat.card ↥S = Nat.card ↥(sigmaCore M) := by
    rw [hSdef, ← Subgroup.card_subtype M ((sigmaCore M).subgroupOf M),
      Subgroup.map_subgroupOf_eq_of_le hHall.le]
  have hnot : ¬ p ∣ S.index := fun h =>
    hHall.2.notMem_of_mem_primeFactors_index p
      (Nat.mem_primeFactors.2 ⟨hpp, h, Subgroup.index_ne_zero_of_finite⟩) hp
  have hdvdS : p ∣ Nat.card ↥S := by
    rcases (Nat.Prime.dvd_mul hpp).1 (hmul ▸ hdvd) with h | h
    · exact h
    · exact absurd h hnot
  intro hbot
  rw [hcard, hbot, Subgroup.card_bot] at hdvdS
  exact hpp.one_lt.ne' (Nat.dvd_one.1 hdvdS)

theorem FBG_sigma_core_nontrivial
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FBG_sigma_core_nontrivial.{u} := by
  intro G _ _ hG M hM
  obtain ⟨p, hp⟩ := sigmaPrimes_nonempty hG hM
  obtain ⟨hHall, -, -⟩ := h₁ G hG M hM
  exact ⟨⟨p, hp⟩, sigmaCore_ne_bot_of_mem_sigmaPrimes hp hHall⟩

end

end CFSG.FeitThompson.Proofs
