module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.LargestPrimeCharacteristicSylow
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {M : Subgroup G}

theorem not_isUniqueMaximalOvergroup_bot [Finite G] (hna : ¬ IsMulCommutative G)
    (M : Subgroup G) : ¬ IsUniqueMaximalOvergroup (⊥ : Subgroup G) M := by
  intro h
  have hall : ∀ g : G, g ∈ M := by
    intro g
    have hz : zpowers g ≠ ⊤ := by
      intro hzt
      refine hna ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨m, rfl⟩ : a ∈ zpowers g := hzt ▸ mem_top a
      obtain ⟨n, rfl⟩ : b ∈ zpowers g := hzt ▸ mem_top b
      exact zpow_mul_comm g m n
    exact h.le_of_ne_top bot_le hz (mem_zpowers g)
  exact h.isCoatom.1 (eq_top_iff.2 fun g _ => hall g)

theorem not_isUniqueMaximalOvergroup_of_isPiSubgroup_compl_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    {K : Subgroup G} (hKM : K ≤ M) (hK : IsPiSubgroup (sigmaPrimes M)ᶜ K)
    {N : Subgroup G} : ¬ IsUniqueMaximalOvergroup K N := by
  intro h
  have hNM : M = N := h.eq_of_isCoatom hM hKM
  rw [← hNM] at h
  clear hNM
  rcases eq_or_ne K ⊥ with rfl | hKbot
  · exact not_isUniqueMaximalOvergroup_bot hna M h
  have hMtop : M ≠ ⊤ := hM.1
  have hMsolv : Group.IsSolvable ↥M := hsolv M hMtop
  have hKsub : IsPiSubgroup (sigmaPrimes M)ᶜ (K.subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun p hp => isPiSubgroup_iff.1 hK p ?_
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv] at hp
  obtain ⟨E', hE', hKE'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hKsub
  set E : Subgroup G := E'.map M.subtype with hEdef
  have hEM : E ≤ M := map_subtype_le _
  have hcardE : Nat.card ↥E = Nat.card ↥E' := card_map_of_injective M.subtype_injective
  have hKE : K ≤ E := by
    rw [hEdef, ← map_subgroupOf_eq_of_le hKM]; exact map_mono hKE'
  have hEtop : E ≠ ⊤ := fun hEt => hMtop (top_le_iff.1 (hEt ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hsolv E hEtop
  have hEodd : Odd (Nat.card ↥E) := odd_natCard_subgroup hodd E
  have hEpi : ∀ p ∈ (Nat.card ↥E).primeFactors, p ∉ sigmaPrimes M := by
    refine fun p hp => isPiSubgroup_iff.1 hE'.isPiSubgroup p ?_
    rwa [hcardE] at hp
  have hEnt : Nontrivial ↥E :=
    (Subgroup.nontrivial_iff_ne_bot E).2 fun hEb => hKbot (le_bot_iff.1 (hEb ▸ hKE))
  have hrank2 : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥E ≤ 2 := by
    intro p hp
    by_contra hlt
    have h3 : 3 ≤ elementaryAbelianPRank p ↥E := by omega
    have hpα : p ∈ alphaPrimes ↥M :=
      mem_alphaPrimes.2 ⟨hp, h3.trans (elementaryAbelianPRank_le_of_le hp.one_lt hEM)⟩
    have hpσ : p ∈ sigmaPrimes M := alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM hpα
    have hpdvd : p ∣ Nat.card ↥E := (one_le_elementaryAbelianPRank_iff hp).1 (by omega)
    exact hEpi p (Nat.mem_primeFactors.2 ⟨hp, hpdvd, Nat.card_pos.ne'⟩) hpσ
  have hFrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw ↥E) ≤ 2 :=
    fun p hp => (elementaryAbelianPRank_subgroup_le hp.one_lt _).trans (hrank2 p hp)
  obtain ⟨hqp, hqE, hqmax⟩ := max'_primeFactors_natCard_spec ↥E
  set q := (Nat.card ↥E).primeFactors.max' (primeFactors_natCard_nonempty ↥E) with hqdef
  obtain ⟨Q, hQchar, hQcard⟩ :=
    exists_characteristic_natCard_eq_pow_factorization (G := ↥E) hEodd hFrank hqp hqE hqmax
  set P : Subgroup G := Q.map E.subtype with hPdef
  have hPE : P ≤ E := map_subtype_le _
  have hPM : P ≤ M := hPE.trans hEM
  have hPcard : Nat.card ↥P = q ^ (Nat.card ↥E).factorization q := by
    rw [hPdef, card_map_of_injective E.subtype_injective, hQcard]
  have hqπ : q ∉ sigmaPrimes M :=
    hEpi q (Nat.mem_primeFactors.2 ⟨hqp, hqE, Nat.card_pos.ne'⟩)
  have hidx : ¬ q ∣ E'.index := fun hdvd => by
    have hmem := isPiNumber_iff.1 hE'.index q
      (Nat.mem_primeFactors.2 ⟨hqp, hdvd, index_ne_zero_of_finite⟩)
    rw [compl_compl] at hmem
    exact hqπ hmem
  have hfacM : (Nat.card ↥M).factorization q = (Nat.card ↥E).factorization q := by
    have h1 : Nat.card ↥E' * E'.index = Nat.card ↥M := card_mul_index E'
    rw [← h1, Nat.factorization_mul Nat.card_pos.ne' index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, ← hcardE]
    simp
  have hEnorm : E ≤ normalizer (P : Set G) :=
    le_normalizer_map_subtype_of_normal (Subgroup.normal_of_characteristic Q)
  have hvpos : 0 < (Nat.card ↥E).factorization q :=
    hqp.factorization_pos_of_dvd Nat.card_pos.ne' hqE
  have hPbot : P ≠ ⊥ := by
    intro hPb
    rw [hPb, card_bot] at hPcard
    exact absurd hPcard.symm (Nat.one_lt_pow hvpos.ne' hqp.one_lt).ne'
  have hPp : IsPGroup q ↥P := IsPGroup.of_card hPcard
  have hlt : normalizer (P : Set G) < ⊤ := normalizer_lt_top_of_isPGroup hna hqp hPbot hPp
  have hNle : normalizer (P : Set G) ≤ M := h.le_of_ne_top (hKE.trans hEnorm) hlt.ne
  exact hqπ ((mem_sigmaPrimes_iff_exists_subgroup hqp).2
    ⟨hqE.trans (Subgroup.card_dvd_of_le hEM), P, hPM, by rw [hPcard, hfacM], hNle⟩)

theorem not_isUniqueMaximalOvergroup_of_forall_prime_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    {K : Subgroup G} (hKM : K ≤ M)
    (hK : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p ∉ sigmaPrimes M)
    {N : Subgroup G} : ¬ IsUniqueMaximalOvergroup K N :=
  not_isUniqueMaximalOvergroup_of_isPiSubgroup_compl_sigmaPrimes hna hodd hsolv hM hKM
    (isPiSubgroup_iff.2 fun p hp =>
      hK p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)) (N := N)

theorem exists_ne_isCoatom_ge_of_forall_prime_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    {K : Subgroup G} (hKM : K ≤ M)
    (hK : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p ∉ sigmaPrimes M) :
    ∃ N₁ N₂ : Subgroup G, IsCoatom N₁ ∧ IsCoatom N₂ ∧ K ≤ N₁ ∧ K ≤ N₂ ∧ N₁ ≠ N₂ := by
  have hKtop : K ≠ ⊤ := fun hKt => hM.1 (top_le_iff.1 (hKt ▸ hKM))
  obtain ⟨N₁, hN₁, hKN₁⟩ := (IsCoatomic.eq_top_or_exists_le_coatom K).resolve_left hKtop
  by_contra hcon
  refine not_isUniqueMaximalOvergroup_of_forall_prime_notMem_sigmaPrimes hna hodd hsolv hM hKM hK
    (N := N₁) ⟨hN₁, hKN₁, fun N hN hKN => ?_⟩
  by_contra hne
  exact hcon ⟨N, N₁, hN, hN₁, hKN, hKN₁, hne⟩

end

end CFSG.FeitThompson
