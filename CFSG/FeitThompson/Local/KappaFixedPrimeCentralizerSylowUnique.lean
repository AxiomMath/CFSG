module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {π : Set ℕ} {p q : ℕ} {M K N Q : Subgroup G}

theorem isHallPiSubgroup_subgroupOf_of_isHallPiOf (h : CFSG.FeitThompson.Prep03.IsHallPiOf π K M) :
    IsHallPiSubgroup π (K.subgroupOf M) := by
  refine isHallPiSubgroup_iff.2 ⟨fun r hr => h.2.1 r ?_, fun r hr => h.2.2 r hr⟩
  rwa [← Subgroup.card_subtype M (K.subgroupOf M), Subgroup.map_subgroupOf_eq_of_le h.1] at hr

theorem factorization_eq_of_isHallPiSubgroup_subgroupOf [Finite G] (hq : q.Prime)
    (hNM : N ≤ M) (h : IsHallPiSubgroup π (N.subgroupOf M)) (hqπ : q ∈ π) :
    (Nat.card ↥M).factorization q = (Nat.card ↥N).factorization q := by
  have hcard : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcardN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hi : (N.subgroupOf M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h0 : Nat.card ↥(N.subgroupOf M) ≠ 0 := Nat.card_pos.ne'
  have hqi : ¬ q ∣ (N.subgroupOf M).index := fun hdvd =>
    (isHallPiSubgroup_iff.1 h).2 q (Nat.mem_primeFactors.2 ⟨hq, hdvd, hi⟩) hqπ
  calc (Nat.card ↥M).factorization q
      = (Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index).factorization q := by rw [hcard]
    _ = (Nat.card ↥(N.subgroupOf M)).factorization q
          + ((N.subgroupOf M).index).factorization q := by
        rw [Nat.factorization_mul h0 hi]; rfl
    _ = (Nat.card ↥N).factorization q := by
        rw [hcardN, Nat.factorization_eq_zero_of_not_dvd hqi, add_zero]

theorem le_sigmaCore_of_isPiSubgroup_of_isHallPiSubgroup [Finite G]
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hQM : Q ≤ M) (hQ : IsPiSubgroup (sigmaPrimes M) Q) : Q ≤ sigmaCore M := by
  have h1 : IsPiSubgroup (sigmaPrimes M) (Q.subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 hQ r ?_
    rwa [← Subgroup.card_subtype M (Q.subgroupOf M), Subgroup.map_subgroupOf_eq_of_le hQM] at hr
  have h2 := hHall.le_of_isPiSubgroup h1
  have h3 := Subgroup.map_mono (f := M.subtype) h2
  rwa [Subgroup.map_subgroupOf_eq_of_le hQM,
    Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] at h3

theorem isPiSubgroup_of_natCard_eq_pow (hq : q.Prime) {k : ℕ} (hQ : Nat.card ↥Q = q ^ k)
    (hqπ : q ∈ π) : IsPiSubgroup π Q := by
  refine isPiSubgroup_iff.2 fun r hr => ?_
  rw [hQ] at hr
  obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
  rwa [(Nat.prime_dvd_prime_iff_eq hrp hq).1 (hrp.dvd_of_dvd_pow hrd)]

theorem factorization_eq_of_isInternalSemidirectProduct [Finite G] {A B : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct M A B) (hA : ¬ p ∣ Nat.card ↥A) :
    (Nat.card ↥M).factorization p = (Nat.card ↥B).factorization p := by
  rw [h.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hA]
  simp

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

theorem FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness.{u} := by
  intro G _ _ M K A Z hsetup
  obtain ⟨hamb, hM, hκ, hKH, hA, -⟩ := hsetup
  have hsimple := hamb.isSimpleGroup
  have hmin : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.forall_isSolvable⟩
  have hmin2 : IsOddOrderMinimalSimple G :=
    ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.forall_isSolvable⟩
  obtain ⟨hHallOf, hHallG, -⟩ := h₁ G hmin2 M hM
  obtain ⟨-, U, E₁, -, -, hsd, -, hE₁bot, hE₁Hall, hE₁K, -, hcentX, hcentK, -⟩ :=
    h₂ G hamb M K hM hκ hKH
  have hsd' : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K) :=
    ⟨hsd.2.2.2.1, hsd.2.2.1, disjoint_iff.2 hsd.2.2.2.2⟩
  have hE₁E : E₁ ≤ U ⊔ K := hE₁K.trans le_sup_right
  have hE₁M : E₁ ≤ M := hE₁E.trans hsd.2.1
  have hE₁HallS : IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf (U ⊔ K)) :=
    isHallPiSubgroup_subgroupOf_of_isHallPiOf hE₁Hall
  have hAE₁ : A = Prep09.centIn (sigmaCore M) (E₁ : Set G) := by
    rw [hA, ← hcentX E₁ hE₁K hE₁bot]; rfl
  have hAS : A ≤ sigmaCore M := by rw [hA]; exact inf_le_left
  have key : ∀ q : ℕ, q.Prime → ∀ X : Subgroup G, X ≤ A → Nat.card ↥X = q →
      IsUniqueMaximalOvergroup (centralizer (X : Set G)) M ∧
        ∀ S : Sylow q ↥(sigmaCore M),
          IsUniqueMaximalOvergroup
            (((S : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype : Subgroup G)) M :=
    fun q hq X hXA hXc =>
      h₃ G hmin M hM (U ⊔ K) hsd.2.1 hsd' E₁ hE₁E hE₁HallS E₁ le_rfl hE₁bot q hq X
        (hAE₁ ▸ hXA) hXc
  obtain ⟨p, hp⟩ : (Nat.card ↥E₁).primeFactors.Nonempty := by
    refine Nat.nonempty_primeFactors.2 (lt_of_le_of_ne Nat.card_pos (Ne.symm ?_))
    exact fun h => hE₁bot (Subgroup.card_eq_one.1 h)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpτ : p ∈ tau1Primes M := hE₁Hall.2.1 p hp
  have hpσ : p ∉ sigmaPrimes M := (mem_tau1Primes_iff.1 hpτ).2.2.1
  have hpM : p ∣ Nat.card ↥M := (mem_tau1Primes_iff.1 hpτ).2.1
  have hfacE : 0 < (Nat.card ↥E₁).factorization p :=
    hpp.factorization_pos_of_dvd Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hp)
  have hfacM : (Nat.card ↥M).factorization p = (Nat.card ↥E₁).factorization p := by
    have h1 : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
      hpσ (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
        (Nat.mem_primeFactors.2 ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
    rw [factorization_eq_of_isInternalSemidirectProduct hsd' h1,
      factorization_eq_of_isHallPiSubgroup_subgroupOf hpp hE₁E hE₁HallS hpτ]
  have hfp : Fact p.Prime := ⟨hpp⟩
  obtain ⟨SP⟩ : Nonempty (Sylow p ↥E₁) := inferInstance
  set P : Subgroup G := (SP : Subgroup ↥E₁).map E₁.subtype with hPdef
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := by
    rw [hPdef, Subgroup.card_subtype, SP.card_eq_multiplicity, hfacM]
  have hPE₁ : P ≤ E₁ := Subgroup.map_subtype_le _
  have hPbot : P ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥P = 1 := by rw [h]; simp
    rw [hPcard, hfacM] at h1
    exact absurd h1 (Nat.ne_of_gt (Nat.one_lt_pow (by omega) hpp.one_lt))
  have hNPtop : Subgroup.normalizer (P : Set G) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hamb.not_isMulCommutative hpp hPbot
      (IsPGroup.of_card hPcard)).ne
  refine ⟨hA ▸ hcentK, fun q X hq hXA hXc => ?_, fun q Q hq hqA hQ => ?_⟩
  · obtain ⟨hu, -⟩ := key q hq X hXA hXc
    exact ⟨hu.le, fun T hT hTle => hu.eq_of_isCoatom hT hTle⟩
  · have hfq : Fact q.Prime := ⟨hq⟩
    have hqσ : q ∈ sigmaPrimes M :=
      isPiSubgroup_iff.1 hHallG.isPiSubgroup q (Nat.mem_primeFactors.2
        ⟨hq, hqA.trans (Subgroup.card_dvd_of_le hAS), Nat.card_pos.ne'⟩)
    have hQS : Q ≤ sigmaCore M :=
      le_sigmaCore_of_isPiSubgroup_of_isHallPiSubgroup hHallOf.2 hQ.1
        (isPiSubgroup_of_natCard_eq_pow hq hQ.2 hqσ)
    have hcardQ : Nat.card ↥(Q.subgroupOf (sigmaCore M))
        = q ^ (Nat.card ↥(sigmaCore M)).factorization q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv, hQ.2,
        factorization_eq_of_isHallPiSubgroup_subgroupOf hq (sigmaCore_le M) hHallOf.2 hqσ]
    set S : Sylow q ↥(sigmaCore M) := Sylow.ofCard (Q.subgroupOf (sigmaCore M)) hcardQ with hS
    have hmapS : ((S : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype : Subgroup G) = Q := by
      rw [hS, Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hQS]
    obtain ⟨x, hxA, hxo⟩ := exists_mem_orderOf_eq_of_dvd hq hqA
    have huniq := (key q hq (zpowers x) (zpowers_le.2 hxA) (by rw [Nat.card_zpowers, hxo])).2 S
    rw [hmapS] at huniq
    refine ⟨fun T hT hQT => huniq.eq_of_isCoatom hT hQT, fun hQA => ?_⟩
    have hQN : Q ≤ Subgroup.normalizer (P : Set G) :=
      le_trans (le_trans (le_trans (le_trans hQA (le_of_eq hAE₁)) inf_le_right)
        (centralizer_le (SetLike.coe_subset_coe.2 hPE₁))) (centralizer_le_normalizer _)
    obtain ⟨T, hT, hNT⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom
        (Subgroup.normalizer (P : Set G))).resolve_left hNPtop
    have hNM : Subgroup.normalizer (P : Set G) ≤ M :=
      huniq.eq_of_isCoatom hT (hQN.trans hNT) ▸ hNT
    exact hpσ ((mem_sigmaPrimes_iff_exists_subgroup hpp).2
      ⟨hpM, P, hPE₁.trans hE₁M, hPcard, hNM⟩)

end

end CFSG.FeitThompson.Proofs
