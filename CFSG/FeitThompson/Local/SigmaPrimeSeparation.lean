module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SharedSigmaSylowSetup
import CFSG.FeitThompson.Local.CommonCoreTauOneWitness
import CFSG.FeitThompson.Local.NonconjugateIntersectionPrimeCentralization
import CFSG.FeitThompson.Local.TauOneIntersectionAsymmetry
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem conjSub_eq_prep08 (g : G) (Y : Subgroup G) :
    Prep09.conjSub g Y = Prep08.conjSubgroup Y g := (conj_smul_eq_map_conj g⁻¹ Y).symm

theorem conjSub_eq_prep01 (g : G) (Y : Subgroup G) :
    Prep09.conjSub g Y = CFSG.FeitThompson.conjSubgroup Y g := (rfl)

theorem le_centralizer_symm' {A B : Subgroup G} (h : A ≤ centralizer (B : Set G)) :
    B ≤ centralizer (A : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
  rwa [Subgroup.commutator_comm]

theorem dvd_natCard_of_le_of_natCard_eq_pow [Finite G] {q n : ℕ} (hq : q.Prime)
    {X Y : Subgroup G} (hXY : X ≤ Y) (hY : Nat.card ↥Y = q ^ n) (hX : X ≠ ⊥) :
    q ∣ Nat.card ↥X := by
  have hd : Nat.card ↥X ∣ q ^ n := hY ▸ Subgroup.card_dvd_of_le hXY
  have h1 : Nat.card ↥X ≠ 1 := fun h => hX (Subgroup.card_eq_one.1 h)
  have hm : (Nat.card ↥X).minFac.Prime := Nat.minFac_prime h1
  have hmq : (Nat.card ↥X).minFac = q :=
    (Nat.prime_dvd_prime_iff_eq hm hq).1 (hm.dvd_of_dvd_pow ((Nat.minFac_dvd _).trans hd))
  exact hmq ▸ Nat.minFac_dvd _

theorem false_of_mem_sigmaPrimes_inter [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    (hG : Prep09.IsMinimalSimpleOddOrder G) {M T : Subgroup G} (hM : IsCoatom M)
    (hT : IsCoatom T) (hnc : ∀ g : G, T ≠ Prep09.conjSub g M) {q : ℕ}
    (hqM : q ∈ sigmaPrimes M) (hqT : q ∈ sigmaPrimes T) : False := by
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqM
  have _ifact : Fact q.Prime := ⟨hq⟩
  have _iF : Fintype G := Fintype.ofFinite G
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG07 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG01 : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨E, Q, g, hEM, hEbot, hsd, hQbot, hQsylS, hQsylM, hQsylG, hQsylL, -, hEQ,
      hNQ, hEML, -, hLnc⟩ :=
    FTS_shared_sigma_sylow_setup h₁ G hG08 M T q hM hT
      (fun x => by rw [← conjSub_eq_prep08]; exact hnc x) hqM hqT
  have hLcoatom : IsCoatom (Prep08.conjSubgroup T g) := isCoatom_conj_smul hT g⁻¹
  set L : Subgroup G := Prep08.conjSubgroup T g with hLdef
  have hLM : L ≠ M := fun h => hLnc 1 (by rw [h, Prep08.conjSubgroup_one])
  have hnc' : ∀ x : G, L ≠ CFSG.FeitThompson.conjSubgroup M x := by
    intro x
    rw [← conjSub_eq_prep01, conjSub_eq_prep08]
    exact hLnc x
  have hQM : Q ≤ M := hQsylM.le
  have hQL : Q ≤ L := hQsylL.le
  have hQS : Q ≤ sigmaCore M := hQsylS.le
  have hEL : E ≤ L := hEML.trans inf_le_right
  have hSML : sigmaCore M ⊓ L ≠ ⊥ := by
    intro h
    refine hQbot (le_bot_iff.1 ?_)
    rw [← h]; exact le_inf hQS hQL
  obtain ⟨E₁, E₂, E₃, hHall₁, -, -, p, hpτ, P, hPE₁, hPcard, -, -, -, hPML, hPnorm⟩ :=
    FTS_common_core_tau_one_witness h₁ h₆ h₇ h₈ G hG07 M hM L hLcoatom (Ne.symm hLM) E hEM hEbot
      hsd hEL hSML
  have hp : p.Prime := prime_of_mem_tau1Primes hpτ
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  have hE₁E : E₁ ≤ E := hHall₁.1
  have hPQ : P ≤ normalizer (Q : Set G) := hPnorm Q hEQ
  have hPL : P ≤ L := hPML.trans inf_le_right
  have hQfix : Q ⊓ centralizer (P : Set G) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := hQsylS.isPGroup.exists_card_eq
    have hdvd : q ∣ Nat.card ↥(Q ⊓ centralizer (P : Set G) : Subgroup G) :=
      dvd_natCard_of_le_of_natCard_eq_pow hq inf_le_left hn hne
    obtain ⟨X, hXle, hXcard⟩ := exists_le_natCard_eq_of_prime_dvd hq hdvd
    have hXc : X ≤ Prep09.centIn (sigmaCore M) (P : Set G) := by
      change X ≤ sigmaCore M ⊓ centralizer (P : Set G)
      exact le_inf ((hXle.trans inf_le_left).trans hQS) (hXle.trans inf_le_right)
    obtain ⟨-, hsyl⟩ := h₉ G hG M hM E hEM hsd E₁ hE₁E hHall₁.2 P hPE₁ hPbot q hq X hXc hXcard
    obtain ⟨S, hS⟩ := hQsylS
    have huniq := hsyl S
    rw [hS] at huniq
    exact hLM (huniq.eq_of_isCoatom hLcoatom hQL)
  have hcomm : ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ ≠ ⊥ := by
    intro hb
    have h1 : (sigmaCore M ⊓ L : Subgroup G) ≤ centralizer ((M ⊓ L : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb
    have h2 : Q ≤ centralizer (P : Set G) :=
      (le_inf hQS hQL).trans (h1.trans (centralizer_le (SetLike.coe_subset_coe.2 hPML)))
    refine hQbot (le_bot_iff.1 ?_)
    rw [← hQfix]; exact le_inf le_rfl h2
  have hpτL : p ∈ tau1Primes L := by
    by_contra hpn
    have hsetup : IsNonconjugateSetup M L E p :=
      { isCoatom_M := hM
        isCoatom_L := hLcoatom
        nonconj := hnc'
        le_M_E := hEM
        semidirect := hsd
        prime := hp
        dvd_natCard_E := hPcard ▸ Subgroup.card_dvd_of_le (hPE₁.trans hE₁E)
        dvd_natCard_L := hPcard ▸ Subgroup.card_dvd_of_le hPL }
    have hcc := FBG_nonconjugate_intersection_prime_centralization h₁ h₂ h₃ G hG01 M L E p
      hsetup hpn hcomm P hPML (IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one]))
    have h1 : P ≤ centralizer ((sigmaCore M ⊓ L : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcc
    have h2 : Q ≤ centralizer (P : Set G) := (le_inf hQS hQL).trans (le_centralizer_symm' h1)
    refine hQbot (le_bot_iff.1 ?_)
    rw [← hQfix]; exact le_inf le_rfl h2
  have hQcardG : Nat.card ↥Q = q ^ (Nat.card G).factorization q := by
    have h := (Prep08.isSylowOf_iff_natCard hq (le_top : Q ≤ ⊤)).1 hQsylG
    rwa [Subgroup.card_top] at h
  have hQsylML : Nat.card ↥Q = q ^ (Nat.card ↥(M ⊓ L : Subgroup G)).factorization q :=
    natCard_eq_pow_factorization_of_le hq (le_inf hQM hQL) hQcardG
  exact FBG_tau_one_intersection_asymmetry h₁ h₄ h₅ h₈ G hG02 M L hM hLcoatom hnc' p hp hpτ hpτL
    P hPML hPcard q q hq hq Q Q ⟨le_inf hQM hQL, hQsylML⟩ ⟨le_inf hQM hQL, hQsylML⟩
    (le_inf hPQ hPQ) hQfix hQfix (hNQ.trans inf_le_right) (hNQ.trans inf_le_left)

theorem FTS_sigma_prime_separation
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u} := by
  intro G _ _ hG M T hM hT hnc
  rw [Set.eq_empty_iff_forall_notMem]
  intro q hq
  exact false_of_mem_sigmaPrimes_inter h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ hG hM hT hnc hq.1 hq.2

end

end CFSG.FeitThompson.Proofs
