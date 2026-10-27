module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Representations.CanonicalPiSetComponent

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep05

universe u

variable {G : Type*} [Group G]

theorem signalizer_eq_sigmaSignalizer [Finite G] (x : G) :
    signalizer x = sigmaSignalizer x := (rfl)

theorem exists_pow_eq_of_commute_of_coprime_orderOf {x r : G} (h : Commute x r)
    (hcop : (orderOf x).Coprime (orderOf r)) (hx : orderOf x ≠ 0) (hr : orderOf r ≠ 0) :
    ∃ k : ℕ, (x * r) ^ k = x := by
  have hxpi : CoprimeComponent.IsPiNumber (↑(orderOf x).primeFactors : Set ℕ) (orderOf x) :=
    CoprimeComponent.isPiNumber_iff_forall_prime.2
      ⟨Nat.pos_of_ne_zero hx, fun p hp hpd => Nat.mem_primeFactors.2 ⟨hp, hpd, hx⟩⟩
  have hrpi : CoprimeComponent.IsPiPrimeNumber
      (↑(orderOf x).primeFactors : Set ℕ) (orderOf r) := by
    refine CoprimeComponent.isPiPrimeNumber_iff_forall_prime.2
      ⟨Nat.pos_of_ne_zero hr, fun p hp hpd hmem => ?_⟩
    exact Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, Nat.dvd_of_mem_primeFactors hmem, hpd⟩ hcop
  have hcomp := CoprimeComponent.piComponent_eq_of_commute h hxpi hrpi
  obtain ⟨k, hk⟩ := CoprimeComponent.piComponent_mem_powers
    (↑(orderOf x).primeFactors : Set ℕ) (x * r)
  exact ⟨k, by simpa using hk.trans hcomp⟩

theorem exists_isHallPiOf_of_isSolvable [Finite G] (π : Set ℕ) {N : Subgroup G}
    (hsolv : Group.IsSolvable ↥N) : ∃ J : Subgroup G, Prep03.IsHallPiOf π J N := by
  have := hsolv
  obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := ↥N) π
  have hrel : (H.map N.subtype).relIndex N = H.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  refine ⟨H.map N.subtype, Subgroup.map_subtype_le _, fun p hp => ?_, fun p hp => ?_⟩
  · rw [Subgroup.card_subtype] at hp
    exact isPiNumber_iff.1 hH.natCard p hp
  · rw [hrel] at hp
    exact isPiNumber_iff.1 hH.index p hp

theorem FPF_core_packet_derived_support_centralizer
    (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (_h₄ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₅ : Statements.FTS_core_centralizing_external_element_dichotomy.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FPF_core_packet_derived_support_centralizer.{u} := by
  intro G _ _ hG M N hM hN hconj hkM hkN x hx hx1 r hr ha
  have _hfin : Fintype G := Fintype.ofFinite G
  have hamb7 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hamb9 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb3 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨haN, ha1, hafix⟩ := mem_fixedSet.1 ha
  have hr' : r ∈ sigmaSignalizer x := by rwa [← signalizer_eq_sigmaSignalizer]
  have hrC : r ∈ centralizer ({x} : Set G) := sigmaSignalizer_le_centralizer x hr'
  have hcomm : Commute x r := (mem_centralizer_singleton_iff.1 hrC).symm
  have hcopRM : Nat.Coprime (Nat.card ↥(sigmaSignalizer x)) (Nat.card ↥M) :=
    (h₃ G hamb7 M hM).2 hkM x hx hx1
  have hordr : orderOf r ∣ Nat.card ↥(sigmaSignalizer x) :=
    (sigmaSignalizer x).orderOf_dvd_natCard hr'
  have hordx : orderOf x ∣ Nat.card ↥M := M.orderOf_dvd_natCard (sigmaCore_le M hx)
  have hcop : (orderOf x).Coprime (orderOf r) :=
    (Nat.Coprime.coprime_dvd_left hordr (Nat.Coprime.coprime_dvd_right hordx hcopRM)).symm
  obtain ⟨k, hk⟩ := exists_pow_eq_of_commute_of_coprime_orderOf hcomm hcop
    (orderOf_pos x).ne' (orderOf_pos r).ne'
  have hxmem : x ∈ zpowers (x * r) := mem_zpowers_iff.2 ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩
  have hxcomm : x ∈ (⁅N, N⁆ : Subgroup G) := hk ▸ pow_mem haN k
  have hxN : x ∈ N := commutator_le_self N hxcomm
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hafix
  have hz1' : z ≠ 1 := by simpa using hz1
  have hzx : z ∈ centralizerIn (sigmaCore N) (zpowers x) :=
    ⟨hz.1, Subgroup.centralizer_le
      (SetLike.coe_subset_coe.2 (Subgroup.zpowers_le.2 hxmem)) hz.2⟩
  have hzxcomm : x * z = z * x := mem_centralizer_iff.1 hz.2 x hxmem
  have hprimes : ∀ p ∈ (orderOf x).primeFactors, p ∉ sigmaPrimes N := by
    intro p hp hpN
    have hsep := h₆ G hamb9 M N hM hN fun g hg => hconj ⟨g⁻¹, hg⟩
    have hmem : p ∈ sigmaPrimes M ∩ sigmaPrimes N :=
      ⟨primeFactors_orderOf_subset_sigmaPrimes hx p hp, hpN⟩
    rw [hsep] at hmem
    exact hmem
  have hxcentz : x ∈ N ⊓ centralizer ({z} : Set G) :=
    ⟨hxN, mem_centralizer_singleton_iff.2 hzxcomm⟩
  rcases h₅ G hamb7 N hN z hz.1 hz1' x hxcentz hx1 hprimes with ⟨hkappa, -⟩ | ⟨-, huniq⟩
  ·
    exfalso
    obtain ⟨J, hJ⟩ := exists_isHallPiOf_of_isSolvable (kappaPrimes N)
      (hG.isSolvable_of_ne_top N hN.1)
    have hsetup : Prep03.IsKappaSetup G N J (Prep03.cent (sigmaCore N) (J : Set G))
        (J ⊔ Prep03.cent (sigmaCore N) (J : Set G)) :=
      { ambient := hamb3
        isCoatom := hN
        kappa_nonempty := hkN
        isHall_K := hJ
        A_eq := rfl
        Z_eq := rfl }
    obtain ⟨hmain, -, -⟩ := FNI_kappa_derived_complement h₁ h₂ G N J _ _ hsetup
    have hcard : Nat.card (⁅N, N⁆ : Subgroup G) = J.relIndex N :=
      natCard_commutator_eq_relIndex hJ.1 hmain
    obtain ⟨p, hp⟩ : (orderOf x).primeFactors.Nonempty := by
      rw [Nat.nonempty_primeFactors]
      have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
      have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
      omega
    have hpdvd : p ∣ J.relIndex N := hcard ▸
      (Nat.dvd_of_mem_primeFactors hp).trans ((⁅N, N⁆ : Subgroup G).orderOf_dvd_natCard hxcomm)
    refine hJ.2.2 p (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp, hpdvd, ?_⟩)
      (hkappa p hp)
    rw [← hcard]
    exact (Nat.card_pos (α := ↥(⁅N, N⁆ : Subgroup G))).ne'
  ·
    refine ⟨⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩, hxcomm, ?_, huniq, ?_⟩
    · intro hbot
      rw [hbot, mem_bot] at hzx
      exact hz1' hzx
    · intro hle
      exact hconj ((huniq.eq_of_isCoatom hM hle) ▸ isConjugateSubgroup_refl M)

end

end CFSG.FeitThompson.Proofs
