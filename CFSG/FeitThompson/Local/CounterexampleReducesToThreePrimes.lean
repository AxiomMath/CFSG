module

public import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.PrimeSubgroupFixesFittingLine
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.Local.ProperSubconfigurationSylowActionTrivial
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.SylowNormalizerNotCentralizing
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.OddOrder.SemidirectReassociation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem le_normalizer_commutator_of_le_normalizer₂ {A B C : Subgroup G}
    (hA : C ≤ normalizer (A : Set G)) (hB : C ≤ normalizer (B : Set G)) :
    C ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := fun g hg => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hB hg)]

variable [Finite G]

theorem commutator_commutator_eq_of_le_normalizer [Group.IsSolvable G] {K P : Subgroup G}
    (hPK : P ≤ normalizer (K : Set G)) (hcop : (Nat.card ↥P).Coprime (Nat.card ↥K)) :
    (⁅⁅K, P⁆, P⁆ : Subgroup G) = ⁅K, P⁆ := by
  set L : Subgroup G := K ⊔ P with hL
  have hKL : K ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hDK : (⁅K, P⁆ : Subgroup G) ≤ K :=
    (Subgroup.commutator_mono le_rfl hPK).trans (commutator_normalizer_le K)
  have hDL : (⁅K, P⁆ : Subgroup G) ≤ L := hDK.trans hKL
  have hDDL : (⁅⁅K, P⁆, P⁆ : Subgroup G) ≤ L :=
    ((Subgroup.commutator_mono le_rfl (Subgroup.normalizer_commutator_ge_right K P)).trans
      (commutator_normalizer_le _)).trans hDL
  have _iKn : (K.subgroupOf L).Normal := normal_subgroupOf_sup hPK
  have hcop' : (Nat.card ↥(P.subgroupOf L)).Coprime (Nat.card ↥(K.subgroupOf L)) := by
    rw [natCard_subgroupOf_of_le hPL, natCard_subgroupOf_of_le hKL]; exact hcop
  have h := commutator_commutator_eq_commutator (K.subgroupOf L) (P.subgroupOf L) hcop'
  rw [commutator_subgroupOf hKL hPL, commutator_subgroupOf hDL hPL] at h
  have h2 := congrArg (Subgroup.map L.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hDDL, Subgroup.map_subgroupOf_eq_of_le hDL] at h2

theorem exists_prime_isPGroup_of_forall_characteristic {K P : Subgroup G}
    [Group.IsNilpotent ↥K] (hKne : K ≠ ⊥)
    (hcent : ∀ S : Subgroup ↥K, S.Characteristic → S.map K.subtype ≠ K →
      S.map K.subtype ≤ centralizer (P : Set G))
    (hKP : (⁅K, P⁆ : Subgroup G) ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card ↥K ∧ IsPGroup q ↥K := by
  have hcard : Nat.card ↥K ≠ 1 := fun h => hKne (Subgroup.card_eq_one.1 h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcard
  refine ⟨q, hq, hqd, ?_⟩
  set S : Subgroup ↥K := sylowPiPart ({q}ᶜ : Set ℕ) ↥K with hS
  set T : Subgroup ↥K := sylowPiPart ({q} : Set ℕ) ↥K with hT
  have hmapsup : S.map K.subtype ⊔ T.map K.subtype = K := by
    rw [← Subgroup.map_sup, hS, hT, sup_comm, sylowPiPart_sup_compl, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  by_cases hTtop : T.map K.subtype = K
  · have hTtop' : T = ⊤ :=
      Subgroup.map_injective K.subtype_injective
        (hTtop.trans (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]))
    have h1 : IsPiSubgroup ({q} : Set ℕ) (⊤ : Subgroup ↥K) :=
      hTtop' ▸ hT ▸ isPiSubgroup_sylowPiPart _ _
    exact ((isPiSubgroup_singleton_iff hq _).1 h1).of_equiv Subgroup.topEquiv
  exfalso
  have hSne : S.map K.subtype ≠ K := by
    intro hStop
    have hStop' : S = ⊤ :=
      Subgroup.map_injective K.subtype_injective
        (hStop.trans (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]))
    have h1 : IsPiSubgroup ({q}ᶜ : Set ℕ) (⊤ : Subgroup ↥K) :=
      hStop' ▸ hS ▸ isPiSubgroup_sylowPiPart _ _
    have h2 := isPiSubgroup_iff.1 h1 q (by
      rw [Subgroup.card_top]
      exact Nat.mem_primeFactors.2 ⟨hq, hqd, Nat.card_pos.ne'⟩)
    simp at h2
  refine hKP (Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_)
  rw [← hmapsup]
  exact sup_le (hcent S (sylowPiPart_characteristic _ _) hSne)
    (hcent T (sylowPiPart_characteristic _ _) hTtop)

variable {p : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsPrimeCentralizerKernelSetup p H R R0 V K U N P)

namespace IsPrimeCentralizerKernelSetup

include hc

theorem inf_K_P : K ⊓ P = ⊥ := by
  rw [inf_comm]
  exact inf_eq_bot_of_isPGroup_of_coprime hc.prime_p hc.isPGroup_P hc.coprime_card_K.symm

theorem P_le_normalizer_K : P ≤ normalizer (K : Set G) :=
  hc.P_le_N.trans hc.le_normalizer_K_of_mem_N

theorem R0_le_normalizer_K : R0 ≤ normalizer (K : Set G) :=
  hc.admissible.le.trans hc.R_le_normalizer_K

theorem K_ne_bot : K ≠ ⊥ := fun h =>
  hc.commutator_K_P_ne_bot (by rw [h, Subgroup.commutator_bot_left])

theorem isNilpotent_K : Group.IsNilpotent ↥K :=
  hc.K_eq_fittingRaw_N ▸ isNilpotent_map_fittingRaw N

theorem coprime_natCard_P_K : (Nat.card ↥P).Coprime (Nat.card ↥K) := by
  rw [hc.card_P]; exact Nat.Coprime.pow_left _ hc.coprime_card_K.symm

theorem natCard_sup_V_X_P_R0 {X : Subgroup G} (hX : X ≤ K) (hXP : P ≤ normalizer (X : Set G))
    (hXR0 : R0 ≤ normalizer (X : Set G)) :
    Nat.card ↥(V ⊔ X ⊔ P ⊔ R0)
      = Nat.card ↥V * Nat.card ↥X * Nat.card ↥P * Nat.card ↥R0 := by
  have hVn := hc.normal_V
  have hXP' : Nat.card ↥(X ⊔ P) = Nat.card ↥X * Nat.card ↥P :=
    natCard_sup_eq_mul_of_le_normalizer hXP
      (le_bot_iff.1 ((inf_le_inf hX le_rfl).trans hc.inf_K_P.le))
  have hXPN : X ⊔ P ≤ N := sup_le (hX.trans hc.K_le_N) hc.P_le_N
  have hV1 : Nat.card ↥(V ⊔ (X ⊔ P)) = Nat.card ↥V * Nat.card ↥(X ⊔ P) :=
    natCard_sup_eq_mul_of_le_normalizer (fun _ hg => Subgroup.le_normalizer_of_normal hg)
      (le_bot_iff.1 ((inf_le_inf le_rfl hXPN).trans hc.inf_V_N.le))
  have hR0 : Nat.card ↥(V ⊔ X ⊔ P ⊔ R0) = Nat.card ↥(V ⊔ X ⊔ P) * Nat.card ↥R0 :=
    natCard_sup_eq_mul_of_le_normalizer (hc.R0_le_normalizer_sup hXR0)
      (le_bot_iff.1 ((inf_le_inf (hc.sup_V_X_P_le_H hX) hc.admissible.le).trans
        hc.admissible.inf_eq_bot.le))
  rw [hR0, sup_assoc, hV1, hXP']
  ring

theorem sup_V_K_P_R0_eq_top : V ⊔ K ⊔ P ⊔ R0 = ⊤ := by
  by_contra hne
  exact hc.commutator_K_P_ne_bot
    (hc.commutator_X_P_eq_bot le_rfl hc.P_le_normalizer_K hc.R0_le_normalizer_K hne)

theorem natCard_V_K_P_R0 :
    Nat.card ↥V * Nat.card ↥K * Nat.card ↥P * Nat.card ↥R0 = Nat.card G := by
  rw [← hc.natCard_sup_V_X_P_R0 le_rfl hc.P_le_normalizer_K hc.R0_le_normalizer_K,
    hc.sup_V_K_P_R0_eq_top, Subgroup.card_top]

private theorem natCard_key :
    Nat.card ↥R = Nat.card ↥R0 ∧ Nat.card ↥K * Nat.card ↥P = Nat.card ↥N := by
  have hVn := hc.normal_V
  have hH : Nat.card ↥V * Nat.card ↥N = Nat.card ↥H := by
    rw [← hc.sup_V_N]
    exact (natCard_sup_eq_mul_of_le_normalizer
      (fun _ hg => Subgroup.le_normalizer_of_normal hg) hc.inf_V_N).symm
  have hG : Nat.card ↥H * Nat.card ↥R = Nat.card G := hc.admissible.card_mul_card
  have hKP : Nat.card ↥(K ⊔ P) = Nat.card ↥K * Nat.card ↥P :=
    natCard_sup_eq_mul_of_le_normalizer hc.P_le_normalizer_K hc.inf_K_P
  have hle : Nat.card ↥K * Nat.card ↥P ≤ Nat.card ↥N :=
    hKP ▸ Subgroup.card_le_of_le (sup_le hc.K_le_N hc.P_le_N)
  have hler : Nat.card ↥R0 ≤ Nat.card ↥R := Subgroup.card_le_of_le hc.admissible.le
  have heq : Nat.card ↥V * (Nat.card ↥N * Nat.card ↥R)
      = Nat.card ↥V * (Nat.card ↥K * Nat.card ↥P * Nat.card ↥R0) := by
    rw [← mul_assoc, hH, hG, ← hc.natCard_V_K_P_R0]; ring
  have h2 : Nat.card ↥N * Nat.card ↥R = Nat.card ↥K * Nat.card ↥P * Nat.card ↥R0 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos heq
  have hb1 : Nat.card ↥K * Nat.card ↥P * Nat.card ↥R0 ≤ Nat.card ↥N * Nat.card ↥R0 :=
    Nat.mul_le_mul_right _ hle
  have hb2 : Nat.card ↥N * Nat.card ↥R0 ≤ Nat.card ↥N * Nat.card ↥R :=
    Nat.mul_le_mul_left _ hler
  have hreq : Nat.card ↥R = Nat.card ↥R0 :=
    Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥N) Nat.card_pos (by omega)
  refine ⟨hreq, ?_⟩
  rw [hreq] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2.symm

theorem R_eq_R0 : R = R0 :=
  (Subgroup.eq_of_le_of_card_ge hc.admissible.le (le_of_eq hc.natCard_key.1)).symm

theorem sup_K_P_eq_N : K ⊔ P = N :=
  Subgroup.eq_of_le_of_card_ge (sup_le hc.K_le_N hc.P_le_N)
    (le_of_eq (by
      rw [natCard_sup_eq_mul_of_le_normalizer hc.P_le_normalizer_K hc.inf_K_P]
      exact hc.natCard_key.2.symm))

theorem sup_V_K_P : V ⊔ K ⊔ P = H := by
  rw [sup_assoc, hc.sup_K_P_eq_N, hc.sup_V_N]

theorem commutator_P_R_eq : (⁅P, R⁆ : Subgroup G) = P := by
  rw [hc.R_eq_R0]; exact hc.commutator_P_R0_eq

theorem P_ne_bot : P ≠ ⊥ := fun h =>
  hc.commutator_K_P_ne_bot (by rw [h, Subgroup.commutator_bot_right])

theorem centralizes_of_lt (S : Subgroup G) (hSK : S ≤ K) (hSne : S ≠ K)
    (hSP : P ≤ normalizer (S : Set G)) (hSR : R ≤ normalizer (S : Set G)) :
    P ≤ centralizer (S : Set G) := by
  have hSR0 : R0 ≤ normalizer (S : Set G) := hc.R_eq_R0 ▸ hSR
  have hproper : V ⊔ S ⊔ P ⊔ R0 ≠ ⊤ := by
    intro htop
    have h1 := hc.natCard_sup_V_X_P_R0 hSK hSP hSR0
    rw [htop, Subgroup.card_top, ← hc.natCard_V_K_P_R0] at h1
    have h2 := Nat.eq_of_mul_eq_mul_right (m := Nat.card ↥R0) Nat.card_pos h1
    have h3 := Nat.eq_of_mul_eq_mul_right (m := Nat.card ↥P) Nat.card_pos h2
    have h4 : Nat.card ↥K = Nat.card ↥S := Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
    exact hSne (Subgroup.eq_of_le_of_card_ge hSK h4.le)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hc.commutator_X_P_eq_bot hSK hSP hSR0 hproper

theorem K_eq_commutator : K = ⁅K, P⁆ := by
  have _isolv : Group.IsSolvable G := hc.admissible.isSolvable
  set D : Subgroup G := ⁅K, P⁆ with hD
  have hDK : D ≤ K :=
    (Subgroup.commutator_mono le_rfl hc.P_le_normalizer_K).trans (commutator_normalizer_le K)
  by_contra hne
  have hDP : P ≤ normalizer (D : Set G) :=
    le_normalizer_commutator_of_le_normalizer₂ hc.P_le_normalizer_K le_normalizer
  have hDR : R ≤ normalizer (D : Set G) :=
    le_normalizer_commutator_of_le_normalizer₂ hc.R_le_normalizer_K hc.R_le_normalizer_P
  have hcent := hc.centralizes_of_lt D hDK (Ne.symm hne) hDP hDR
  have hbot : (⁅D, P⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  rw [hD, commutator_commutator_eq_of_le_normalizer hc.P_le_normalizer_K
    hc.coprime_natCard_P_K] at hbot
  exact hc.commutator_K_P_ne_bot hbot

theorem exists_prime_isPGroup_K :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧ q ≠ Nat.card ↥R0 ∧ IsPGroup q ↥K := by
  have := hc.isNilpotent_K
  obtain ⟨q, hq, hqd, hqK⟩ := exists_prime_isPGroup_of_forall_characteristic hc.K_ne_bot
    (fun S _hSchar hSne => by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hc.centralizes_of_lt _ (Subgroup.map_subtype_le S) hSne
        (le_normalizer_map_subtype_of_characteristic S hc.P_le_normalizer_K)
        (le_normalizer_map_subtype_of_characteristic S hc.R_le_normalizer_K))
    hc.commutator_K_P_ne_bot
  refine ⟨q, hq, (hc.admissible.odd_card_subgroup K).of_dvd_nat hqd, ?_, ?_, hqK⟩
  · exact fun hqp => hc.prime_p.one_lt.ne'
      (hc.coprime_card_K.symm.eq_one_of_dvd (hqp ▸ hqd))
  · exact fun hqr => hq.one_lt.ne'
      (Nat.eq_one_of_dvd_coprimes hc.coprime_natCard_K_R0 hqd hqr.dvd)

theorem primeCentralizerThreePrimeGeneration :
    V ⊔ K ⊔ P = H ∧ R = R0 ∧ (⁅P, R⁆ : Subgroup G) = P ∧ P ≠ ⊥ ∧ K = ⁅K, P⁆ ∧
      (∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧ q ≠ Nat.card ↥R0 ∧ IsPGroup q ↥K) ∧
      (∀ S : Subgroup G, S ≤ K → S ≠ K → P ≤ normalizer (S : Set G) →
        R ≤ normalizer (S : Set G) → P ≤ centralizer (S : Set G)) :=
  ⟨hc.sup_V_K_P, hc.R_eq_R0, hc.commutator_P_R_eq, hc.P_ne_bot, hc.K_eq_commutator,
    hc.exists_prime_isPGroup_K, hc.centralizes_of_lt⟩

theorem isReducedPrimeCentralizerKernel :
    ∃ q : ℕ, IsReducedPrimeCentralizerKernel p q H R R0 V K U N P := by
  obtain ⟨q, hq, hqodd, hqp, hqr, hqK⟩ := hc.exists_prime_isPGroup_K
  exact ⟨q,
    { admissible := hc.admissible
      prime_p := hc.prime_p
      not_hasPLengthLeOne := hc.not_hasPLengthLeOne
      minimal := hc.minimal
      V_eq := hc.V_eq
      K_le_H := hc.K_le_H
      R_le_normalizer_K := hc.R_le_normalizer_K
      U_eq := hc.U_eq
      N_eq := hc.N_eq
      P_le_N := hc.P_le_N
      card_P := hc.card_P
      R_le_normalizer_P := hc.R_le_normalizer_P
      U_subgroupOf_eq := hc.U_subgroupOf_eq
      inf_K_V := hc.inf_K_V
      coprime_card_K := hc.coprime_card_K
      sup_V_N := hc.sup_V_N
      commutator_K_P_ne_bot := hc.commutator_K_P_ne_bot
      inf_V_centralizer_K := hc.inf_V_centralizer_K
      inf_V_N := hc.inf_V_N
      K_eq_fittingRaw_N := hc.K_eq_fittingRaw_N
      inf_H_centralizer_K_le := hc.inf_H_centralizer_K_le
      sup_V_K_P := hc.sup_V_K_P
      R_eq := hc.R_eq_R0
      P_eq_commutator := hc.commutator_P_R_eq.symm
      P_ne_bot := hc.P_ne_bot
      K_eq_commutator := hc.K_eq_commutator
      prime_q := hq
      odd_q := hqodd
      q_ne_p := hqp
      q_ne_r := hqr
      isPGroup_K := hqK
      centralizes_of_lt := hc.centralizes_of_lt }⟩

end IsPrimeCentralizerKernelSetup

end CFSG.FeitThompson

end
