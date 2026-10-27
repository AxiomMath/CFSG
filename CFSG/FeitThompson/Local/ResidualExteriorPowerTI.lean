module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep08 (IsMinimalSimpleOddOrder IsHallOf conjSet)

universe u

variable {G : Type*} [Group G]

theorem isInternalSemidirectProduct_sup_left {M N U K : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct M N (U ⊔ K)) :
    FreeCore.IsInternalSemidirectProduct (N ⊔ U) N U where
  sup_eq := rfl
  le_normalizer := sup_le le_normalizer ((le_sup_left.trans h.right_le).trans h.le_normalizer)
  disjoint := disjoint_iff.2 (le_bot_iff.1
    (h.inf_eq_bot ▸ inf_le_inf_left N (le_sup_left : U ≤ U ⊔ K)))

theorem orderOf_pow_dvd_of_orderOf_dvd_mul {y : G} {a b k : ℕ} (hord : orderOf y ∣ a * b)
    (hka : a ∣ k) : orderOf (y ^ k) ∣ b := by
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← pow_mul]
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  obtain ⟨c, rfl⟩ := hka
  exact hord.trans ⟨c, by ring⟩

theorem orderOf_mul_inv_pow_dvd_of_orderOf_dvd_mul {y : G} {a b k : ℕ}
    (hord : orderOf y ∣ a * b) (hkb : (b : ℤ) ∣ (k : ℤ) - 1) :
    orderOf (y * (y ^ k)⁻¹) ∣ a := by
  have hy : y * (y ^ k)⁻¹ = y ^ (1 - (k : ℤ)) := by
    rw [sub_eq_add_neg, zpow_add, zpow_one, zpow_neg, zpow_natCast]
  have hpow : (y ^ (1 - (k : ℤ))) ^ (a : ℕ) = y ^ ((1 - (k : ℤ)) * (a : ℤ)) := by
    rw [← zpow_natCast (y ^ (1 - (k : ℤ))) a, ← zpow_mul]
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [hy, hpow]
  refine orderOf_dvd_iff_zpow_eq_one.1 (dvd_trans (Int.natCast_dvd_natCast.2 hord) ?_)
  obtain ⟨c, hc⟩ := hkb
  refine ⟨-c, ?_⟩
  have h1 : (1 : ℤ) - (k : ℤ) = -((b : ℤ) * c) := by linarith
  push_cast
  rw [h1]
  ring

theorem inf_centralizer_conj_ne_bot {N : Subgroup G} {m y : G}
    (hm : m ∈ normalizer (N : Set G)) (h : N ⊓ centralizer ({y} : Set G) ≠ ⊥) :
    N ⊓ centralizer ({m⁻¹ * y * m} : Set G) ≠ ⊥ := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  obtain ⟨hxN, hxy⟩ := Subgroup.mem_inf.1 x.2
  have hx1 : (x : G) ≠ 1 := by simpa using hx
  have hxy' : (x : G) * y = y * (x : G) := mem_centralizer_singleton_iff.1 hxy
  have hxN' : m⁻¹ * (x : G) * m ∈ N := (mem_set_normalizer_iff''.1 hm (x : G)).1 hxN
  have hcomm : (m⁻¹ * (x : G) * m) * (m⁻¹ * y * m) = (m⁻¹ * y * m) * (m⁻¹ * (x : G) * m) := by
    calc (m⁻¹ * (x : G) * m) * (m⁻¹ * y * m) = m⁻¹ * ((x : G) * y) * m := by group
      _ = m⁻¹ * (y * (x : G)) * m := by rw [hxy']
      _ = (m⁻¹ * y * m) * (m⁻¹ * (x : G) * m) := by group
  intro hbot
  have hmem : m⁻¹ * (x : G) * m ∈ N ⊓ centralizer ({m⁻¹ * y * m} : Set G) :=
    Subgroup.mem_inf.2 ⟨hxN', mem_centralizer_singleton_iff.2 hcomm⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  refine hx1 ?_
  have h2 := congrArg (fun z : G => m * z * m⁻¹) hmem
  simp only [mul_one] at h2
  rw [show m * (m⁻¹ * (x : G) * m) * m⁻¹ = (x : G) by group] at h2
  simpa using h2

theorem exists_dvd_and_dvd_sub_one {a b : ℕ} (h : a.Coprime b) :
    ∃ k : ℕ, a ∣ k ∧ (b : ℤ) ∣ (k : ℤ) - 1 := by
  obtain ⟨k, hk0, hk1⟩ := Nat.chineseRemainder h 0 1
  exact ⟨k, (Nat.modEq_zero_iff_dvd).1 hk0, dvd_sub_comm.1 hk1.dvd⟩

variable [Finite G] {M K U : Subgroup G}

theorem relIndex_sigmaCore_eq
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K) :
    (sigmaCore M).relIndex M = Nat.card ↥U * Nat.card ↥K := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(sigmaCore M))) ?_
  rw [CFSG.FeitThompson.natCard_mul_relIndex_of_le (sigmaCore_le M),
    hsemi.natCard_eq_mul, hsemiE.natCard_eq_mul]

theorem relIndex_eq_of_isInternalSemidirectProduct
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K) (hKM : K ≤ M) :
    K.relIndex M = Nat.card ↥(sigmaCore M) * Nat.card ↥U := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥K)) ?_
  rw [CFSG.FeitThompson.natCard_mul_relIndex_of_le hKM, hsemi.natCard_eq_mul,
    hsemiE.natCard_eq_mul]
  ring

theorem notMem_sigmaPrimes_of_mem_primeFactors_natCard [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K)
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) : p ∉ sigmaPrimes M := by
  have hHall := (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM).isHallPiSubgroup
  refine hHall.notMem_of_mem_primeFactors_index p ?_
  have hidx : ((sigmaCore M).subgroupOf M).index = Nat.card ↥U * Nat.card ↥K :=
    relIndex_sigmaCore_eq hsemi hsemiE
  rw [hidx]
  exact Nat.primeFactors_mono (Dvd.intro _ rfl)
    (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') hp

theorem notMem_kappaPrimes_of_mem_primeFactors_natCard
    (hKHall : IsHallOf (kappaPrimes M) K M)
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K)
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) : p ∉ kappaPrimes M := by
  refine hKHall.isHallPiSubgroup.notMem_of_mem_primeFactors_index p ?_
  have hidx : (K.subgroupOf M).index = Nat.card ↥(sigmaCore M) * Nat.card ↥U :=
    relIndex_eq_of_isInternalSemidirectProduct hsemi hsemiE hKHall.le
  rw [hidx]
  exact Nat.primeFactors_mono ⟨Nat.card ↥(sigmaCore M), by ring⟩
    (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') hp

theorem coprime_natCard_sigmaCore_natCard [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K) :
    (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥U) := by
  by_contra hc
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  refine notMem_sigmaPrimes_of_mem_primeFactors_natCard hna hodd hsolv hM hsemi hsemiE
    (Nat.mem_primeFactors.2 ⟨hp, hpb, Nat.card_pos.ne'⟩) ?_
  exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
    (Nat.mem_primeFactors.2 ⟨hp, hpa, Nat.card_pos.ne'⟩)

theorem isUniqueMaximalOvergroup_centralizer_pow
    (h₃ : Statements.FTS_core_centralizing_external_element_dichotomy.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsMinimalSimpleOddOrder G)
    {M K U : Subgroup G} (hM : IsCoatom M) (hKHall : IsHallOf (kappaPrimes M) K M)
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K)
    {k : ℕ} (hka : Nat.card ↥(sigmaCore M) ∣ k) (hkb : (Nat.card ↥U : ℤ) ∣ (k : ℤ) - 1)
    {y : G} (hyB : y ∈ sigmaCore M ⊔ U) (hyS : y ∉ sigmaCore M)
    (hyc : sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥) :
    y ^ k ≠ 1 ∧ orderOf (y ^ k) ∣ Nat.card ↥U ∧
      IsUniqueMaximalOvergroup (centralizer ({y ^ k} : Set G)) M := by
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  have hBM : sigmaCore M ⊔ U ≤ M :=
    sup_le (sigmaCore_le M) ((le_sup_left : U ≤ U ⊔ K).trans hsemi.right_le)
  have hord : orderOf y ∣ Nat.card ↥(sigmaCore M) * Nat.card ↥U := by
    have h := (sigmaCore M ⊔ U).orderOf_dvd_natCard hyB
    rwa [(isInternalSemidirectProduct_sup_left hsemi).natCard_eq_mul] at h
  have hub : orderOf (y ^ k) ∣ Nat.card ↥U := orderOf_pow_dvd_of_orderOf_dvd_mul hord hka
  have hva : orderOf (y * (y ^ k)⁻¹) ∣ Nat.card ↥(sigmaCore M) :=
    orderOf_mul_inv_pow_dvd_of_orderOf_dvd_mul hord hkb
  have hyM : y ∈ M := hBM hyB
  have hukM : y ^ k ∈ M := pow_mem hyM k
  have hvS : y * (y ^ k)⁻¹ ∈ sigmaCore M := by
    refine mem_sigmaCore_of_primeFactors_orderOf hna hodd hsolv hM
      (mul_mem hyM (inv_mem hukM)) fun p hp => ?_
    exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.primeFactors_mono hva Nat.card_pos.ne' hp)
  have hu1 : y ^ k ≠ 1 := by
    intro h
    rw [h] at hvS
    exact hyS (by simpa using hvS)
  refine ⟨hu1, hub, ?_⟩
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hyc
  obtain ⟨hxS, hxy⟩ := Subgroup.mem_inf.1 x.2
  have hx1 : (x : G) ≠ 1 := by simpa using hx
  have hc : Commute (x : G) y := mem_centralizer_singleton_iff.1 hxy
  have hux : y ^ k ∈ centralizer ({(x : G)} : Set G) :=
    mem_centralizer_singleton_iff.2 (hc.pow_right k).symm.eq
  have hprimes : ∀ r ∈ (orderOf (y ^ k)).primeFactors, r ∉ sigmaPrimes M := fun r hr =>
    notMem_sigmaPrimes_of_mem_primeFactors_natCard hna hodd hsolv hM hsemi hsemiE
      (Nat.primeFactors_mono hub Nat.card_pos.ne' hr)
  have hdich := h₃ G ⟨hG.isSimpleGroup, hna, hodd, hsolv⟩ M hM (x : G) hxS hx1 (y ^ k)
    (Subgroup.mem_inf.2 ⟨hukM, hux⟩) hu1 hprimes
  rcases hdich with ⟨hkappa, -⟩ | ⟨-, huniq⟩
  · exfalso
    have hone : orderOf (y ^ k) ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.1 h)
    have hzero : orderOf (y ^ k) ≠ 0 := (orderOf_pos (y ^ k)).ne'
    obtain ⟨r, hr⟩ : (orderOf (y ^ k)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.2 (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.2 hzero) (Ne.symm hone))
    exact notMem_kappaPrimes_of_mem_primeFactors_natCard hKHall hsemi hsemiE
      (Nat.primeFactors_mono hub Nat.card_pos.ne' hr) (hkappa r hr)
  · exact huniq

theorem normalizer_eq_and_ti_of_nonempty
    (h₃ : Statements.FTS_core_centralizing_external_element_dichotomy.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsMinimalSimpleOddOrder G)
    {M K U : Subgroup G} (hM : IsCoatom M) (hKHall : IsHallOf (kappaPrimes M) K M)
    (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsemiE : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K)
    {D : Set G}
    (hD : D = {y | y ∈ sigmaCore M ⊔ U ∧ y ∉ sigmaCore M ∧
      sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥})
    (hne : D.Nonempty) :
    normalizer D = M ∧
      (∀ g : G, g ∉ M → D ∩ Prep08.conjSet D g = ∅) ∧
      (∀ y ∈ D, ∀ z ∈ D, ∀ g : G, g⁻¹ * y * g = z → g ∈ M) ∧
      ∀ y ∈ D, centralizer ({y} : Set G) ≤ M := by
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  obtain ⟨k, hka, hkb⟩ := exists_dvd_and_dvd_sub_one
    (coprime_natCard_sigmaCore_natCard hna hodd hsolv hM hsemi hsemiE)
  have hSn : M ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) := le_normalizer_sigmaCore M
  have hBn : M ≤ normalizer ((sigmaCore M ⊔ U : Subgroup G) : Set G) :=
    CFSG.FeitThompson.le_normalizer_sup_of_isSemidirect
      ⟨hsemi.left_le, hsemi.right_le, hsemi.le_normalizer, hsemi.sup_eq, hsemi.inf_eq_bot⟩
      ⟨hsemiE.left_le, hsemiE.right_le, hsemiE.le_normalizer, hsemiE.sup_eq, hsemiE.inf_eq_bot⟩
  have hstab : ∀ m ∈ M, (fun d => m⁻¹ * d * m) '' D ⊆ D := by
    rintro m hm z ⟨d, hd, rfl⟩
    rw [hD] at hd ⊢
    obtain ⟨hdB, hdS, hdc⟩ := hd
    refine ⟨(mem_set_normalizer_iff''.1 (hBn hm) d).1 hdB, ?_,
      inf_centralizer_conj_ne_bot (hSn hm) hdc⟩
    exact fun h => hdS ((mem_set_normalizer_iff''.1 (hSn hm) d).2 h)
  have hmain : ∀ d ∈ D, IsUniqueMaximalOvergroup (centralizer ({d ^ k} : Set G)) M := by
    intro d hd
    rw [hD] at hd
    exact (isUniqueMaximalOvergroup_centralizer_pow h₃ G hG hM hKHall hsemi hsemiE hka hkb
      hd.1 hd.2.1 hd.2.2).2.2
  have hle : ∀ d ∈ D, centralizer ({d ^ k} : Set G) ≤ M := fun d hd => (hmain d hd).le
  have huniq : ∀ d ∈ D, ∀ L : Subgroup G, IsCoatom L →
      centralizer ({d ^ k} : Set G) ≤ L → L = M := fun d hd L hL hsub =>
    (hmain d hd).eq_of_isCoatom hL hsub
  obtain ⟨hnorm, hdisj⟩ :=
    normalizer_eq_and_disjoint_conj_of_isCoatom_centralizer_pow hM
      (normalizer_coe_eq_of_isCoatom hna hM) hne hstab hle huniq
  have hconjSet : ∀ g : G, Prep08.conjSet D g = (fun d => g⁻¹ * d * g) '' D := fun _ => rfl
  have hti : ∀ g : G, g ∉ M → D ∩ Prep08.conjSet D g = ∅ := fun g hg => by
    rw [hconjSet g]; exact hdisj g hg
  have hconj : ∀ y ∈ D, ∀ z ∈ D, ∀ g : G, g⁻¹ * y * g = z → g ∈ M := by
    intro y hy z hz g hgz
    by_contra hgM
    have hzmem : z ∈ D ∩ Prep08.conjSet D g := ⟨hz, by rw [hconjSet g]; exact ⟨y, hy, hgz⟩⟩
    rw [hti g hgM] at hzmem
    exact hzmem
  refine ⟨hnorm, hti, hconj, fun y hy c hcy => ?_⟩
  refine hconj y hy y hy c ?_
  have h := (mem_centralizer_singleton_iff.1 hcy).symm
  calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
    _ = c⁻¹ * (c * y) := by rw [h]
    _ = y := by group

theorem FTS_residual_exterior_power_ti
    (_h₁ : Statements.FNI_kappa_local_pair.{u})
    (_h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FTS_core_centralizing_external_element_dichotomy.{u}) :
    Statements.FTS_residual_exterior_power_ti.{u} := by
  intro G _ _ hG M K U B hM hKHall _hUM hsemi hsemiE hB D hD
  subst hB
  refine ⟨fun k hka hkb y hy => ?_, fun hne => ?_⟩
  · rw [hD] at hy
    exact isUniqueMaximalOvergroup_centralizer_pow h₃ G hG hM hKHall hsemi hsemiE hka hkb
      hy.1 hy.2.1 hy.2.2
  · exact normalizer_eq_and_ti_of_nonempty h₃ G hG hM hKHall hsemi hsemiE hD hne

end

end CFSG.FeitThompson.Proofs
