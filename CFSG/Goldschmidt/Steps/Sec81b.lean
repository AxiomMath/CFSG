module

import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.AxB
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.Walter.Bender1970.S3.FStar
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem qCoreOf_le_of_ne {H M V : Subgroup G} {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hqp : q ≠ p) (hVp : IsPGroup p V) (hVc : ¬ IsCyclic V)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H) (hVM : V ≤ M) :
    GorensteinWalter.qCoreOf M q ≤ H := by
  obtain ⟨E, hEV, hEp, hEc⟩ := exists_plane hp hp2 hVp hVc
  have hcomp : ¬ p ∣ Nat.card (GorensteinWalter.qCoreOf M q) := by
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, hk⟩ := (GorensteinWalter.qCoreOf_isPGroup M q).exists_card_eq
    rw [hk]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm
  have hEN : E ≤ Subgroup.normalizer (GorensteinWalter.qCoreOf M q : Set G) :=
    (hEV.trans hVM).trans
      (GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.qCoreOf_normal_in M q))
  rw [RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp E _ hEp
    hEc hcomp hEN]
  refine iSup₂_le fun e he => inf_le_right.trans (hVC e (hEV e.2) fun h => he ?_)
  exact Subtype.ext h

theorem qCoreOf_le_centralizer {M V : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G}
    (ha2 : a ^ 2 = 1) (hVp : IsPGroup p V) (hV1 : V ≠ ⊥)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({a} : Set G))
    (haM : a ∈ M) (hVM : V ≤ M) (hVa : V ≤ Subgroup.centralizer ({a} : Set G)) :
    GorensteinWalter.qCoreOf M p ≤ Subgroup.centralizer ({a} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hMN := GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.qCoreOf_normal_in M p)
  have hza : Subgroup.zpowers a ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hVa hv))
  have hcard : Nat.Coprime (Nat.card (Subgroup.zpowers a)) p := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ha2)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  have hfix : GorensteinWalter.qCoreOf M p ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro x hx
    have hxa : x ∈ Subgroup.centralizer ({a} : Set G) := hVC v v.2 (fun h => hv1 (Subtype.ext h))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr v.2) hx.2)
    have hc : Commute x a := Subgroup.mem_centralizer_singleton_iff.mp hxa
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hc.zpow_right k).symm.eq
  have h := N10 G (GorensteinWalter.qCoreOf M p) (Subgroup.zpowers a) V
    (GorensteinWalter.qCoreOf_isPGroup M p) hcard hVp
    (Subgroup.zpowers_le.mpr (hMN haM)) (hVM.trans hMN)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hza) hfix
  exact h.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a)))

omit [Finite G] in
theorem mem_centralizer_zpowers {x a : G} (h : x ∈ Subgroup.centralizer ({a} : Set G)) :
    x ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  have hc : Commute x a := Subgroup.mem_centralizer_singleton_iff.mp h
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (hc.zpow_right k).symm.eq

omit [Finite G] in
theorem ne_bot_of_not_isCyclic {V : Subgroup G} (hVc : ¬ IsCyclic V) : V ≠ ⊥ := by
  rintro rfl
  exact hVc isCyclic_of_subsingleton

theorem fittingSubgroupOf_le_centralizer {M V : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a : G} (ha2 : a ^ 2 = 1) (hVp : IsPGroup p V) (hVc : ¬ IsCyclic V)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({a} : Set G))
    (haM : a ∈ M) (hVM : V ≤ M) (hVa : V ≤ Subgroup.centralizer ({a} : Set G)) :
    CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer ({a} : Set G) := by
  rw [(show CFSG.fittingSubgroupOf M = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf M)]
  refine iSup_le fun q => ?_
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hqp : q.1.1 = p
  · rw [hqp]
    exact qCoreOf_le_centralizer hp hp2 ha2 hVp (ne_bot_of_not_isCyclic hVc) hVC haM hVM hVa
  · exact qCoreOf_le_of_ne hp hp2 hq hqp hVp hVc hVC hVM

theorem oddCoreOf_le_centralizer_of_fitting {M : Subgroup G} {a : G} (ha2 : a ^ 2 = 1)
    (haM : a ∈ M) (hF : CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer ({a} : Set G)) :
    oddCoreOf M ≤ Subgroup.centralizer ({a} : Set G) := by
  set X := oddCoreOf M with hX
  set R := Subgroup.zpowers a with hR
  have hXM : X ≤ M := oddCoreOf_le M
  have hRX : R ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_oddCoreOf M haM)
  have hcop : Nat.Coprime (Nat.card R) (Nat.card X) := by
    rw [hR, Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ha2)
      (Nat.coprime_two_left.mpr (odd_card_oddCoreOf M))
  have hXn : (X.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr (le_normalizer_oddCoreOf M)
  have hFX : CFSG.fittingSubgroupOf X ≤ CFSG.fittingSubgroupOf M :=
    Walter.fittingSubgroupOf_le_of_isSubnormal hXM hXn.isSubnormal
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreOf M)
  have hFXn : GorensteinWalter.IsNormalIn (CFSG.fittingSubgroupOf X) X :=
    GorensteinWalter.fittingSubgroupOf_isNormalIn X
  have hXR : ⁅X, R⁆ ≤ CFSG.fittingSubgroupOf X := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have hrf : ∀ f ∈ CFSG.fittingSubgroupOf X, r * f = f * r := fun f hf =>
      ((Subgroup.mem_centralizer_iff.mp (mem_centralizer_zpowers (hF (hFX hf)))) r hr)
    have h1 : ⁅x, r⁆ ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hRX hr) x⁻¹).mp (X.inv_mem hx)
      simpa [commutatorElement_def, mul_assoc] using X.mul_mem hx this
    have h2 : ⁅x, r⁆ ∈ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
      have hf' : x⁻¹ * f * x ∈ CFSG.fittingSubgroupOf X := by
        simpa using hFXn.2 x⁻¹ (X.inv_mem hx) f hf
      have e1 := hrf f hf
      have e2 := hrf _ hf'
      rw [commutatorElement_def]
      calc f * (x * r * x⁻¹ * r⁻¹) = x * (x⁻¹ * f * x) * r * x⁻¹ * r⁻¹ := by group
        _ = x * r * (x⁻¹ * f * x) * x⁻¹ * r⁻¹ := by rw [mul_assoc x, ← e2, ← mul_assoc]
        _ = x * r * x⁻¹ * f * r⁻¹ := by group
        _ = x * r * x⁻¹ * r⁻¹ * (r * f) * r⁻¹ := by group
        _ = x * r * x⁻¹ * r⁻¹ * f := by rw [e1]; group
    have h3 : (⟨⁅x, r⁆, h1⟩ : X) ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.mp h2 y ⟨y, hy, rfl⟩
    exact ⟨_, CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv h3, rfl⟩
  have hdouble : ⁅⁅X, R⁆, R⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun y hy =>
      mem_centralizer_zpowers (hF (hFX (hXR hy)))
  have h := GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot X R hRX hcop
    hdouble
  intro x hx
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a))
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx)

theorem oddCoreOf_le_centralizer {M V : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : G} (ha2 : a ^ 2 = 1) (hVp : IsPGroup p V) (hVc : ¬ IsCyclic V)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({a} : Set G))
    (haM : a ∈ M) (hVM : V ≤ M) (hVa : V ≤ Subgroup.centralizer ({a} : Set G)) :
    oddCoreOf M ≤ Subgroup.centralizer ({a} : Set G) :=
  oddCoreOf_le_centralizer_of_fitting ha2 haM
    (fittingSubgroupOf_le_centralizer hp hp2 ha2 hVp hVc hVC haM hVM hVa)

theorem mem_centralizer_of_mem_two (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a b y : G}
    (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hya : y ∈ Subgroup.centralizer ({a} : Set G)) (hyb : y ∈ Subgroup.centralizer ({b} : Set G)) :
    y ∈ Subgroup.centralizer (A : Set G) := by
  have ea : y * a * y⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hya, mul_inv_cancel_right]
  have eb : y * b * y⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hyb, mul_inv_cancel_right]
  refine mem_centralizer_of_forall fun x hx => ?_
  rcases mem_four hset.elem h4 ha hb hx ha1 hb1 hab with rfl | rfl | rfl | rfl
  · group
  · exact ea
  · exact eb
  · calc y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      _ = a * b := by rw [ea, eb]

theorem not_le_centralizer (h64 : S_G64) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a)
    {V : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hVp : IsPGroup p V)
    (hVc : ¬ IsCyclic V) (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H) :
    ¬ V ≤ Subgroup.centralizer (A : Set G) := by
  intro hVA
  obtain ⟨-, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  obtain ⟨n, hn, hnc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hba, -⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  have hb : n * a * n⁻¹ ∈ A := conj_mem hn ha
  have hb1 : n * a * n⁻¹ ≠ 1 := conj_ne_one ha1
  have hHb : Subgroup.centralizer ({n * a * n⁻¹} : Set G) ∈ Walter.benderM (n * a * n⁻¹) := by
    have := Walter.map_conj_mem_benderM n hH
    rwa [hHa, Walter.map_conj_centralizer_singleton] at this
  have hVC' : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := fun v hv hv1 => hHa ▸ hVC v hv hv1
  have haCb : a ∈ Subgroup.centralizer ({n * a * n⁻¹} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm hset.elem ha hb)
  have hVCb : V ≤ Subgroup.centralizer ({n * a * n⁻¹} : Set G) :=
    hVA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hVa : V ≤ Subgroup.centralizer ({a} : Set G) :=
    hVA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hOa := oddCoreOf_le_centralizer hp hp2 (hset.elem.2 a ha) hVp hVc hVC' haCb hVCb hVa
  apply commutator_ne_bot hset h4 hb hb1 hHb
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp
    fun y hy => ?_)
  exact mem_centralizer_of_mem_two hset h4 ha hb ha1 hb1 (Ne.symm hba) (hOa hy)
    (oddCoreOf_le _ hy)

end CFSG.Goldschmidt.Sec8
