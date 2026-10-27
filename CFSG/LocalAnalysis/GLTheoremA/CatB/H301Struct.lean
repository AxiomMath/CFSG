module

import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
import CFSG.LocalAnalysis.RankFourTheoremC.PPointCentral
import CFSG.RankThree.PartOne.K1214.PGroupCyclic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open scoped commutatorElement

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]

private theorem eq_one_of_mem_centralizer_component {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : RankThreeCoreUniqueness.Helpers.primeComplementCore (G := Q) p = ⊥)
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) {z : Q} (hz : z ∈ Subgroup.center Q)
    (hzp : orderOf z = p)
    (hrk : ∀ y ∈ Subgroup.centralizer (K : Set Q), y ^ p = 1 → y ∈ Subgroup.zpowers z)
    {h : Q} (hh : h ∈ Subgroup.centralizer (K : Set Q)) (hh2 : ∃ k : ℕ, h ^ (2 ^ k) = 1) :
    h = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzc : Subgroup.zpowers z ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr hz
  obtain ⟨R⟩ : Nonempty (Sylow p Q) := inferInstance
  have huniq : ∀ J : Subgroup Q, IsComponentOf J ⊤ → J = K := by
    intro J hJ
    by_contra hne
    obtain ⟨t, ⟨-, htJ⟩, htp, htC⟩ :=
      AGLEmbedding.exists_mem_sylow_inf_component hp hp2 hcore R hJ
    have htz : t ∈ Subgroup.zpowers z :=
      hrk t (AGLEmbedding.le_centralizer_of_component_ne hJ hK hne htJ)
        (htp ▸ pow_orderOf_eq_one t)
    exact htC (Subgroup.center_le_centralizer _ (hzc htz))
  have hKn : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have heq := huniq _
      ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK)
    rw [← heq]
    exact ⟨n, hn, rfl⟩
  have hcyc : IsCyclic ((R : Subgroup Q) ⊓ Subgroup.centralizer (K : Set Q) : Subgroup Q) :=
    RankThree.PartOne.K1214.isCyclic_subgroup_of_pow_eq_one_subset hp hp2
      (R.isPGroup'.to_le inf_le_left)
      ⟨AGLEmbedding.mem_sylow_of_mem_center hz hzp R, Subgroup.center_le_centralizer _ hz⟩ hzp
      fun y hy hyp => hrk y hy.2 hyp
  have hP := RankFourTheoremC.isPGroup_centralizer_of_unique_component R hcore hK hKn huniq
    hcyc hz hzp
  obtain ⟨k, hk⟩ := hh2
  obtain ⟨j, hj⟩ := hP ⟨h, hh⟩
  have h1 : orderOf h ∣ p ^ j :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
  have h2 : orderOf h ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (p ^ j) (2 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)

end Abstract

variable {G : Type} [Group G] [Finite G]

private theorem mk_mem_centralizer_barX {p : ℕ} {X L : Subgroup G} (hLsn : IsSubnormal L X)
    {a : G} (ha : a ∈ X) (haL : (⁅L, Subgroup.zpowers a⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩ ∈
      Subgroup.centralizer (GLTheoremB.barX p X L : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  have hlL : (l : G) ∈ L := hl
  obtain ⟨w, hw, hwc⟩ :=
    HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hLsn
      (haL (Subgroup.commutator_mem_commutator hlL (Subgroup.mem_zpowers a)))
  have hw' : w = ⁅l, ⟨a, ha⟩⁆ := Subtype.ext (by simpa [commutatorElement_def] using hwc)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⁅l, ⟨a, ha⟩⁆ = 1 := by
    rw [← hw']
    exact (QuotientGroup.eq_one_iff _).mpr hw
  rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1

private theorem centMod_of_mk_mem_centralizer_barX {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) {a : G} (ha : a ∈ X)
    (hc : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩ ∈
      Subgroup.centralizer (GLTheoremB.barX p X L : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    CentMod p L a := by
  have hN : a ∈ Subgroup.normalizer (L : Set G) :=
    GLTheoremB.mem_normalizer_of_barX_normalizes hp le_rfl hL ha (Subgroup.le_normalizer ha)
      (Subgroup.centralizer_le_normalizer _ hc)
  refine ⟨hN, Subgroup.commutator_le.mpr fun l hl b hb => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hlX : l ∈ X := hL.1 hl
  have hcL : ⁅l, a ^ k⁆ ∈ L := by
    have h1 : a ^ k * l⁻¹ * (a ^ k)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hN k) _).mp (L.inv_mem hl)
    rw [commutatorElement_def]
    simpa only [mul_assoc] using L.mul_mem hl h1
  have hcO : ⁅l, a ^ k⁆ ∈ GLAPPrimeCoreOf p X := by
    refine ⟨⁅(⟨l, hlX⟩ : ↥X), ⟨a, ha⟩ ^ k⁆, (QuotientGroup.eq_one_iff _).mp ?_, ?_⟩
    · have hcomm : Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩)
          (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩) :=
        Subgroup.mem_centralizer_iff.mp hc _ ⟨⟨l, hlX⟩, hl, rfl⟩
      show QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⁅(⟨l, hlX⟩ : ↥X), ⟨a, ha⟩ ^ k⁆ = 1
      rw [map_commutatorElement, map_zpow, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.zpow_right k
    · simp [commutatorElement_def]
  have := HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp X L ⟨hcO, hcL⟩
  rwa [inf_eq_right.mpr hL.1] at this

theorem mem_pPrimeCoreOf_of_centMod_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
    {L : Subgroup G} (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hZ : Odd (Nat.card (Subgroup.center (PQuot p L))))
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    {g : G} (hg : g ∈ cx x) (hg2 : ∃ k : ℕ, g ^ (2 ^ k) = 1) (hgL : CentMod p L g) :
    g ∈ GLAPPrimeCoreOf p (cx x) := by
  have : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := cx x
  set O : Subgroup ↥X := GLAPPrimeCore p ↥X
  have hOcop : p.Coprime (Nat.card O) := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X)
  set Lb : Subgroup (↥X ⧸ O) := GLTheoremB.barX p X L
  have hcore : RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥X ⧸ O) p = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  set z : ↥X ⧸ O := QuotientGroup.mk' O ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hz : z ∈ Subgroup.center (↥X ⧸ O) := AGLEmbedding.mk_mem_center_centralizer O rfl
  have hzp : orderOf z = p :=
    AGLEmbedding.orderOf_mk_of_coprime hp O hOcop (by rw [← Subgroup.orderOf_coe]; exact hx)
  have hrk : ∀ y ∈ Subgroup.centralizer (Lb : Set (↥X ⧸ O)), y ^ p = 1 →
      y ∈ Subgroup.zpowers z := by
    intro y hy hyp
    by_contra hyz
    set E : Subgroup (↥X ⧸ O) := Subgroup.zpowers z ⊔ Subgroup.zpowers y
    have hE2 : 2 ≤ CFSG.Open.pRank p E :=
      AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers hp hzp hyp hyz
        (Subgroup.mem_center_iff.mp hz y).symm
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hEC : E ≤ Subgroup.centralizer (Lb : Set (↥X ⧸ O)) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz))
        (Subgroup.zpowers_le.mpr hy)
    have hY2 : 2 ≤ CFSG.Open.pRank p (E.comap (QuotientGroup.mk' O)) := by
      rw [← PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p hp O
        ((Nat.Prime.coprime_iff_not_dvd hp).mp hOcop),
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
      exact hE2
    obtain ⟨A, hAY, hA, hAcard⟩ :=
      AGLEmbedding.exists_isElemAbelian_card_sq_of_two_le_pRank hp hY2
    have hle := hrk1 (A.map X.subtype) (hA.map _) (Subgroup.map_subtype_le _) (by
      rintro _ ⟨a, ha, rfl⟩
      exact centMod_of_mk_mem_centralizer_barX hp hL a.2 (hEC (hAY ha)))
    rw [Subgroup.card_map_of_injective X.subtype_injective, hAcard] at hle
    exact absurd hle (not_le.mpr (lt_self_pow₀ hp.one_lt one_lt_two))
  obtain ⟨k, hk⟩ := hg2
  have hgk : (QuotientGroup.mk' O ⟨g, hg⟩) ^ (2 ^ k) = 1 := by
    rw [← map_pow, show (⟨g, hg⟩ : ↥X) ^ (2 ^ k) = 1 from Subtype.ext (by simpa using hk),
      map_one]
  have h1 := eq_one_of_mem_centralizer_component hp hp2 hcore hL.2.2.1 hz hzp hrk
    (mk_mem_centralizer_barX hL.2.1 hg hgL.2) ⟨k, hgk⟩
  exact ⟨⟨g, hg⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
