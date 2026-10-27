module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.SECore
import CFSG.GroupTheory.CentralizeSolvableOfPCores
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.PGroup.FrattiniQuotientRankBound
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.RankThree.PartTwo.Sec21.StronglyEmbedded
import CFSG.GroupTheory.PerfectGeneration
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S8Core

private theorem layerLift_map_data (k : S8Core G) {H : Subgroup G} (hH : k.Config H) :
    ∃ φ : ↥(CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H) →*
        ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)),
      Function.Surjective φ ∧
        (∀ x : ↥(CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H),
          φ x = 1 →
            Subgroup.inclusion
              (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H) x ∈
                CFSG.pPrimeCore k.q ↥H) := by
  classical
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  let J : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H
  have hJH : J ≤ H := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.map_layerLift_eq k.q H hLbarperf
  let ι : ↥J →* ↥H := Subgroup.inclusion hJH
  let φ₀ : ↥J →* (↥H ⧸ K₀) := π.comp ι
  have hφ₀mem : ∀ x : ↥J, φ₀ x ∈ Lbar := by
    intro x
    have hx : ι x ∈ J.subgroupOf H := Subgroup.mem_subgroupOf.mpr x.2
    have hmem : π (ι x) ∈ (J.subgroupOf H).map π := Subgroup.mem_map_of_mem π hx
    rwa [hmap] at hmem
  let φ : ↥J →* ↥Lbar := φ₀.codRestrict Lbar hφ₀mem
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : ↥H ⧸ K₀) ∈ (J.subgroupOf H).map π := by
      rw [hmap]
      exact y.2
    obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hy
    have hhJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
    refine ⟨⟨(h : G), hhJ⟩, ?_⟩
    apply Subtype.ext
    have hι : ι ⟨(h : G), hhJ⟩ = h := Subtype.ext rfl
    show π (ι ⟨(h : G), hhJ⟩) = (y : ↥H ⧸ K₀)
    rw [hι]
    exact hπh
  have hker_mem : ∀ x : ↥J, φ x = 1 → ι x ∈ K₀ := by
    intro x hx
    have hx' : φ₀ x = 1 := by
      have := congrArg Subtype.val hx
      simpa [φ] using this
    have hx'' : π (ι x) = 1 := by simpa [φ₀] using hx'
    exact (QuotientGroup.eq_one_iff _).mp hx''
  exact ⟨φ, hφsurj, hker_mem⟩

private theorem layerLift_ker_data (k : S8Core G) {H : Subgroup G} (hH : k.Config H) :
    ∃ φ : ↥(CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H) →*
        ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)),
      Function.Surjective φ ∧
        (∀ x : ↥(CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H),
          φ x = 1 →
            Subgroup.inclusion
              (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H) x ∈
                CFSG.pPrimeCore k.q ↥H) ∧
        Odd (Nat.card φ.ker) ∧ Nat.Coprime (Nat.card φ.ker) (2 * k.q) ∧
          IsSolvable φ.ker := by
  obtain ⟨φ, hφsurj, hker_mem⟩ := layerLift_map_data k hH
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let J : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H
  let ι : ↥J →* ↥H :=
    Subgroup.inclusion (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H)
  let ψ0 : φ.ker →* ↥H := ι.comp φ.ker.subtype
  have hψ0mem : ∀ x : φ.ker, ψ0 x ∈ K₀ :=
    fun x => hker_mem x.1 (MonoidHom.mem_ker.mp x.2)
  let ψ : φ.ker →* ↥K₀ := ψ0.codRestrict K₀ hψ0mem
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h0 : ψ0 x = ψ0 y := congrArg Subtype.val hxy
    have h1 : ι (φ.ker.subtype x) = ι (φ.ker.subtype y) := by simpa [ψ0] using h0
    exact Subtype.ext
      (Subgroup.inclusion_injective
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H) h1)
  have hK₀odd : Odd (Nat.card ↥K₀) := k.odd_card_pPrimeCore hH
  have hK₀solv : Group.IsSolvable ↥K₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥K₀ hK₀odd
  have hksolv : Group.IsSolvable φ.ker := by
    haveI : Group.IsSolvable ↥K₀ := hK₀solv
    exact Group.isSolvable_of_isSolvable_injective (f := ψ) hψinj
  have hker_dvd : Nat.card φ.ker ∣ Nat.card ↥K₀ := Subgroup.card_dvd_of_injective ψ hψinj
  have hK₀cop : Nat.Coprime k.q (Nat.card ↥K₀) := CFSG.pPrimeCore_coprime_card
  have hcop2 : Nat.Coprime (Nat.card φ.ker) 2 :=
    (Nat.Coprime.coprime_dvd_right hker_dvd (Nat.coprime_two_left.mpr hK₀odd)).symm
  have hcopp : Nat.Coprime (Nat.card φ.ker) k.q :=
    (Nat.Coprime.coprime_dvd_right hker_dvd hK₀cop).symm
  exact ⟨φ, hφsurj, hker_mem, Odd.of_dvd_nat hK₀odd hker_dvd,
    hcop2.mul_right hcopp, hksolv⟩

private lemma qPrimeElement_mem_centralizer
    {q : ℕ} (hq : q.Prime) {D R J : Subgroup G}
    (hJND : J ≤ Subgroup.normalizer (D : Set G))
    (hJR : J ≤ Subgroup.normalizer (R : Set G))
    (hDq : IsPGroup q ↥D)
    (hDfaith : ∀ K : Subgroup G, ¬ q ∣ Nat.card K →
      K ≤ Subgroup.normalizer (R : Set G) →
      K ≤ Subgroup.centralizer (D : Set G) →
      K ≤ Subgroup.centralizer (R : Set G))
    (conjD : ↥J →* MulAut ↥D)
    (hconjD : conjD = D.normalizerMonoidHom.comp (Subgroup.inclusion hJND))
    (ρ : ↥J →* MulAut (↥D ⧸ frattini ↥D))
    (hρ : ρ = 1)
    (hρdef : ρ = (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥D)).comp conjD) :
    ∀ j : ↥J, ¬ q ∣ orderOf j → (j : G) ∈ Subgroup.centralizer (R : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro j hjq
  have hρj : ρ j = 1 := by rw [hρ]; rfl
  rw [hρdef] at hρj
  have hquot1 : (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥D)) (conjD j) = 1 := by simpa using hρj
  have hmemker : conjD j ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥D)).ker := MonoidHom.mem_ker.mpr hquot1
  have hqker : IsPGroup q ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥D)).ker) :=
    (CFSG.GroupTheory.frattini_automorphism_kernel hDq).2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hqker ⟨conjD j, hmemker⟩
  have hord_eq : orderOf (conjD j) = q ^ k := by
    rw [← hk]
    exact (Subgroup.orderOf_mk (conjD j) hmemker).symm
  have hdvd : orderOf (conjD j) ∣ orderOf j := orderOf_map_dvd conjD j
  have hk0 : k = 0 := by
    by_contra hkne
    have hqk : q ∣ orderOf (conjD j) := by
      rw [hord_eq]
      exact dvd_pow_self q hkne
    exact hjq (hqk.trans hdvd)
  have hconj1 : conjD j = 1 := by
    apply orderOf_eq_one_iff.mp
    rw [hord_eq, hk0, pow_zero]
  have hconj1' : D.normalizerMonoidHom ⟨(j : G), hJND j.2⟩ = 1 := by
    rw [show (⟨(j : G), hJND j.2⟩ : Subgroup.normalizer (D : Set G)) =
      Subgroup.inclusion hJND j from Subtype.ext rfl]
    simpa [hconjD] using hconj1
  have hmem : (⟨(j : G), hJND j.2⟩ : Subgroup.normalizer (D : Set G)) ∈
      D.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr hconj1'
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
  have hordj : orderOf (j : G) = orderOf j :=
    (Subgroup.orderOf_mk (j : G) j.2).symm
  have hnotdvd : ¬ q ∣ Nat.card (Subgroup.zpowers (j : G)) := by
    rw [Nat.card_zpowers, hordj]
    exact hjq
  exact hDfaith (Subgroup.zpowers (j : G)) hnotdvd
    (Subgroup.zpowers_le.mpr (hJR j.2))
    (Subgroup.zpowers_le.mpr hmem) (Subgroup.mem_zpowers (j : G))

private lemma commutator_eq_bot_of_forall_qPrime_mem_centralizer
    {q : ℕ} (hq : q.Prime) {J R : Subgroup G} (hJperfect : Group.IsPerfect ↥J)
    (hJR : J ≤ Subgroup.normalizer (R : Set G))
    (hstep5 : ∀ j : ↥J, ¬ q ∣ orderOf j → (j : G) ∈ Subgroup.centralizer (R : Set G)) :
    ⁅J, R⁆ = ⊥ := by
  let CJ : Subgroup G := J ⊓ Subgroup.centralizer (R : Set G)
  have hJC : J ≤ Subgroup.normalizer (CJ : Set G) := by
    have key : ∀ g ∈ J, ∀ c ∈ CJ, g * c * g⁻¹ ∈ CJ := by
      intro g hg c hc
      obtain ⟨hcJ, hcC⟩ := Subgroup.mem_inf.mp hc
      refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hg hcJ) (J.inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hcC ⊢
      intro r hr
      have hgr : g⁻¹ * r * g ∈ R := by
        have h := (Subgroup.mem_normalizer_iff.mp (hJR (J.inv_mem hg)) r).mp hr
        simpa using h
      have hc' := hcC (g⁻¹ * r * g) hgr
      calc r * (g * c * g⁻¹) = g * (g⁻¹ * r * g) * c * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc']
        _ = (g * c * g⁻¹) * r := by group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact key g hg c hc
    · intro hc
      have hc' := key g⁻¹ (J.inv_mem hg) (g * c * g⁻¹) hc
      have heq : g⁻¹ * (g * c * g⁻¹) * (g⁻¹)⁻¹ = c := by group
      rwa [heq] at hc'
  let C : Subgroup ↥J := CJ.subgroupOf J
  haveI : C.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show CJ ≤ J from inf_le_left)).mpr hJC
  have hC : ∀ x : ↥J, ¬ q ∣ orderOf x → x ∈ C := by
    intro x hx
    have hxJ : (x : G) ∈ J := x.2
    have hxR : (x : G) ∈ Subgroup.centralizer (R : Set G) := hstep5 x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hxJ, hxR⟩)
  have hCtop : C = ⊤ :=
    CFSG.GroupTheory.eq_top_of_isPerfect_of_forall_not_dvd_orderOf_mem hq hJperfect hC
  have hJcentR : J ≤ Subgroup.centralizer (R : Set G) := by
    intro j hj
    have hjC : (⟨j, hj⟩ : ↥J) ∈ C := by
      rw [hCtop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hjC).2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJcentR

theorem commutator_layerLift_pCoreOf_eq_bot (k : S8Core G) {H : Subgroup G}
    (hH : k.Config H)
    (hB : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CoverActsTriviallyOnSmall k.q
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)))
    {q : ℕ} (hq : q.Prime) :
    ⁅CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H,
      CFSG.Open.pCoreOf q ((CFSG.pPrimeCore k.q ↥H).map H.subtype)⁆ = ⊥ := by
  classical
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let K : Subgroup G := K₀.map H.subtype
  let J : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H
  let R : Subgroup G := CFSG.Open.pCoreOf q K
  have hRK : R ≤ K := CFSG.LieType.BorelTits.pCoreOf_le q K
  have hKcard : Nat.card K = Nat.card ↥K₀ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact k.odd_card_pPrimeCore hH
  have hKcop : Nat.Coprime k.q (Nat.card K) := by
    rw [hKcard]
    exact CFSG.pPrimeCore_coprime_card
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype H K₀
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q K)
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H).trans hHR
  by_cases hRne : R = ⊥
  · change ⁅J, R⁆ = ⊥
    rw [hRne, Subgroup.commutator_bot_right]
  have hRq : IsPGroup q R := CFSG.LieType.BorelTits.pCoreOf_isPGroup q K
  have hq2 : q ≠ 2 := by
    intro hqeq
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2R : 2 ∣ Nat.card R := by
      rw [← hqeq]
      exact CFSG.RankThree.PartTwo.Sec21.dvd_card_of_isPGroup_ne_bot hRq hRne
    have h2K : 2 ∣ Nat.card K := h2R.trans (Subgroup.card_dvd_of_le hRK)
    exact Nat.not_even_iff_odd.mpr hKodd (even_iff_two_dvd.mpr h2K)
  have hqp : q ≠ k.q := by
    intro hqeq
    have hpR : k.q ∣ Nat.card R := by
      rw [← hqeq]
      exact CFSG.RankThree.PartTwo.Sec21.dvd_card_of_isPGroup_ne_bot hRq hRne
    have hpK : k.q ∣ Nat.card K := hpR.trans (Subgroup.card_dvd_of_le hRK)
    exact (hp.coprime_iff_not_dvd).mp hKcop hpK
  obtain ⟨D, hDR, hDN, hDexp, hDcl, hDfaith⟩ :=
    CFSG.RankThree.PartTwo.Sec5.Bender.exists_critical_faithful (p := q) hq2 hRq hRne
  have hJND : J ≤ Subgroup.normalizer (D : Set G) := fun j hj => hDN j (hJR hj)
  have hDq : IsPGroup q ↥D := hRq.to_le hDR
  have hDexp' : ∀ x : ↥D, x ^ q = 1 :=
    fun x => Subtype.ext (by simpa using hDexp (x : G) x.2)
  have hDrank : CFSG.Open.pRank q (⊤ : Subgroup ↥D) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) D]
    exact ((CFSG.SectionRank.pRank_mono hq.one_lt hDR).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt hRK)).trans (k.pRank_pPrimeCore_le_three hH hq)
  have hDcl' : ⁅⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆, (⊤ : Subgroup ↥D)⁆ = ⊥ := by
    rw [Subgroup.commutator_top_right_eq_bot_iff_le_center, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hmem : ⁅(a : G), (b : G)⁆ ∈ Subgroup.centralizer (D : Set G) :=
      hDcl (Subgroup.commutator_mem_commutator (H₁ := D) (H₂ := R) a.2 (hDR b.2))
    have hcommc := (Subgroup.mem_centralizer_iff.mp hmem) (g : G) g.2
    have hcoe : ((⁅a, b⁆ : ↥D) : G) = ⁅(a : G), (b : G)⁆ := map_commutatorElement D.subtype a b
    simpa only [Subgroup.coe_mul, hcoe] using hcommc
  have hVdata := CFSG.GroupTheory.frattini_elementary_quotient (p := q) hDq
  have hVcomm : ∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a :=
    fun a b => hVdata.2.1.is_comm.comm a b
  have hVexp : ∀ v : ↥D ⧸ frattini ↥D, v ^ q = 1 := hVdata.2.2.1
  have hVcard : Nat.card (↥D ⧸ frattini ↥D) ≤ q ^ 4 :=
    CFSG.GroupTheory.card_quotient_frattini_le_pow_four hDq hDexp' hDcl' hDrank
  let conjD : ↥J →* MulAut ↥D :=
    D.normalizerMonoidHom.comp (Subgroup.inclusion hJND)
  let ρ : ↥J →* MulAut (↥D ⧸ frattini ↥D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥D)).comp conjD
  obtain ⟨φ, hφsurj, -, -, hcop, hksolv⟩ := layerLift_ker_data k hH
  have hJperfect : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.commutator_layerLift k.q H)
  unfold CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CoverActsTriviallyOnSmall at hB
  have hρ : ρ = 1 :=
    hB ↥J hJperfect φ hφsurj hcop hksolv q hq hq2 hqp
      (↥D ⧸ frattini ↥D) hVcomm hVexp hVcard ρ
  have hstep5 := qPrimeElement_mem_centralizer hq hJND hJR hDq hDfaith conjD rfl ρ hρ rfl
  exact commutator_eq_bot_of_forall_qPrime_mem_centralizer hq hJperfect hJR hstep5

theorem step75_of_coverActsTriviallyOnSmall (k : S8Core G)
    (hB : ∀ H : Subgroup G, k.Config H →
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CoverActsTriviallyOnSmall k.q
        ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H))) :
    ∀ H : Subgroup G, k.Config H →
      ⁅CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H,
        (CFSG.pPrimeCore k.q ↥H).map H.subtype⁆ = ⊥ := by
  intro H hH
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let K : Subgroup G := K₀.map H.subtype
  have hKcard : Nat.card K = Nat.card ↥K₀ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact k.odd_card_pPrimeCore hH
  have hKsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥K hKodd
  have hJK : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H ≤
      Subgroup.normalizer (K : Set G) :=
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H).trans
      (CFSG.ABGLocalTools.le_normalizer_map_subtype H K₀)
  exact CFSG.GroupTheory.commutator_eq_bot_of_forall_pCoreOf hKsolv
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.commutator_layerLift k.q H) hJK
    (fun q hq => commutator_layerLift_pCoreOf_eq_bot k hH (hB H hH) hq)

theorem exists_twoLocal_four_le_threeRank_of_coverHasLargeTwoLocal (k : S8Core G)
    {H : Subgroup G} (hH : k.Config H)
    (h75 : ⁅CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H,
      (CFSG.pPrimeCore k.q ↥H).map H.subtype⁆ = ⊥)
    (hbad : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CoverHasLargeTwoLocal
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H))) :
    ∃ N : Subgroup G, CFSG.Open.IsTwoLocal N ∧ 4 ≤ CFSG.Open.pRank 3 N := by
  obtain ⟨φ, hφsurj, hker_mem, hφker_odd, -, -⟩ := layerLift_ker_data k hH
  let J : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let KG : Subgroup G := K₀.map H.subtype
  have hJH : J ≤ H :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift_le k.q H
  have hJperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.commutator_layerLift k.q H)
  have hφker_center : φ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hxK₀ : Subgroup.inclusion hJH x ∈ K₀ :=
      hker_mem x (MonoidHom.mem_ker.mp hx)
    have hxKG : (x : G) ∈ KG := Subgroup.mem_map_of_mem H.subtype hxK₀
    have hcommKG : KG ≤ Subgroup.centralizer (J : Set G) := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := KG) (H₂ := J)).mp ?_
      simpa [Subgroup.commutator_comm] using h75
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcommKG hxKG) (y : G) y.2
  obtain ⟨U, hUne, hU2, hU4⟩ := hbad ↥J hJperf φ hφsurj hφker_center hφker_odd
  let UG : Subgroup G := U.map J.subtype
  have hUGne : UG ≠ ⊥ := by
    rintro h
    exact hUne ((Subgroup.map_eq_bot_iff_of_injective U J.subtype_injective).mp h)
  have hUG2 : IsPGroup 2 UG := hU2.map J.subtype
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (UG : Set G)) :=
    ⟨UG, hUGne, hUG2, rfl⟩
  have hle : (Subgroup.normalizer (U : Set ↥J)).map J.subtype ≤
      Subgroup.normalizer (UG : Set G) := Subgroup.le_normalizer_map J.subtype
  have h4G : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (UG : Set G)) :=
    hU4.trans ((CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) J.subtype
      J.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle))
  exact ⟨_, hloc, h4G⟩

theorem four_le_localRank_of_cover (k : S8Core G) {H : Subgroup G} (hH : k.Config H)
    (h75 : ⁅CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.layerLift k.q H,
      (CFSG.pPrimeCore k.q ↥H).map H.subtype⁆ = ⊥)
    (hbad : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CoverHasLargeTwoLocal
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H))) :
    4 ≤ CFSG.Open.rankThreeLocalRank 3 G := by
  obtain ⟨N, hloc, h4G⟩ :=
    exists_twoLocal_four_le_threeRank_of_coverHasLargeTwoLocal k hH h75 hbad
  change 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G
  exact h4G.trans (le_csSup
    (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3 Nat.prime_three)
    ⟨_, hloc, rfl⟩)

end S8Core

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
