module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {p r k : ℕ}

theorem starImg_zpowers_central (hp : p.Prime) {x : G} (hxH : x ∈ H)
    (hxc : ∀ y ∈ H, x * y = y * x) (hx : orderOf x = p) :
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨x, hxH⟩ : StarGroup p H) ∈
        Subgroup.center (StarGroup p H) ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨x, hxH⟩ :
        StarGroup p H) = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hOcop : p.Coprime (Nat.card O) := by
    simpa [O] using primeComplementCore_coprime (G := ↥H) p
  have hx' : orderOf (⟨x, hxH⟩ : ↥H) = p := by
    rw [← Subgroup.orderOf_coe (⟨x, hxH⟩ : ↥H)]
    exact hx
  have hxpow : (⟨x, hxH⟩ : ↥H) ^ p = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hx'])
  have hzpow : π ⟨x, hxH⟩ ^ p = 1 := by
    rw [← map_pow, hxpow, map_one]
  have hzne : π ⟨x, hxH⟩ ≠ 1 := by
    intro hz
    have hxO : (⟨x, hxH⟩ : ↥H) ∈ O := (QuotientGroup.eq_one_iff _).mp hz
    have hdvd : orderOf (⟨x, hxH⟩ : ↥H) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    rw [hx'] at hdvd
    exact (hp.coprime_iff_not_dvd.mp hOcop) hdvd
  constructor
  · rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O g
    show π y * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa [mul_comm] using (hxc y y.2).symm)
  · exact orderOf_eq_prime hzpow hzne

theorem starImg_normalizes {S Y : Subgroup G}
    (hN : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S) :
    ∀ y ∈ starImg p H Y, ∀ s ∈ starImg p H S, y * s * y⁻¹ ∈ starImg p H S := by
  intro y hy s hs
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
  have hconj : (y₀ : G) * s₀ * (y₀ : G)⁻¹ ∈ S :=
    hN (y₀ : G) (Subgroup.mem_subgroupOf.mp hy₀) (s₀ : G)
      (Subgroup.mem_subgroupOf.mp hs₀)
  refine Subgroup.mem_map.mpr ⟨y₀ * s₀ * y₀⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    simpa using hconj
  · rw [map_mul, map_mul, map_inv]

private theorem exists_lift_isPGroup (hp : p.Prime) {E : Subgroup (StarGroup p H)}
    (hE : IsPGroup p E) :
    ∃ B₁ : Subgroup ↥H, IsPGroup p B₁ ∧ starImg p H (B₁.map H.subtype) = E ∧
      Nat.card (B₁.map H.subtype) = Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hOcop : p.Coprime (Nat.card O) := by
    simpa [O] using primeComplementCore_coprime (G := ↥H) p
  let U : Subgroup ↥H := E.comap π
  have hOleU : O ≤ U := by
    intro x hx
    rw [Subgroup.mem_comap]
    show π x ∈ E
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact E.one_mem
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  have hcardU : Nat.card ↥U = Nat.card O * Nat.card E := by
    simpa [U, O, π] using CFSG.ABGLocalTools.card_comap_mk' O E
  have hdvd : p ^ n ∣ Nat.card ↥U := by
    rw [hcardU, hn]
    exact Dvd.intro_left _ rfl
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥U) p (n := n) hdvd
  have hKp : IsPGroup p K := IsPGroup.of_card hK
  have hker_le : (π.comp U.subtype).ker ≤ O.subgroupOf U := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff (U.subtype x)).mp (by simpa [π] using hx)
  have hker_dvd : Nat.card ↥(π.comp U.subtype).ker ∣ Nat.card O := by
    have h1 : Nat.card ↥(O.subgroupOf U) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleU).toEquiv
    rw [← h1]
    have h2 := Subgroup.card_subgroup_dvd_card
      ((π.comp U.subtype).ker.subgroupOf (O.subgroupOf U))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv] at h2
    exact h2
  have hker_cop : p.Coprime (Nat.card ↥(π.comp U.subtype).ker) :=
    hOcop.coprime_dvd_right hker_dvd
  have hdisj : K ⊓ (π.comp U.subtype).ker = ⊥ :=
    CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hKp hker_cop
  have hcardmap : Nat.card (K.map (π.comp U.subtype)) = p ^ n := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot (π.comp U.subtype) hdisj, hK]
  have hmap_le : K.map (π.comp U.subtype) ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact Subgroup.mem_comap.mp x.2
  have hmap_eq : K.map (π.comp U.subtype) = E := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [hcardmap, hn]
  refine ⟨K.map U.subtype, hKp.map _, ?_, ?_⟩
  · change (Subgroup.comap H.subtype ((K.map U.subtype).map H.subtype)).map π = E
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective, Subgroup.map_map]
    exact hmap_eq
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective U.subtype_injective, hK, hn]

private theorem exists_isPGroup_r_normalizing (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {T : Subgroup (StarGroup p H)} (hT : T ≠ ⊥) (hT2 : IsPGroup r T)
    {B₁ : Subgroup ↥H} (hB₁ : IsPGroup p B₁)
    (hB₁n : B₁ ≤ Subgroup.normalizer
      ((T.comap (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))) : Set ↥H)) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup r W ∧
      B₁.map H.subtype ≤ Subgroup.normalizer (W : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  let T₁ : Subgroup ↥H := T.comap π
  have hOcop : p.Coprime (Nat.card O) := by
    simpa [O] using primeComplementCore_coprime (G := ↥H) p
  have hcardT₁ : Nat.card ↥T₁ = Nat.card O * Nat.card T := by
    simpa [T₁, O, π] using CFSG.ABGLocalTools.card_comap_mk' O T
  have hrT : r ∣ Nat.card T := by
    rcases hT2.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hT
    · exact h1
  have hpT : ¬ p ∣ Nat.card T := by
    obtain ⟨m, hm⟩ := hT2.exists_card_eq
    rw [hm]
    intro hdvd
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd))
  have hpT₁ : ¬ p ∣ Nat.card ↥T₁ := by
    rw [hcardT₁]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with hO | hT'
    · exact (hp.coprime_iff_not_dvd.mp hOcop) hO
    · exact hpT hT'
  obtain ⟨R, hRsyl, hB₁R⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime (G := ↥H) hp hr hB₁ hB₁n hpT₁
  have hrT₁ : r ∣ Nat.card ↥T₁ := by
    rw [hcardT₁]
    exact dvd_mul_of_dvd_right hrT _
  have hRne : R ≠ ⊥ := by
    intro hbot
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
    rw [hbot, Subgroup.relIndex_bot_left] at h
    exact h hrT₁
  have hWne : R.map H.subtype ≠ ⊥ := by
    intro hbot
    apply hRne
    have hcard := Subgroup.card_map_of_injective H.subtype_injective (K := R)
    rw [hbot, Subgroup.card_bot] at hcard
    exact Subgroup.card_eq_one.mp hcard.symm
  refine ⟨R.map H.subtype, hWne, hRsyl.isPGroup.map H.subtype, ?_⟩
  exact (Subgroup.map_mono hB₁R).trans (Subgroup.le_normalizer_map H.subtype)

theorem pRank_normalizer_starImg_le (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (h : ∀ W : Subgroup G, W ≠ ⊥ → IsPGroup r W →
      CFSG.Open.pRank p (Subgroup.normalizer (W : Set G)) ≤ k) :
    ∀ T : Subgroup (StarGroup p H), T ≠ ⊥ → IsPGroup r T →
      CFSG.Open.pRank p (Subgroup.normalizer (T : Set (StarGroup p H))) ≤ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  intro T hT hT2
  refine CFSG.SectionRank.pRank_le hp.one_lt
    (H := Subgroup.normalizer (T : Set (StarGroup p H))) (k := k) ?_
  intro E hEN hE
  obtain ⟨B₁, hB₁, hstar, hcard⟩ :=
    exists_lift_isPGroup (p := p) (H := H) hp (elementary_isPGroup p E hE)
  let B : Subgroup G := B₁.map H.subtype
  have hBH : B ≤ H := Subgroup.map_subtype_le B₁
  have hB : IsPGroup p B := hB₁.map H.subtype
  have hBelem : IsElemAbelian p B :=
    (isElemAbelian_starImg_iff hp hBH hB).mp (hstar ▸ hE)
  have hB₁le : B₁ ≤ E.comap π := by
    intro b hb
    rw [Subgroup.mem_comap]
    have hb' : π b ∈ starImg p H B := by
      refine Subgroup.mem_map.mpr ⟨b, ?_, rfl⟩
      change b ∈ Subgroup.comap H.subtype (Subgroup.map H.subtype B₁)
      rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hb
    rwa [hstar] at hb'
  have hB₁n : B₁ ≤ Subgroup.normalizer (T.comap π : Set ↥H) := by
    intro b hb
    have hbE : π b ∈ E := Subgroup.mem_comap.mp (hB₁le hb)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have hconj : π b * π t * (π b)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hEN hbE) (π t)).mp ht
      show π (b * t * b⁻¹) ∈ T
      simpa only [map_mul, map_inv] using hconj
    · intro ht
      change π (b * t * b⁻¹) ∈ T at ht
      have hconj : π b * π t * (π b)⁻¹ ∈ T := by
        simpa only [map_mul, map_inv] using ht
      show π t ∈ T
      exact (Subgroup.mem_normalizer_iff.mp (hEN hbE) (π t)).mpr hconj
  obtain ⟨W, hWne, hW2, hBW⟩ := exists_isPGroup_r_normalizing hp hr hpr hT hT2 hB₁ hB₁n
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hnle : n ≤ CFSG.Open.pRank p (Subgroup.normalizer (W : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hBW hBelem hn
  have hle := h W hWne hW2
  rw [← hcard, hn]
  exact Nat.pow_le_pow_right hp.pos (hnle.trans hle)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
