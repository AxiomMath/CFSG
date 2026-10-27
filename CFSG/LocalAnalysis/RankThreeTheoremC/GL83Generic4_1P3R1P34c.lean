module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem p34_rankThreePrimeCore_le (J : Subgroup G) : rankThreePrimeCore 3 J ≤ J :=
  sSup_le fun _ hN => hN.1

theorem p34_isSimpleGroup {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsM11Normal M x J) :
    IsSimpleGroup ↥(r1sBar x J) := by
  have hJC := hJ.le_centralizer
  set φ : ↥J →* ↥(r1sBar x J) := r1sHom x hJC with hφ
  have hsurj : Function.Surjective φ := r1sHom_surjective x hJC
  have hker : φ.ker = (rankThreePrimeCore 3 J).subgroupOf J := ker_r1sHom hJ
  have : Nontrivial ↥(r1sBar x J) := by
    obtain ⟨j, hjJ, hjO⟩ := IsConcreteLE.exists_of_lt hJ.lt_core
    refine ⟨⟨φ ⟨j, hjJ⟩, 1, fun h => ?_⟩⟩
    have : (⟨j, hjJ⟩ : ↥J) ∈ φ.ker := h
    rw [hker] at this
    exact hjO (Subgroup.mem_subgroupOf.mp this)
  refine ⟨fun N hN => ?_⟩
  set N' : Subgroup ↥J := N.comap φ with hN'
  set NG : Subgroup G := N'.map J.subtype with hNG
  have hNGJ : NG ≤ J := Subgroup.map_subtype_le N'
  have hNGsub : NG.subgroupOf J = N' :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective N'
  have hNn : (NG.subgroupOf J).Normal := by rw [hNGsub]; exact Subgroup.normal_comap φ
  have hON : rankThreePrimeCore 3 J ≤ NG := by
    intro o ho
    have hoJ : o ∈ J := p34_rankThreePrimeCore_le J ho
    have h1 : (⟨o, hoJ⟩ : ↥J) ∈ φ.ker := by rw [hker]; exact Subgroup.mem_subgroupOf.mpr ho
    refine ⟨⟨o, hoJ⟩, ?_, rfl⟩
    show φ ⟨o, hoJ⟩ ∈ N
    rw [MonoidHom.mem_ker.mp h1]
    exact N.one_mem
  rcases hJ.minimal NG hNGJ hNn hON with h | h
  · left
    refine eq_bot_iff.mpr fun n hn => ?_
    obtain ⟨j, rfl⟩ := hsurj n
    have hj : j ∈ N' := hn
    have h2 : N' = φ.ker := by rw [← hNGsub, h, hker]
    rw [h2] at hj
    exact Subgroup.mem_bot.mpr hj
  · right
    refine eq_top_iff.mpr fun n _ => ?_
    obtain ⟨j, rfl⟩ := hsurj n
    have h2 : N' = ⊤ := by rw [← hNGsub, h, Subgroup.subgroupOf_self]
    have hj : j ∈ N' := by rw [h2]; exact Subgroup.mem_top j
    exact hj

theorem p34_yData (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J) :
    P34YData (GenericReduced 3 x) (r1sBar x J) := by
  have hnorm := r1sBar_normal hJ
  have hsimple := p34_isSimpleGroup hJ
  have hperf := r1sBar_perfect hJ
  have hcyc := m11_reducedCentralizer_isCyclic hS hU0 hKM hKA hp hM hgen hJ
  refine ⟨hnorm, hsimple, ?_, r1sBar_nonempty_equiv hJ,
    m11_reducedCentralizer_isPGroup hS hU0 hKM hKA hp hM hgen hJ, ?_,
    m11_bar_inf_reducedCentralizer_eq_bot hKM hKA hJ⟩
  · by_contra hab
    push Not at hab
    have : IsMulCommutative ↥(r1sBar x J) := ⟨⟨fun a b => hab a b⟩⟩
    have hsub := Group.IsPerfect.subsingleton_of_isMulCommutative (G := ↥(r1sBar x J))
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  · have : IsCyclic ↥(centralizer ((r1sBar x J : Subgroup (GenericReduced 3 x)) :
        Set (GenericReduced 3 x))) := hcyc
    exact inferInstance

theorem p34_mk_inj {C : Type*} [Group C] [Finite C] {O : Subgroup C} [O.Normal]
    (hO : Nat.Coprime 3 (Nat.card O))
    {T : Subgroup C} (hT : IsPGroup 3 T) {a b : C} (ha : a ∈ T) (hb : b ∈ T)
    (h : QuotientGroup.mk' O a = QuotientGroup.mk' O b) : a = b := by
  have h1 : a⁻¹ * b ∈ O := QuotientGroup.eq.mp h
  have h2 : a⁻¹ * b ∈ T ⊓ O := ⟨T.mul_mem (T.inv_mem ha) hb, h1⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup Nat.prime_three hT hO, Subgroup.mem_bot,
    inv_mul_eq_one] at h2
  exact h2

section Abstract

variable {C : Type} [Group C] [Finite C] (O : Subgroup C) [O.Normal]

theorem p34c_comm (hO : Nat.Coprime 3 (Nat.card O)) {L : Subgroup (C ⧸ O)}
    (hY : P34YData (C ⧸ O) L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (T : Sylow 3 C) {a b : C} (ha : a ∈ (T : Subgroup C))
    (hb : b ∈ (T : Subgroup C)) : a * b = b * a := by
  let Sbar : Sylow 3 (C ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O)
  have hSbar : (Sbar : Subgroup (C ⧸ O)) = (T : Subgroup C).map (QuotientGroup.mk' O) :=
    Sylow.coe_mapSurjective _ _
  have hcomm := hY.sylow_isMulCommutative hKM hKA Sbar
  have h1 : QuotientGroup.mk' O a ∈ (Sbar : Subgroup (C ⧸ O)) :=
    hSbar ▸ Subgroup.mem_map_of_mem _ ha
  have h2 : QuotientGroup.mk' O b ∈ (Sbar : Subgroup (C ⧸ O)) :=
    hSbar ▸ Subgroup.mem_map_of_mem _ hb
  have h3 := p34_comm_of_isMulCommutative hcomm h1 h2
  refine p34_mk_inj hO T.isPGroup' (T.mul_mem ha hb) (T.mul_mem hb ha) ?_
  rw [map_mul, map_mul]
  exact h3

theorem p34c_commutator (L : Subgroup (C ⧸ O)) (hY : P34YData (C ⧸ O) L)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hSig : SignalizerTwoGroupKFact) (T : Sylow 3 C) {F : Subgroup C} (hF : IsPGroup 2 F)
    (hn : ∀ s ∈ (T : Subgroup C), s ∈ normalizer (F : Set C)) :
    ∀ f ∈ F, ∀ s ∈ (T : Subgroup C), QuotientGroup.mk' O ⁅f, s⁆ = 1 := by
  let Sbar : Sylow 3 (C ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O)
  have hSbar : (Sbar : Subgroup (C ⧸ O)) = (T : Subgroup C).map (QuotientGroup.mk' O) :=
    Sylow.coe_mapSurjective _ _
  have hFbar2 : IsPGroup 2 (F.map (QuotientGroup.mk' O)) := hF.map _
  have hnorm : ∀ s ∈ (Sbar : Subgroup (C ⧸ O)),
      s ∈ normalizer ((F.map (QuotientGroup.mk' O) : Subgroup (C ⧸ O)) : Set (C ⧸ O)) := by
    intro s hs
    rw [hSbar] at hs
    obtain ⟨c, hc, rfl⟩ := hs
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' O) ⟨c, hn c hc, rfl⟩
  have hcomm := hY.sylow_commute_two hKM hKA hSig Sbar hFbar2 hnorm
  intro f hf s hs
  have h3 : QuotientGroup.mk' O s ∈ (Sbar : Subgroup (C ⧸ O)) :=
    hSbar ▸ Subgroup.mem_map_of_mem _ hs
  have h4 : QuotientGroup.mk' O f ∈ F.map (QuotientGroup.mk' O) :=
    Subgroup.mem_map_of_mem _ hf
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact (hcomm _ h3 _ h4).symm

end Abstract

theorem p34_isMulCommutative_of_isSylowOf {x : G} {J : Subgroup G}
    (hY : P34YData (GenericReduced 3 x) (r1sBar x J)) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) {Q₁ : Subgroup G}
    (hQ₁ : IsSylowOf 3 Q₁ (centralizer ({x} : Set G))) : IsMulCommutative Q₁ := by
  obtain ⟨T, rfl⟩ := hQ₁
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a', ha', ha⟩ := a.2
  obtain ⟨b', hb', hb⟩ := b.2
  apply Subtype.ext
  change (a : G) * b = b * a
  rw [← ha, ← hb]
  exact congrArg Subtype.val (p34c_comm (primeComplementCore (G := centralizer ({x} : Set G)) 3)
    (primeComplementCore_coprime 3) hY hKM hKA T ha' hb')

theorem p34_commutator_mem {x : G} {J : Subgroup G}
    (hY : P34YData (GenericReduced 3 x) (r1sBar x J)) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hSig : SignalizerTwoGroupKFact) {Q₁ T₁ : Subgroup G}
    (hQ₁ : IsSylowOf 3 Q₁ (centralizer ({x} : Set G))) (hT₁C : T₁ ≤ centralizer ({x} : Set G))
    (hT₁ : IsPGroup 2 T₁) (hn : Q₁ ≤ normalizer (T₁ : Set G)) :
    ∀ t ∈ T₁, ∀ q ∈ Q₁, ⁅t, q⁆ ∈ GLBPrimeCore 3 (centralizer ({x} : Set G)) := by
  have hQ₁C : Q₁ ≤ centralizer ({x} : Set G) := hQ₁.le
  obtain ⟨T, hT⟩ := id hQ₁
  have hTeq : (T : Subgroup ↥(centralizer ({x} : Set G))) =
      Q₁.subgroupOf (centralizer ({x} : Set G)) := by
    rw [Subgroup.subgroupOf, ← hT,
      Subgroup.comap_map_eq_self_of_injective (centralizer ({x} : Set G)).subtype_injective]
  set F : Subgroup ↥(centralizer ({x} : Set G)) := T₁.subgroupOf (centralizer ({x} : Set G))
    with hF
  have hF2 : IsPGroup 2 F := hT₁.comap_subtype
  have hnF : ∀ s ∈ (T : Subgroup ↥(centralizer ({x} : Set G))), s ∈ normalizer (F : Set _) := by
    intro c hc
    have hcQ : (c : G) ∈ Q₁ := by rw [hTeq] at hc; exact hc
    rw [mem_normalizer_iff]
    intro f
    show f ∈ T₁.subgroupOf _ ↔ (c * f * c⁻¹ : ↥(centralizer ({x} : Set G))) ∈ T₁.subgroupOf _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := mem_normalizer_iff.mp (hn hcQ) (f : G)
    simpa using this
  have hcomm := p34c_commutator (primeComplementCore (G := centralizer ({x} : Set G)) 3) _ hY hKM
    hKA hSig T hF2 hnF
  intro t ht q hq
  have htC : t ∈ centralizer ({x} : Set G) := hT₁C ht
  have hqC : q ∈ centralizer ({x} : Set G) := hQ₁C hq
  have h1 : (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G))) ∈ (T : Subgroup _) := by
    rw [hTeq]; exact hq
  have h2 : (⟨t, htC⟩ : ↥(centralizer ({x} : Set G))) ∈ F := ht
  have h7 := (CFSG.AGLEmbedding.mk'_primeComplementCore_eq_one_iff 3
    (⁅(⟨t, htC⟩ : ↥(centralizer ({x} : Set G))), (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G)))⁆ :
      ↥(centralizer ({x} : Set G)))).mp (hcomm _ h2 _ h1)
  simpa [commutatorElement_def] using h7

end CFSG.LocalAnalysis.RankThreeTheoremC
