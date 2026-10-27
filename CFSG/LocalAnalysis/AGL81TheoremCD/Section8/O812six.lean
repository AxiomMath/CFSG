module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.SEStep75
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.AltTen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec21.StronglyEmbedded
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.Open CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_ne_top_of_nontrivial_le {F M : Subgroup G} (hC : CStarGen G)
    (hFM : F ≤ M) (hFne : F ≠ ⊥) (hMne : M ≠ ⊤) :
    Subgroup.normalizer (F : Set G) ≠ ⊤ := by
  intro htop
  haveI : F.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
  haveI := hC.simple
  have htopF : F = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal F).resolve_left hFne
  exact hMne (top_le_iff.mp (htopF ▸ hFM))

private theorem config_of_normalizer (k : S8Core G) {F : Subgroup G}
    (hFM : F ≤ k.M) (hFne : F ≠ ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank k.q (k.M ⊓ Subgroup.centralizer (F : Set G)))
    (hnotle : ¬ Subgroup.normalizer (F : Set G) ≤ k.M) :
    k.Config (Subgroup.normalizer (F : Set G)) := by
  refine ⟨?_, hnotle, ?_⟩
  · exact normalizer_ne_top_of_nontrivial_le k.cstar hFM hFne k.M_ne_top
  · have hle : k.M ⊓ Subgroup.centralizer (F : Set G) ≤
        Subgroup.normalizer (F : Set G) ⊓ k.M :=
      le_inf (inf_le_right.trans (Subgroup.centralizer_le_normalizer (F : Set G))) inf_le_left
    exact hrank.trans (CFSG.SectionRank.pRank_mono k.prime.one_lt hle)

private theorem isPSolvable_inf_of_solvable_map (k : S8Core G) {H : Subgroup G}
    (hH : k.Config H)
    (hsol : Group.IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.q ↥H)))) :
    CFSG.HallHigman.IsPSolvable k.q ↥(H ⊓ k.M) := by
  classical
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  let K : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let π : ↥H →* (↥H ⧸ K) := QuotientGroup.mk' K
  let HM : Subgroup G := H ⊓ k.M
  let KG : Subgroup G := K.map H.subtype
  let KH : Subgroup ↥HM := KG.subgroupOf HM
  have hKle : KG ≤ HM := le_inf (Subgroup.map_subtype_le K) (k.pPrimeCore_le hH)
  have hKGnorm : H ≤ Subgroup.normalizer (KG : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype H K
  haveI : KH.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr (inf_le_left.trans hKGnorm)
  have hcardKH : Nat.card ↥KH = Nat.card ↥K := by
    have h1 : Nat.card ↥KH = Nat.card ↥KG := CFSG.natCard_subgroupOf_eq KG HM hKle
    rw [h1, Subgroup.card_map_of_injective H.subtype_injective]
  have hcop : Nat.Coprime k.q (Nat.card ↥KH) := by
    rw [hcardKH]
    exact CFSG.pPrimeCore_coprime_card
  let φ : ↥HM →* (↥H ⧸ K) := π.comp (Subgroup.inclusion (inf_le_left : HM ≤ H))
  have hmem_map : ∀ y : ↥H, (y : G) ∈ KG ↔ y ∈ K := by
    intro y
    constructor
    · intro hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      simpa [Subtype.ext hwy] using hw
    · exact Subgroup.mem_map_of_mem H.subtype
  have hφker : φ.ker = KH := by
    ext x
    simp only [MonoidHom.mem_ker, φ, π, MonoidHom.comp_apply]
    change ((Subgroup.inclusion (inf_le_left : HM ≤ H) x : ↥H) : (↥H ⧸ K)) = 1 ↔ x ∈ KH
    rw [QuotientGroup.eq_one_iff]
    rw [← hmem_map (Subgroup.inclusion (inf_le_left : HM ≤ H) x)]
    rw [Subgroup.coe_inclusion, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = ((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.q ↥H)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hsol' : Group.IsSolvable ↥φ.range := by
    rw [hφrange]
    exact hsol
  have hsolker : Group.IsSolvable (↥HM ⧸ φ.ker) := by
    haveI := hsol'
    exact Group.isSolvable_of_isSolvable_injective
      (QuotientGroup.quotientKerEquivRange φ).injective
  have hsolQ : Group.IsSolvable (↥HM ⧸ KH) := by
    haveI := hsolker
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hφker).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hφker).surjective
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable
    KH hcop hsolQ

private theorem two_le_pRank_three_of_two_le_map (k : S8Core G) {H : Subgroup G}
    (hN : 2 ≤ CFSG.Open.pRank 3
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.q ↥H)))) :
    2 ≤ CFSG.Open.pRank 3 k.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let π : ↥H →* (↥H ⧸ K) := QuotientGroup.mk' K
  let HM : Subgroup G := H ⊓ k.M
  let N : Subgroup (↥H ⧸ K) := (HM.subgroupOf H).map π
  have hNdef : N = ((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.q ↥H)) := rfl
  let ψ₀ : ↥HM →* (↥H ⧸ K) := π.comp (Subgroup.inclusion (inf_le_left : HM ≤ H))
  have hψ₀range : ψ₀.range = N := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let ψ : ↥HM →* N := ψ₀.codRestrict N
    (fun x => hψ₀range ▸ ⟨x, rfl⟩)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : ↥H ⧸ K) ∈ ψ₀.range := by
      rw [hψ₀range]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hNrank : 2 ≤ CFSG.Open.pRank 3 N := hNdef ▸ hN
  let T : Sylow 3 ↥HM := default
  have hTnc : ¬ IsCyclic (T : Subgroup ↥HM) := by
    intro hTcyc
    have hScyc : IsCyclic ((T : Subgroup ↥HM).map ψ) := by
      haveI := hTcyc
      have hrange : (ψ.comp (T : Subgroup ↥HM).subtype).range =
          (T : Subgroup ↥HM).map ψ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact isCyclic_of_surjective (ψ.comp (T : Subgroup ↥HM).subtype).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    have hQcyc : IsCyclic ((T.mapSurjective hψsurj : Sylow 3 N) : Subgroup N) := by
      rw [Sylow.coe_mapSurjective]
      exact hScyc
    have hQrank : 2 ≤ CFSG.Open.pRank 3
        ((T.mapSurjective hψsurj : Sylow 3 N) : Subgroup N) := by
      rw [(CFSG.SectionRank.pRank_sylow (T.mapSurjective hψsurj)).1]
      rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup N] at hNrank
    have hle1 : CFSG.Open.pRank 3
        ((T.mapSurjective hψsurj : Sylow 3 N) : Subgroup N) ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hQcyc
    omega
  have h2T : 2 ≤ CFSG.Open.pRank 3 (T : Subgroup ↥HM) :=
    CFSG.AGLEmbedding.two_le_pRank_of_isPGroup_not_isCyclic Nat.prime_three (by norm_num)
      T.isPGroup' hTnc
  have h2HM : 2 ≤ CFSG.Open.pRank 3 HM := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup HM]
    exact h2T.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top)
  exact h2HM.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_right)

private theorem layerLift_map_alternatingTen (k : S8Core G) {H : Subgroup G} (hH : k.Config H)
    (e : ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)) ≃*
      alternatingGroup (Fin 10)) :
    ∃ φ : ↥(layerLift k.q H) →* alternatingGroup (Fin 10),
      Function.Surjective φ ∧
        φ.ker ≤ ((CFSG.pPrimeCore k.q ↥H).map H.subtype).subgroupOf (layerLift k.q H) := by
  classical
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  let K : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let π : ↥H →* (↥H ⧸ K) := QuotientGroup.mk' K
  let Lbar : Subgroup (↥H ⧸ K) := CFSG.generalizedFitting (↥H ⧸ K)
  let J : Subgroup G := layerLift k.q H
  let KG : Subgroup G := K.map H.subtype
  have hJH : J ≤ H := layerLift_le k.q H
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar := map_layerLift_eq k.q H hLbarperf
  let φ₀ : ↥J →* (↥H ⧸ K) := π.comp (Subgroup.inclusion hJH)
  have hφ₀range : φ₀.range = Lbar := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hmap
  let φL : ↥J →* ↥Lbar := φ₀.codRestrict Lbar
    (fun x => hφ₀range ▸ ⟨x, rfl⟩)
  have hφLsurj : Function.Surjective φL := by
    intro y
    have hy : (y : ↥H ⧸ K) ∈ φ₀.range := by
      rw [hφ₀range]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let φ : ↥J →* alternatingGroup (Fin 10) := e.toMonoidHom.comp φL
  have hφsurj : Function.Surjective φ := e.surjective.comp hφLsurj
  have hker_le : ∀ x : ↥J, φ x = 1 → (x : G) ∈ KG := by
    intro x hx
    have hxL : φL x = 1 := by
      apply e.injective
      simpa [φ] using hx
    have hx₀ : φ₀ x = 1 := by
      simpa [φL] using congrArg Subtype.val hxL
    exact Subgroup.mem_map_of_mem H.subtype
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJH x)).mp hx₀)
  exact ⟨φ, hφsurj, fun x hx => Subgroup.mem_subgroupOf.mpr (hker_le x hx)⟩

private theorem layerLift_ker_center_and_odd (k : S8Core G) {H : Subgroup G} (hH : k.Config H)
    (h75 : ⁅layerLift k.q H, (CFSG.pPrimeCore k.q ↥H).map H.subtype⁆ = ⊥)
    (φ : ↥(layerLift k.q H) →* alternatingGroup (Fin 10))
    (hker : φ.ker ≤ ((CFSG.pPrimeCore k.q ↥H).map H.subtype).subgroupOf (layerLift k.q H)) :
    φ.ker ≤ Subgroup.center ↥(layerLift k.q H) ∧ Odd (Nat.card φ.ker) := by
  classical
  let J : Subgroup G := layerLift k.q H
  let KG : Subgroup G := (CFSG.pPrimeCore k.q ↥H).map H.subtype
  have hcent : KG ≤ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.commutator_comm] at h75
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := KG) (H₂ := J)).mp h75
  constructor
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (hcent (Subgroup.mem_subgroupOf.mp (hker hx))) (y : G) y.2
  · have hcardsub : Nat.card ↥(KG.subgroupOf J) = Nat.card (KG ⊓ J : Subgroup G) := by
      have hsub : KG.subgroupOf J = (KG ⊓ J).subgroupOf J := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rw [hsub, CFSG.natCard_subgroupOf_eq (KG ⊓ J) J inf_le_right]
    have hdiv : Nat.card φ.ker ∣ Nat.card ↥KG :=
      (Subgroup.card_dvd_of_le hker).trans (hcardsub ▸
        Subgroup.card_dvd_of_le (inf_le_left : KG ⊓ J ≤ KG))
    have hoddKG : Odd (Nat.card ↥KG) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact k.odd_card_pPrimeCore hH
    exact Odd.of_dvd_nat hoddKG hdiv

private theorem exists_orderOf_eq_three_centralizing_layerLift (k : S8Core G)
    {H : Subgroup G} {F : Subgroup G} (hFM : F ≤ k.M) (hF3 : IsPGroup 3 F) (hFne : F ≠ ⊥)
    (hFH : F ≤ H) (hHnorm : H ≤ Subgroup.normalizer (F : Set G)) (h5 : 5 ≤ k.q)
    (h75 : ⁅layerLift k.q H, (CFSG.pPrimeCore k.q ↥H).map H.subtype⁆ = ⊥) :
    ∃ z : G, orderOf z = 3 ∧ ∀ j ∈ layerLift k.q H, z * j = j * z := by
  classical
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  have hq3 : k.q ≠ 3 := by omega
  let K : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let J : Subgroup G := layerLift k.q H
  let KG : Subgroup G := K.map H.subtype
  have h3dvd : 3 ∣ Nat.card F :=
    CFSG.RankThree.PartTwo.Sec21.dvd_card_of_isPGroup_ne_bot hF3 hFne
  obtain ⟨zF, hz3F⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  refine ⟨(zF : G), (Subgroup.orderOf_coe zF).trans hz3F, ?_⟩
  have hFh_normal : (F.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFH).mpr hHnorm
  have hcard : Nat.card ↥(F.subgroupOf H) = Nat.card F :=
    CFSG.natCard_subgroupOf_eq F H hFH
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hF3
  have hcop3 : Nat.Coprime k.q 3 :=
    (Nat.coprime_primes hp Nat.prime_three).mpr hq3
  have hcopF : Nat.Coprime k.q (Nat.card F) := by
    rw [hn]
    exact hcop3.pow_right n
  have hcop : Nat.Coprime k.q (Nat.card ↥(F.subgroupOf H)) := by
    rwa [hcard]
  have hFh_le : F.subgroupOf H ≤ K := by
    intro x hx
    change x ∈ sSup (CFSG.normalPPrimeSubgroups k.q ↥H)
    exact le_sSup (show F.subgroupOf H ∈ CFSG.normalPPrimeSubgroups k.q ↥H from
      ⟨hFh_normal, hcop⟩) hx
  have hzK : (⟨(zF : G), hFH zF.2⟩ : ↥H) ∈ K :=
    hFh_le (Subgroup.mem_subgroupOf.mpr zF.2)
  have hzKG : (zF : G) ∈ KG := Subgroup.mem_map_of_mem H.subtype hzK
  have hcent : KG ≤ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.commutator_comm] at h75
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := KG) (H₂ := J)).mp h75
  intro j hj
  exact (Subgroup.mem_centralizer_iff.mp (hcent hzKG) j hj).symm

private theorem false_of_normalizer_not_le (hSE : StronglyEmbeddedFive)
    (hId : StronglyEmbeddedSolvableId) (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (k : S8Core G) (h5 : 5 ≤ k.q) {F : Subgroup G} (hFM : F ≤ k.M) (hF3 : IsPGroup 3 F)
    (hFne : F ≠ ⊥) (hH : k.Config (Subgroup.normalizer (F : Set G)))
    (hnot : ¬ CFSG.HallHigman.IsPSolvable k.q
      ↥(k.M ⊓ Subgroup.centralizer (F : Set G)))
    (h3not : 3 ∉ sigmaSet G k.M) : False := by
  classical
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  have hstep75 : ∀ H : Subgroup G, k.Config H →
      ⁅layerLift k.q H, (CFSG.pPrimeCore k.q ↥H).map H.subtype⁆ = ⊥ :=
    k.step75_of_coverActsTriviallyOnSmall
      (fun H hH => k.coverActsTriviallyOnSmall_of_stronglyEmbeddedFive h5 hH hSE)
  let H : Subgroup G := Subgroup.normalizer (F : Set G)
  let K : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let X := ↥H ⧸ K
  let N : Subgroup X := ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' K)
  have hN : IsStronglyPEmbedded k.q N := k.isStronglyPEmbedded_map_quotient_pPrimeCore hH
  have hK : CFSG.Open.IsKGroup X :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient'
      (CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.cstar.kProper hH.ne_top) K
  have hO : CFSG.pPrimeCore k.q X = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have h2 : 2 ≤ CFSG.Open.pRank k.q (⊤ : Subgroup X) :=
    k.two_le_pRank_quotient_pPrimeCore hH
  have hC_le : k.M ⊓ Subgroup.centralizer (F : Set G) ≤ H ⊓ k.M :=
    le_inf (inf_le_right.trans (Subgroup.centralizer_le_normalizer (F : Set G))) inf_le_left
  rcases hId k.q hp h5 X hK hO h2 N hN with hsol | ⟨h3N, hcov | ⟨hq5, ⟨eL⟩⟩⟩
  · exact hnot (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (isPSolvable_inf_of_solvable_map k hH hsol) hC_le)
  · have h3M : 2 ≤ CFSG.Open.pRank 3 k.M :=
      two_le_pRank_three_of_two_le_map k h3N
    have h4 : 4 ≤ CFSG.Open.rankThreeLocalRank 3 G :=
      k.four_le_localRank_of_cover hH (hstep75 H hH) hcov
    exact h3not ⟨mem_sigmaA_of_four_le_localRank Nat.prime_three (by norm_num) h4, h3M⟩
  · have h3M : 2 ≤ CFSG.Open.pRank 3 k.M :=
      two_le_pRank_three_of_two_le_map k h3N
    have h4 : 4 ≤ CFSG.Open.rankThreeLocalRank 3 G := by
      obtain ⟨φ, hφsurj, hφker_sub⟩ := layerLift_map_alternatingTen k hH eL
      obtain ⟨hφker, hφodd⟩ := layerLift_ker_center_and_odd k hH (hstep75 H hH) φ hφker_sub
      have hFH : F ≤ H := Subgroup.le_normalizer
      have hHnorm : H ≤ Subgroup.normalizer (F : Set G) := le_of_eq rfl
      obtain ⟨z, hz, hzJ⟩ :=
        exists_orderOf_eq_three_centralizing_layerLift k hFM hF3 hFne hFH hHnorm h5
          (hstep75 H hH)
      exact four_le_localRank_of_altTen hKSM
        (Subgroup.isPerfect_iff.mpr (commutator_layerLift k.q H)) φ hφsurj hφker hφodd hz hzJ
    exact h3not ⟨mem_sigmaA_of_four_le_localRank Nat.prime_three (by norm_num) h4, h3M⟩

theorem o812sixAt_of_inputs (hSE : StronglyEmbeddedFive)
    (hId : StronglyEmbeddedSolvableId) (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hs : ∀ q ∈ sigmaSet G M, IsStronglyPEmbedded q M) :
    Section15.O812sixAt G M := by
  intro q hqM h5 F hFM hF3 hFne _ hrank hnot
  have hq : q ∈ sigmaSet G M := by
    simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hqM
  let k : S8Core G := S8Core.ofGen hC hM hq hs
  let H : Subgroup G := Subgroup.normalizer (F : Set G)
  by_cases h3 : 3 ∈ sigmaSet G M
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (hs 3 h3).normalizer_le hFne hF3 hFM
  · by_contra hle
    have hH : k.Config H := config_of_normalizer k hFM hFne hrank hle
    exact false_of_normalizer_not_le hSE hId hKSM k h5 hFM hF3 hFne hH hnot h3

theorem o812sixGen_of_inputs (hSE : StronglyEmbeddedFive)
    (hId : StronglyEmbeddedSolvableId) (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt) :
    Section15.O812sixGen := by
  intro G _ _ hC M hM _ hs
  exact o812sixAt_of_inputs hSE hId hKSM hC hM hs

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
