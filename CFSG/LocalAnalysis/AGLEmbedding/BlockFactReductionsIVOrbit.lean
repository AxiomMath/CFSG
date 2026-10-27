module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVMain
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
import CFSG.LocalAnalysis.AGLEmbedding.BlockOutNine
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding.ParabHub
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification


theorem exists_elemAbelian_fixed_of_parabolicThree (hD4 : KFactD4TwoGraphCentralizer)
    (hUn : KFactUnitaryParabolicThreeRank) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (hcl : IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center Y))) {T J : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hNJ : Subgroup.normalizer (T : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer (T : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    (hO3 : IsMulCommutative ↥(CFSG.pCore 3 (↥J ⧸ primeComplementCore (G := ↥J) 3)))
    (hrank : Open.pRank 3 J ≤ 3) {E : Subgroup Y} (hEJ : E ≤ J) (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 3 ^ 3) (α : MulAut Y) (hα3 : α ^ 3 = 1)
    (hα : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ F : Subgroup Y, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2 ∧ ∀ x ∈ F, α x = x := by
  have : Group.IsPerfect Y := ⟨hY.1⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hout : 3 ∣ Nat.card (Outer Y) := by
    have hne : QuotientGroup.mk' (inner Y) α ≠ 1 := fun h =>
      hα ((QuotientGroup.eq_one_iff (N := inner Y) α).mp h)
    have ho : orderOf (QuotientGroup.mk' (inner Y) α) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hα3, map_one]) hne
    rw [← ho]
    exact orderOf_dvd_natCard _
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  obtain ⟨hT', hN1, hN2, hperf'⟩ := map_overgroup_of_central (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' (Subgroup.center Y)).le S hNJ hJ hperf
  rcases three_dvd_card_outer_census (kFactParabolicThreeCensus _ hcl _ _ hT' hN1 hN2 hperf')
    (hout.trans (card_outer_dvd_card_outer_centerQuotient Y)) with ⟨d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · have hα'3 : PerfectAutomorphisms.centerQuotientHom Y α ^ 3 = 1 := by
      rw [← map_pow, hα3, map_one]
    have hα' : PerfectAutomorphisms.centerQuotientHom Y α ∉
        (MulAut.conj : (Y ⧸ Subgroup.center Y) →* MulAut (Y ⧸ Subgroup.center Y)).range := by
      intro hmem
      apply hα
      have h1 : OuterAutomorphisms.centerQuotientOuterHom Y (QuotientGroup.mk' (inner Y) α) =
          1 := (QuotientGroup.eq_one_iff (N := inner (Y ⧸ Subgroup.center Y)) _).mpr hmem
      exact (QuotientGroup.eq_one_iff (N := inner Y) α).mp
        (OuterAutomorphisms.centerQuotient_outer_injective Y (h1.trans (map_one _).symm))
    obtain ⟨E', hE', hE'9, hfix⟩ := hD4 _ d hd ⟨e⟩ _ hα'3 hα'
    exact exists_elemAbelian_fixed_of_centerQuotient hZ α hE' hE'9 hfix
  · exact absurd hE27 (hUn Y hY hZ d hd ⟨e⟩ _ J hT hNJ hJ hperf hO3 hrank E hEJ hE)

section Bar

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_centralizer_of_blockPL (hD4 : KFactD4TwoGraphCentralizer)
    (hUn : KFactUnitaryParabolicThreeRank) (hTPL : CitedBlockTransvectionPL)
    (hA7PL : CitedBlockAltSevenPL) (h93 : Asc81bNineThree)
    {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hperfK : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))))
    (hrank : Open.pRank 3 (blockPL M S L) ≤ 3)
    (hO3 : IsMulCommutative ↥(CFSG.pCore 3
      (↥(blockPL M S L) ⧸ primeComplementCore (G := ↥(blockPL M S L)) 3)))
    (hE : ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ blockPL M S L ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3)
    {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hu3 : u ^ 3 ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (huL : u ∉ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    2 ≤ Open.pRank 3 (barM M L ⊓ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  obtain ⟨E, hEP, hE, hE27⟩ := hE
  have hperf := coprime_card_blockPL_of_perfect hL hperfK
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  rcases h93 G M S L hK hA hL with h1 | h2 | hr
  · exact absurd h1 hX
  · obtain ⟨T₁, hT₁, hN, hne, hJ⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    have hα3 : (barM M L).normalizerMonoidHom ⟨u, hu⟩ ^ 3 = 1 := by
      rw [← map_pow]
      refine MulEquiv.ext fun y => Subtype.ext ?_
      change u ^ 3 * (y : ↥M ⧸ CFSG.pCore 2 ↥M) * (u ^ 3)⁻¹ = y
      rw [← Subgroup.mem_centralizer_iff.mp hu3 y y.2, mul_inv_cancel_right]
    have hαn : (barM M L).normalizerMonoidHom ⟨u, hu⟩ ∉
        (MulAut.conj : ↥(barM M L) →* MulAut ↥(barM M L)).range := by
      rintro ⟨l, hl⟩
      apply huL
      have hcent : (l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * u ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨y, hy⟩)
        change (l : ↥M ⧸ CFSG.pCore 2 ↥M) * y * (l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ =
          u * y * u⁻¹ at h1
        calc y * ((l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * u) =
            (l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * ((l : ↥M ⧸ CFSG.pCore 2 ↥M) * y *
              (l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹) * u := by group
          _ = (l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * (u * y * u⁻¹) * u := by rw [h1]
          _ = (l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * u * y := by group
      rw [show u = (l : ↥M ⧸ CFSG.pCore 2 ↥M) * ((l : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * u) by group]
      exact Subgroup.mul_mem_sup l.2 hcent
    obtain ⟨F, hF, hF9, hfix⟩ := exists_elemAbelian_fixed_of_parabolicThree hD4 hUn
      hL.component.2.2 h2.1 hZ hT₁ hN hne hJ (isMulCommutative_pCore_subgroupOf hPL hO3)
      ((pRank_three_subgroupOf_le (Lb := barM M L) (P := blockPL M S L)).trans hrank)
      (E := E.subgroupOf (barM M L))
      (fun x hx => hEP hx) (isElemAbelian_comap_of_injective (barM M L).subtype_injective hE)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEP.trans hPL)).toEquiv, hE27]) _
      hα3 hαn
    refine le_pRank_of_elemAbelian_le (by norm_num) (E := F.map (barM M L).subtype) ?_
      (isElemAbelian_map_of_isElemAbelian _ hF) (by rw [Subgroup.card_map_of_injective
        (barM M L).subtype_injective, hF9])
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := congrArg Subtype.val (hfix x hx)
    change h * (x : ↥M ⧸ CFSG.pCore 2 ↥M) * h⁻¹ = x at h1
    calc h * (x : ↥M ⧸ CFSG.pCore 2 ↥M) = h * x * h⁻¹ * h := by group
      _ = x * h := by rw [h1]
  · have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    have := card_le_nine_of_blockPL_rest hTPL hA7PL hK hA hL hX hS hr hperf hEP hE3
    omega

theorem kFactBlockThreeOneOrbit_of (hD4 : KFactD4TwoGraphCentralizer)
    (hUn : KFactUnitaryParabolicThreeRank) (hPS : KFactParabolicThreeSylowSmall)
    (hTPL : CitedBlockTransvectionPL) (hA7PL : CitedBlockAltSevenPL) (h93 : Asc81bNineThree) :
    KFactBlockThreeOneOrbit := by
  intro G _ _ M S L hK hA hL hX hS hperfK hZ hrank hO3
  exact ⟨fun U hU hU3 => card_le_of_blockThreeOneOrbit hPS hTPL hA7PL h93 hK hA hL hX hS hperfK
      hrank hO3 hU hU3,
    fun hE _ hu hu3 huL => two_le_pRank_centralizer_of_blockPL hD4 hUn hTPL hA7PL h93 hK hA hL
      hX hS hperfK hZ hrank hO3 hE hu hu3 huL⟩

end Bar

end CFSG.AGLEmbedding
