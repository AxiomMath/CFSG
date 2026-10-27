module

public import CFSG.LocalAnalysis.RankThreeTheoremC.CentralizerGenerationKFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Consumer
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.CentralizerGenerationLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem centralizerGenerationThree_of_kfact3W (hS : Setting G)
    (hK : CentralizerGenerationKFact3W) : CentralizerGenerationThree G := by
  intro p hp hp3 P M D hext hPD z hzZ hz1 hcon E hEP hE hEc
  subst hp3
  have hprime := sigmaA_prime 3 hp
  have hodd := sigmaA_odd 3 hp
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hD := (hext.exists_normal_plane hS hp hPD).1
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  have hzD : z ∈ D := map_subtype_le _ hzZ
  have hzp : z ^ 3 = 1 := (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z hzD
  have hzc : z ∈ centralizer ((P : Subgroup G) : Set G) :=
    hext.center_le_centralizer hprime hodd hD hzZ
  set H := centralizer ({z} : Set G) with hHdef
  have hPH : (P : Subgroup G) ≤ H := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have hHtop : H ≠ ⊤ := fun htop => hS.normalizer_zpowers_ne_top hz1
    (eq_top_iff.2 (htop ▸ centralizer_singleton_le_normalizer_zpowers z))
  have hzH : z ∈ H := mem_centralizer_singleton_iff.mpr rfl
  set O : Subgroup H := primeComplementCore (G := H) 3 with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hO : (3 : ℕ).Coprime (Nat.card O) := primeComplementCore_coprime 3
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections (H ⧸ O) :=
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
  have hcore : primeComplementCore (G := H ⧸ O) 3 = ⊥ := primeComplementCore_quotient_eq_bot 3
  have hcon' : ¬ HasPrimeConstraint (G := H ⧸ O) 3 := fun h =>
    hcon (hasPrimeConstraint_of_quotient h)
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hzord : orderOf z = 3 := orderOf_eq_prime hzp hz1
  have hzHord : orderOf zH = 3 := by rw [← Subgroup.orderOf_coe]; exact hzord
  have hzbord : orderOf (π zH) = 3 :=
    CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO hzHord
  have hzbcen : π zH ∈ center (H ⧸ O) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective O g
    have : g' * zH = zH * g' := Subtype.ext (mem_centralizer_singleton_iff.mp g'.2)
    show π g' * π zH = π zH * π g'
    rw [← map_mul, ← map_mul, this]
  have hzbE := hext.mem_layer_quotient hS hp hD hPH hHtop hcon hzH hzD hzc hzp
  set Pbar : Sylow 3 (H ⧸ O) :=
    (P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective O) with hPbardef
  have hPbar : (Pbar : Subgroup (H ⧸ O)) = ((P : Subgroup G).subgroupOf H).map π := by
    rw [hPbardef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hrankPbar : CFSG.Open.pRank 3 (Pbar : Subgroup (H ⧸ O)) = 3 := by
    rw [hPbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
      map_subgroupOf_eq_of_le hPH]
    exact hP3
  have hDH : D ≤ H := hDP.trans hPH
  have hDplane : IsNonabelianPlane 3 (Pbar : Subgroup (H ⧸ O)) ((D.subgroupOf H).map π) := by
    rw [hPbar]
    exact hext.isNonabelianPlane_map hprime hodd hD hPH O hO
  have hDn : (Pbar : Subgroup (H ⧸ O)) ≤
      normalizer (((D.subgroupOf H).map π : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
    rw [hPbar]
    have h1 : (P : Subgroup G).subgroupOf H ≤
        normalizer ((D.subgroupOf H : Subgroup H) : Set H) := by
      intro x hx
      rw [← Subgroup.subgroupOf_normalizer_eq hDH]
      exact hPD hx
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map π)
  have hDHp : IsPGroup 3 (D.subgroupOf H) := (P.isPGroup'.to_le hDP).comap_subtype
  have hDcard : Nat.card ((D.subgroupOf H).map π) = 3 ^ 3 := by
    rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hprime O hO hDHp,
      Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
    exact hext.card_eq_of_not_isMulCommutative hprime hodd hD
  have hEH : E ≤ H := hEP.trans hPH
  have hEHp : IsPGroup 3 (E.subgroupOf H) := (P.isPGroup'.to_le hEP).comap_subtype
  have hEbP : (E.subgroupOf H).map π ≤ (Pbar : Subgroup (H ⧸ O)) := by
    rw [hPbar]
    exact Subgroup.map_mono (fun x hx => hEP hx)
  have hEbe : IsElemAbelian 3 ((E.subgroupOf H).map π) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (CFSG.AGLEmbedding.isElemAbelian_subgroupOf hE H) π
  have hEbc : Nat.card ((E.subgroupOf H).map π) = 3 ^ 3 := by
    rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hprime O hO hEHp,
      Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv]
    exact hEc
  have he3 : CFSG.twoLocalOddRank (H ⧸ O) ≤ 3 := twoLocalOddRank_reduced_le_three hS hp hHtop
  have hgen := hK (H ⧸ O) hcat he3 hcore Pbar (π zH) ((D.subgroupOf H).map π) hrankPbar hzbord
    hzbcen hzbE hDplane hDn (mem_map_of_mem π (show zH ∈ D.subgroupOf H from hzD)) hDcard
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hext.obstruction.1).1
  have h3 : 3 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
    rw [inf_eq_left.mpr hPH, hP3]
  have hOM : O.map H.subtype ≤ M := pPrimeCoreIn_centralizer_le hS hp hext.obstruction.1 h3
  have hMY : ∀ Y : Subgroup G, Y ≤ (P : Subgroup G) → 2 ≤ CFSG.Open.pRank 3 Y →
      3 ≤ CFSG.Open.pRank 3 (Y ⊔ ((P : Subgroup G) ⊓ centralizer (Y : Set G))) →
        normalizer (Y : Set G) ≤ M := fun Y hYP h2 h3' =>
    (aschCore_normalizer_le 2 3 (P : Subgroup G) Y hYP h2 h3').trans hext.obstruction.1.2
  have hHM : H ≤ M := le_of_top_le_aschCore_quotient hPH O hO hOM hPM hMY Pbar hPbar hgen
  exact absurd hHM (hext.centralizer_not_le_of_mem_center hS hp hD hzZ hz1)

end CFSG.LocalAnalysis.RankThreeTheoremC
