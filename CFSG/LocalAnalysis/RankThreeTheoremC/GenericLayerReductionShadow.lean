module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.AGLEmbedding.CentralizerTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

abbrev GenericReduced (p : ℕ) (x : G) : Type :=
  centralizer ({x} : Set G) ⧸ primeComplementCore (G := centralizer ({x} : Set G)) p

theorem exists_genericShadow (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x) :
    ∃ S : Sylow p (GenericReduced p x),
      (S : Subgroup (GenericReduced p x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
          (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) ∧
      GenericShadow p S
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩)
        (((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) := by
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hxP, hxL, hsyl, hrk⟩ := hx
  obtain ⟨hxM, hx1, hxp, h3, hCM⟩ := hxL
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  have hOcop : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hOM : O ≤ (C ⊓ M).subgroupOf C := by
    have h1 : GLBPrimeCore p C ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn p C).trans (pPrimeCoreIn_centralizer_le hS hp hM hrk.ge)
    rw [hO, ← glbPrimeCore_subgroupOf p C]
    exact glbPrimeCore_subgroupOf_le_inf h1
  obtain ⟨T, hT⟩ := hsyl
  have hTeq : (T : Subgroup C) = ((P : Subgroup G) ⊓ C).subgroupOf C := by
    rw [Subgroup.subgroupOf, ← hT, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  let Sbar : Sylow p (C ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O)
  have hSbar : (Sbar : Subgroup (C ⧸ O)) =
      (((P : Subgroup G) ⊓ C).subgroupOf C).map (QuotientGroup.mk' O) := by
    rw [Sylow.coe_mapSurjective, hTeq]
  refine ⟨Sbar, hSbar, ?_⟩
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hS.simple hS.nonab hx1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxCo : orderOf (⟨x, hxC⟩ : C) = p := by rw [Subgroup.orderOf_mk]; exact hxo
  refine ⟨hprime, hp5, primeComplementCore_quotient_eq_bot p,
    (catalogSimpleSections_of_isKProper hS.kProper C hCtop).quotient O, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hSbar, ← hTeq, pRank_map_mk_eq_pRank_map_subtype hprime O hOcop, hT, hrk]
  ·
    rw [mem_center_iff]
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.mp c.2))
  · exact orderOf_mk_of_coprime hprime O hOcop hxCo
  ·
    intro htop
    apply hCM
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' O) ((C ⊓ M).subgroupOf C)
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hcomap
    intro g hg
    have hmem : (⟨g, hg⟩ : C) ∈ (C ⊓ M).subgroupOf C := hcomap ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  ·
    intro Dbar hDS hD2
    rw [hSbar] at hDS
    obtain ⟨D, hDT, rfl⟩ : ∃ D ≤ ((P : Subgroup G) ⊓ C).subgroupOf C,
        D.map (QuotientGroup.mk' O) = Dbar := ⟨_, inf_le_right, map_comap_inf_eq _ hDS⟩
    have hTp : IsPGroup p (((P : Subgroup G) ⊓ C).subgroupOf C) :=
      (P.isPGroup'.to_le inf_le_left).comap_subtype
    have hDp : IsPGroup p D := hTp.to_le hDT
    have hrank : 2 ≤ CFSG.Open.pRank p (D.map C.subtype) := by
      rw [← pRank_map_mk_eq_pRank_map_subtype hprime O hOcop]
      exact hD2
    have hDG : D.map C.subtype ≤ (P : Subgroup G) := by
      refine (Subgroup.map_mono hDT).trans ?_
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
      exact inf_le_left
    have hN : normalizer ((D.map C.subtype : Subgroup G) : Set G) ≤ M :=
      normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM (hDp.map C.subtype) (hDG.trans hPM) hrank
    have hNH : normalizer (D : Set C) ≤ (C ⊓ M).subgroupOf C := fun n hn =>
      Subgroup.mem_subgroupOf.mpr
        ⟨n.property, hN (Subgroup.le_normalizer_map C.subtype ⟨n, hn, rfl⟩)⟩
    exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
      ((comap_normalizer_map_le_sup hprime O hOcop hDp).trans (sup_le hOM hNH))

end CFSG.LocalAnalysis.RankThreeTheoremC
