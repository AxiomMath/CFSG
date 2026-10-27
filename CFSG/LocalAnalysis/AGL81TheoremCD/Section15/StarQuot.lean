module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZDefs
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GH74.Constrained

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}

noncomputable def starImgMulEquiv (hp : p.Prime) {B : Subgroup G} (hBH : B ≤ H)
    (hB : IsPGroup p B) : B ≃* starImg p H B := by
  classical
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hB' : IsPGroup p (B.comap H.subtype) := hB.comap_subtype (K := H)
  have hcop : p.Coprime (Nat.card O) := by
    simpa [O] using primeComplementCore_coprime (G := ↥H) p
  have hinj : Function.Injective (π.domRestrict (B.comap H.subtype)) := by
    intro x y hxy
    refine Subtype.ext (CFSG.LocalAnalysis.RankFourTheoremC.injOn_mk_of_isPGroup_coprime
      (H := ↥H) (N := O) hp hcop hB' x.2 y.2 ?_)
    exact hxy
  have hrange : (π.domRestrict (B.comap H.subtype)).range = starImg p H B := by
    rw [MonoidHom.domRestrict_range]
    rfl
  exact (Subgroup.subgroupOfEquivOfLe hBH).symm.trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))

theorem isElemAbelian_starImg_iff (hp : p.Prime) {B : Subgroup G} (hBH : B ≤ H)
    (hB : IsPGroup p B) :
    IsElemAbelian p (starImg p H B) ↔ IsElemAbelian p B := by
  rw [isElemAbelian_iff_isElementaryAbelian, isElemAbelian_iff_isElementaryAbelian]
  constructor
  · intro h
    exact CFSG.IsElementaryAbelian.of_mulEquiv (starImgMulEquiv hp hBH hB).symm h
  · intro h
    exact CFSG.IsElementaryAbelian.of_mulEquiv (starImgMulEquiv hp hBH hB) h

theorem isCyclic_center_starImg_iff (hp : p.Prime) {B : Subgroup G} (hBH : B ≤ H)
    (hB : IsPGroup p B) :
    IsCyclic ↥(Subgroup.center ↥(starImg p H B)) ↔
      IsCyclic ↥(Subgroup.center ↥B) :=
  (MulEquiv.isCyclic (Subgroup.centerCongr (starImgMulEquiv hp hBH hB))).symm

theorem isSylowOf_starImg_top (hp : p.Prime) {B : Subgroup G}
    (hB : CFSG.ABGLocalTools.IsSylowOf p B H) :
    CFSG.ABGLocalTools.IsSylowOf p (starImg p H B) ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := hB
  let π : ↥H →* StarGroup p H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let Q' : Sylow p (StarGroup p H) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  refine ⟨Q'.subtype le_top, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top]
  have hQH : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [Sylow.coe_mapSurjective]
  calc (Q : Subgroup ↥H).map π
      = ((((Q : Subgroup ↥H).map H.subtype).subgroupOf H).map π) := by rw [hQH]
    _ = (B.subgroupOf H).map π := by rw [hQ]
    _ = starImg p H B := rfl

theorem starImg_normal {A : Subgroup G} (hA : (A.subgroupOf H).Normal) :
    (starImg p H A).Normal := by
  simpa [starImg] using
    hA.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
      (QuotientGroup.mk'_surjective _)

private theorem starImg_map_subtype (p : ℕ) (A : Subgroup ↥H) :
    starImg p H (A.map H.subtype) =
      A.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
  simp only [starImg, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

theorem starImg_normalizer_eq (hp : p.Prime) {D : Subgroup G} (hDH : D ≤ H)
    (hD : IsPGroup p D) :
    Subgroup.normalizer (starImg p H D : Set (StarGroup p H)) =
      starImg p H (Subgroup.normalizer (D : Set G) ⊓ H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hD' : IsPGroup p (D.subgroupOf H) := hD.comap_subtype (K := H)
  have hcop : p.Coprime (Nat.card O) := by
    simpa [O] using primeComplementCore_coprime (G := ↥H) p
  have h := CFSG.LocalAnalysis.RankFourTheoremC.normalizer_map_mk
    (H := ↥H) (N := O) hp hcop (S := D.subgroupOf H) hD'
  have hleft : (D.subgroupOf H).map π = starImg p H D := rfl
  rw [hleft] at h
  rw [h]
  rw [← starImg_map_subtype p
    (Subgroup.normalizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H))]
  rw [← Subgroup.subgroupOf_normalizer_eq hDH]
  rw [← Subgroup.inf_subgroupOf_right]
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]

theorem rankThreeGamma_starImg_le (hp : p.Prime) {k : ℕ} {B M : Subgroup G}
    (hBH : B ≤ H) (hB : IsPGroup p B)
    (hM : ∀ D : Subgroup G, D ≤ B → k ≤ CFSG.Open.pRank p D →
      Subgroup.normalizer (D : Set G) ⊓ H ≤ M) :
    CFSG.Open.rankThreeGamma k p (starImg p H B) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  let π : ↥H →* StarGroup p H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let B' : Subgroup ↥H := B.subgroupOf H
  unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQB, hkQ, rfl⟩
  have hQB' : Q ≤ B'.map π := hQB
  let D' : Subgroup ↥H := Q.comap π ⊓ B'
  have hD'map : D'.map π = Q := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hd).1
    · intro q hq
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp (hQB' hq)
      exact Subgroup.mem_map.mpr ⟨b, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_comap.mpr hq, hb⟩, rfl⟩
  let D : Subgroup G := D'.map H.subtype
  have hDH : D ≤ H := Subgroup.map_subtype_le D'
  have hDB : D ≤ B := by
    rintro _ ⟨d, hd, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hd).2
  have hDp : IsPGroup p D := hB.to_le hDB
  have hstarD : starImg p H D = Q := by
    have hsub : D.subgroupOf H = D' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective D'
    rw [starImg, hsub, hD'map]
  have hkD : k ≤ CFSG.Open.pRank p D := by
    have h := CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype
      (G := G) (H := H) hp (primeComplementCore (G := ↥H) p)
      (primeComplementCore_coprime (G := ↥H) p) D'
    rw [show D'.map π = Q from hD'map, show D'.map H.subtype = D from rfl] at h
    rw [← h]
    exact hkQ
  have hND : Subgroup.normalizer (D : Set G) ⊓ H ≤ M := hM D hDB hkD
  calc Subgroup.normalizer (Q : Set (StarGroup p H))
      = Subgroup.normalizer (starImg p H D : Set (StarGroup p H)) := by rw [hstarD]
    _ = starImg p H (Subgroup.normalizer (D : Set G) ⊓ H) :=
        starImg_normalizer_eq hp hDH hDp
    _ ≤ starImg p H M := Subgroup.map_mono (Subgroup.comap_mono hND)

theorem pRank_starImg_eq_pRank_inf (hp : p.Prime) (M : Subgroup G) :
    CFSG.Open.pRank p (starImg p H M) = CFSG.Open.pRank p (H ⊓ M) := by
  have h := CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype
    (G := G) (H := H) hp (primeComplementCore (G := ↥H) p)
    (primeComplementCore_coprime (G := ↥H) p) (M.subgroupOf H)
  simpa [starImg, Subgroup.subgroupOf_map_subtype, inf_comm] using h

theorem pPrimeCore_starGroup (hp : p.Prime) :
    CFSG.pPrimeCore p (StarGroup p H) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  change CFSG.pPrimeCore p (↥H ⧸ CFSG.pPrimeCore p ↥H) = ⊥
  exact CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot (↥H) p

theorem catalogSimpleSections_starGroup
    (h : CFSG.AGLEmbedding.CatalogSimpleSections ↥H) :
    CFSG.AGLEmbedding.CatalogSimpleSections (StarGroup p H) := by
  have hcore : CFSG.pPrimeCore p ↥H = primeComplementCore (G := ↥H) p := by
    unfold CFSG.pPrimeCore primeComplementCore
    rfl
  have h' : CFSG.AGLEmbedding.CatalogSimpleSections (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
    h.quotient (CFSG.pPrimeCore p ↥H)
  let e := QuotientGroup.quotientMulEquivOfEq hcore
  simpa [StarGroup] using h'.of_surjective e.toMonoidHom e.surjective

theorem starImg_eq_barInf (p : ℕ) (M H : Subgroup G) :
    starImg p H M = barInf p M H := by
  unfold starImg barInf CFSG.pPrimeCore primeComplementCore
  rw [Subgroup.inf_subgroupOf_left]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
