module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isU3_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (h : IsRankThreeU3 K') :
    IsRankThreeU3 K := by
  obtain ⟨q, hq1, hq2, hl⟩ := h
  exact ⟨q, hq1, hq2, isoLie_of_mulEquiv e.symm hl⟩

theorem r1sBar_normal_u3 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J) :
    (r1sBar x J).Normal := by
  have hn : (J.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.le_centralizer).mpr hJ.centralizer_le
  exact hn.map _ (QuotientGroup.mk'_surjective _)

theorem ker_r1sHom_u3 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J) :
    (r1sHom x hJ.le_centralizer).ker = (rankThreePrimeCore 3 J).subgroupOf J := by
  have hJC := hJ.le_centralizer
  have hn : (J.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hJ.centralizer_le
  have hcore : rankThreePrimeCore 3 J = ((J.subgroupOf (centralizer ({x} : Set G))) ⊓
      primeComplementCore (G := centralizer ({x} : Set G)) 3).map
        (centralizer ({x} : Set G)).subtype := by
    have h := rankThreePrimeCore_map_subtype (p := 3) (C := centralizer ({x} : Set G))
      (J.subgroupOf (centralizer ({x} : Set G)))
    rwa [Subgroup.map_subgroupOf_eq_of_le hJC] at h
  ext j
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hcore]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        (Subgroup.inclusion hJC j) = 1 := congrArg Subtype.val h
    exact ⟨Subgroup.inclusion hJC j, ⟨Subgroup.mem_subgroupOf.mpr j.2,
      (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩
  · rintro ⟨c, ⟨-, hcO⟩, hcj⟩
    have : c = Subgroup.inclusion hJC j := Subtype.ext hcj
    subst this
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hcO)

theorem r1sBar_isU3 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J) :
    IsRankThreeU3 ↥(r1sBar x J) := by
  obtain ⟨Q, _, ψ, hψ, hker, hQ⟩ := hJ.iso
  have hkerφ : (r1sHom x hJ.le_centralizer).ker = ψ.ker :=
    (ker_r1sHom_u3 hJ).trans hker.symm
  exact isU3_of_mulEquiv (((QuotientGroup.quotientKerEquivOfSurjective _
    (r1sHom_surjective x hJ.le_centralizer)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkerφ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)) hQ

theorem r1sBar_perfect_u3 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J) :
    Group.IsPerfect ↥(r1sBar x J) := by
  have := hJ.perfect
  exact Group.IsPerfect.ofSurjective (r1sHom_surjective x hJ.le_centralizer)

end CFSG.LocalAnalysis.RankThreeTheoremC
