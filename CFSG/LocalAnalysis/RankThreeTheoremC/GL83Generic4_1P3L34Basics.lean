module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isL34_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (h : IsRankThreeL34 K') :
    IsRankThreeL34 K := by
  obtain ⟨q, hq1, hq2, hl⟩ := h
  exact ⟨q, hq1, hq2, isoLie_of_mulEquiv e.symm hl⟩

theorem r1sBar_normal_l34 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    (r1sBar x J).Normal := by
  have hn : (J.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.le_centralizer).mpr hJ.centralizer_le
  exact hn.map _ (QuotientGroup.mk'_surjective _)

theorem ker_r1sHom_l34 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
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

theorem r1sBar_isL34 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsRankThreeL34 ↥(r1sBar x J) := by
  obtain ⟨Q, _, ψ, hψ, hker, hQ⟩ := hJ.iso
  have hkerφ : (r1sHom x hJ.le_centralizer).ker = ψ.ker :=
    (ker_r1sHom_l34 hJ).trans hker.symm
  exact isL34_of_mulEquiv (((QuotientGroup.quotientKerEquivOfSurjective _
    (r1sHom_surjective x hJ.le_centralizer)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkerφ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)) hQ

theorem r1sBar_perfect_l34 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    Group.IsPerfect ↥(r1sBar x J) := by
  have := hJ.perfect
  exact Group.IsPerfect.ofSurjective (r1sHom_surjective x hJ.le_centralizer)

theorem r1sBar_sylow_facts_l34 {M : Subgroup G} {x : G} {J : Subgroup G}
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hJ : IsL34Normal M x J)
    (T : Sylow 3 (r1sBar x J)) :
    IsElemAbelian 3 (T : Subgroup (r1sBar x J)) ∧ Nat.card T = 3 ^ 2 ∧
      centralizer ((T : Subgroup (r1sBar x J)) : Set (r1sBar x J)) ≤ T :=
  ⟨(hK1 _ (r1sBar_isL34 hJ) T).1, (hK2 _ (r1sBar_isL34 hJ) T).1,
    (hK2 _ (r1sBar_isL34 hJ) T).2.1⟩

theorem r1s_mem_of_mk_mem_l34 {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J)
    {u : G} (hu : u ∈ centralizer ({x} : Set G)) (hu3 : u ^ 3 = 1)
    (h : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) ⟨u, hu⟩ ∈
      r1sBar x J) : u ∈ J := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hn : (J.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.le_centralizer).mpr hJ.centralizer_le
  obtain ⟨j, hj, hjπ⟩ := h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hjπ
  have ho : j⁻¹ * ⟨u, hu⟩ ∈ O := QuotientGroup.eq.mp hjπ
  set q : C →* C ⧸ J.subgroupOf C := QuotientGroup.mk' (J.subgroupOf C) with hq
  have hqj : q j = 1 := (QuotientGroup.eq_one_iff _).mpr hj
  have hqu : q ⟨u, hu⟩ = q (j⁻¹ * ⟨u, hu⟩) := by
    have : (⟨u, hu⟩ : C) = j * (j⁻¹ * ⟨u, hu⟩) := by group
    conv_lhs => rw [this]
    rw [map_mul, hqj, one_mul]
  have h1 : orderOf (q ⟨u, hu⟩) ∣ 3 :=
    (orderOf_map_dvd q _).trans (orderOf_dvd_of_pow_eq_one (Subtype.ext hu3))
  have h2 : orderOf (q ⟨u, hu⟩) ∣ Nat.card O := by
    rw [hqu]
    exact (orderOf_map_dvd q _).trans (Subgroup.orderOf_dvd_natCard O ho)
  have h3 : orderOf (q ⟨u, hu⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (primeComplementCore_coprime 3) h1 h2
  have h4 : q ⟨u, hu⟩ = 1 := orderOf_eq_one_iff.mp h3
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h4)

end CFSG.LocalAnalysis.RankThreeTheoremC
