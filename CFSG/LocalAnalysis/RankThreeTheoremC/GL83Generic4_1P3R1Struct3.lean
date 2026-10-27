module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

abbrev r1sBar (x : G) (J : Subgroup G) : Subgroup (GenericReduced 3 x) :=
  (J.subgroupOf (centralizer ({x} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))

theorem r1s_reducedCentralizerOfJ_eq (x : G) (J : Subgroup G) :
    reducedCentralizerOfJ x J = centralizer ((r1sBar x J : Subgroup (GenericReduced 3 x)) :
      Set (GenericReduced 3 x)) :=
  rfl

theorem r1sBar_normal {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsM11Normal M x J) :
    (r1sBar x J).Normal := by
  have hn : (J.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.le_centralizer).mpr hJ.centralizer_le
  exact hn.map _ (QuotientGroup.mk'_surjective _)

@[expose] def r1sHom (x : G) {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G)) :
    ↥J →* ↥(r1sBar x J) :=
  ((QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)).comp
    (Subgroup.inclusion hJC)).codRestrict (r1sBar x J)
    fun j => ⟨Subgroup.inclusion hJC j, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩

omit [Finite G] in
theorem r1sHom_surjective (x : G) {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G)) :
    Function.Surjective (r1sHom x hJC) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨c, Subgroup.mem_subgroupOf.mp hc⟩, rfl⟩

theorem ker_r1sHom {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsM11Normal M x J) :
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

theorem r1sBar_nonempty_equiv {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsM11Normal M x J) :
    Nonempty (↥(r1sBar x J) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) := by
  obtain ⟨Q, _, ψ, hψ, hker, ⟨e⟩⟩ := hJ.iso
  have hkerφ : (r1sHom x hJ.le_centralizer).ker = ψ.ker := (ker_r1sHom hJ).trans hker.symm
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _
    (r1sHom_surjective x hJ.le_centralizer)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkerφ)).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).trans e)⟩

theorem r1sBar_perfect {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsM11Normal M x J) :
    Group.IsPerfect ↥(r1sBar x J) := by
  have := hJ.perfect
  exact Group.IsPerfect.ofSurjective (r1sHom_surjective x hJ.le_centralizer)

theorem r1sBar_sylow_facts {M : Subgroup G} {x : G} {J : Subgroup G}
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hJ : IsM11Normal M x J) (T : Sylow 3 (r1sBar x J)) :
    IsElemAbelian 3 (T : Subgroup (r1sBar x J)) ∧ Nat.card T = 3 ^ 2 ∧
      centralizer ((T : Subgroup (r1sBar x J)) : Set (r1sBar x J)) ≤ T := by
  obtain ⟨e⟩ := r1sBar_nonempty_equiv hJ
  exact ⟨(hKA _ ⟨e⟩ T).1, ((hKM _ ⟨e⟩).2 T).1, ((hKM _ ⟨e⟩).2 T).2.1⟩

theorem r1s_mem_of_mk_mem {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsM11Normal M x J)
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
