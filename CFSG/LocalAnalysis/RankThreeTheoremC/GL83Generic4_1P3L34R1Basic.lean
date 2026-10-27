module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_xbar_facts (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) (J : Subgroup G) :
    QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ reducedCentralizerOfJ x J ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩) = 3 := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  refine ⟨?_, hsh.orderOf_eq⟩
  rw [reducedCentralizerOfJ, mem_centralizer_iff]
  intro h _
  exact (mem_center_iff.mp hsh.mem_center h)

theorem l34_x_not_mem_J (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) : x ∉ J := by
  intro hxJ
  obtain ⟨hD, hord⟩ := l34_xbar_facts hS hU0 hp hM hgen J
  have hmem : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
      ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ r1sBar x J :=
    ⟨⟨x, mem_centralizer_singleton_iff.mpr rfl⟩, mem_subgroupOf.mpr hxJ, rfl⟩
  have h1 := (l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ)
  have h2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
      ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ r1sBar x J ⊓ reducedCentralizerOfJ x J :=
    ⟨hmem, hD⟩
  rw [h1, mem_bot] at h2
  rw [h2, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem l34_mem_of_ker_of_mem_J (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three)
    {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J)
    (c : ↥(centralizer ({x} : Set G))) (hcJ : (c : G) ∈ J) (h1 : l34Hom x J c = 1) :
    c ∈ primeComplementCore (G := centralizer ({x} : Set G)) 3 := by
  set O := primeComplementCore (G := centralizer ({x} : Set G)) 3 with hO
  set D := reducedCentralizerOfJ x J with hD
  have hy : QuotientGroup.mk' O c ∈ r1sBar x J := ⟨c, mem_subgroupOf.mpr hcJ, rfl⟩
  have hyD : QuotientGroup.mk' O c ∈ D := by
    have h : QuotientGroup.mk' D.normalCore (QuotientGroup.mk' O c) = 1 := h1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
    exact normalCore_le D h
  have hy1 : QuotientGroup.mk' O c = 1 := by
    have h : QuotientGroup.mk' O c ∈ r1sBar x J ⊓ D := ⟨hy, hyD⟩
    rwa [l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ, mem_bot] at h
  rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
  exact hy1

end CFSG.LocalAnalysis.RankThreeTheoremC
