module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.TightEmbedding
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.EBarData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SU43Transport

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup

theorem Case3Core.exists_ebar_data {G : Type} [Group G] [Finite G] {z : G} {K E : Subgroup G}
    (h : Case3Core G z K) (hKE : K ≤ E) (hEz : E ≤ centralizer ({z} : Set G))
    (hE : CFSG.IsQuasisimple ↥E) (hne : K ≠ E) :
    ∃ (t : ↥E ⧸ center ↥E) (J : Subgroup (↥E ⧸ center ↥E)),
      orderOf t = 2 ∧ J ≤ centralizer ({t} : Set (↥E ⧸ center ↥E)) ∧
      (J.subgroupOf (centralizer ({t} : Set (↥E ⧸ center ↥E)))).IsSubnormal ∧ t ∈ J ∧
      CFSG.IsQuasisimple ↥J ∧ CFSG.ComponentClassification.HarrisLit.IsTwoQuasisimple ↥J ∧
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSU 4 3 1 ∧
      (∀ x ∈ center ↥J, orderOf x ≠ 4) ∧
      Nonempty (↥K ⧸ CFSG.Open.fusionZStar ↥K ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J) := by
  obtain ⟨u, hu, hu4, hu2z, hcomm⟩ := h.exists_generator
  have huK : u ∈ K := by
    rw [CFSG.Open.pCoreOf] at hu
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact x.2
  have htight : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    h.tight u hu hu4
  let e : ↥(K.subgroupOf E) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKE
  let u' : ↥E := ⟨u, hKE huK⟩
  have hK' : CFSG.IsQuasisimple ↥(K.subgroupOf E) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h.quasisimple
  have huK' : u' ∈ K.subgroupOf E := Subgroup.mem_subgroupOf.mpr huK
  have hcomm' : ∀ k ∈ K.subgroupOf E, k * u' = u' * k := by
    intro k hk
    apply Subtype.ext
    simpa using hcomm (k : G) (Subgroup.mem_subgroupOf.mp hk)
  have hKn' : ((K.subgroupOf E).subgroupOf
      (Subgroup.centralizer ({u'} : Set ↥E))).Normal := by
    have hKC : K.subgroupOf E ≤ Subgroup.centralizer ({u'} : Set ↥E) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simpa using hcomm (x : G) (Subgroup.mem_subgroupOf.mp hx)
    refine (Subgroup.normal_subgroupOf_iff hKC).mpr ?_
    intro x k hx hk
    rw [Subgroup.mem_subgroupOf]
    have hkC : (k : G) ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    have hmem : (k : G) * (x : G) * (k : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (htight hkC) (x : G)).mp hxK
    simpa using hmem
  have hu2' : u' * u' ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : G) * ((u' * u' : ↥E) : G) = ((u' * u' : ↥E) : G) * (g : G)
    have huu : ((u' * u' : ↥E) : G) = z := by
      rw [show ((u' * u' : ↥E) : G) = u * u from rfl, ← pow_two, hu2z]
    rw [huu]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEz g.2)
  have hu' : u' ∉ Subgroup.center ↥E := by
    intro huc
    have hNorm : (K.subgroupOf E).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hKE]
      intro y k hy hkE
      have hkC : k ∈ Subgroup.centralizer ({u} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp huc ⟨k, hkE⟩)
      exact (Subgroup.mem_normalizer_iff.mp (htight hkC) y).mp hy
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hNorm with htop | hcent
    · have hE_le_K : E ≤ K := Subgroup.subgroupOf_eq_top.mp htop
      exact hne (le_antisymm hKE hE_le_K)
    · have hcommK : ∀ a b : ↥K, a * b = b * a := by
        intro a b
        have ha : (e.symm a : ↥E) ∈ Subgroup.center ↥E := hcent (e.symm a).2
        have h1' : (e.symm b : ↥E) * (e.symm a : ↥E) = (e.symm a : ↥E) * (e.symm b : ↥E) :=
          Subgroup.mem_center_iff.mp ha (e.symm b)
        have h2 : e (e.symm b * e.symm a) = e (e.symm a * e.symm b) :=
          congrArg e (Subtype.ext h1')
        simpa using h2.symm
      haveI : IsMulCommutative ↥K := IsMulCommutative.of_comm hcommK
      haveI : Group.IsPerfect ↥K := h.quasisimple.1
      haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial h.quasisimple
      exact Group.IsPerfect.not_isMulCommutative ↥K inferInstance
  have htwo' : ∀ c ∈ K.subgroupOf E,
      (∀ k ∈ K.subgroupOf E, k * c = c * k) → IsPGroup 2 (Subgroup.zpowers c) →
        c ∈ Subgroup.zpowers u' := by
    intro c hcK hcc hc2
    have hcK' : (c : G) ∈ K := Subgroup.mem_subgroupOf.mp hcK
    have hcc' : ∀ k ∈ K, k * (c : G) = (c : G) * k := by
      intro k hk
      exact congrArg Subtype.val (hcc ⟨k, hKE hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
    have hc2' : IsPGroup 2 (Subgroup.zpowers (c : G)) := by
      have hmap : (Subgroup.zpowers c).map E.subtype = Subgroup.zpowers (c : G) := by
        rw [MonoidHom.map_zpowers]
        rfl
      have hiso : ↥(Subgroup.zpowers c) ≃* ↥(Subgroup.zpowers (c : G)) :=
        (Subgroup.equivMapOfInjective (Subgroup.zpowers c) E.subtype
          E.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
      exact hc2.of_equiv hiso
    have hzu : (c : G) ∈ Subgroup.zpowers u :=
      mem_zpowers_of_central_two h.isCyclic_twoCore h.card_twoCore hu hu4 hcK' hcc' hc2'
    have hcomap : (Subgroup.zpowers u).comap E.subtype = Subgroup.zpowers u' := by
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg E.subtype hn⟩
    rw [← hcomap]
    exact hzu
  have hB' : IsSU43 (↥(K.subgroupOf E) ⧸ CFSG.oddCore ↥(K.subgroupOf E)) :=
    isSU43_quotient_oddCore_of_mulEquiv e h.quotient
  obtain ⟨t, J, ht, hJcent, hJsub, htJ, hJq, hJ2q, hJlie, hJcenter, hJZ⟩ :=
    CFSG.OddStandard.HigherRank.G2Three.exists_ebar_data (E := ↥E) (K := K.subgroupOf E)
      (u := u') hK' huK' hcomm' hKn' hu2' hu' htwo' hB'
  refine ⟨t, J, ht, hJcent, hJsub, htJ, hJq, hJ2q, hJlie, hJcenter, ?_⟩
  obtain ⟨eZ⟩ := CFSG.ComponentClassification.GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    e.symm
  obtain ⟨eJ⟩ := hJZ
  exact ⟨eZ.trans eJ⟩

end CFSG.OddStandard.HigherRank.G2Three
