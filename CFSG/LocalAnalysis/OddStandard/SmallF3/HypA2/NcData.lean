module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

structure NcData (G : Type) [Group G] (y z : G) (K T N : Subgroup G) (q₀ : ℕ) : Prop where
  oy : orderOf y = 2
  oz : orderOf z = 2
  hK : Omega.IsComponentIn K (centralizer ({y} : Set G))
  hzK : z ∈ K
  hzc : z ∉ (center ↥K).map K.subtype
  hT : HarrisLit.IsTwoComponentIn T (K ⊓ centralizer ({z} : Set G))
  hNT : N ≤ T
  hzN : z ∈ N
  hqodd : Odd q₀
  hq5 : 5 ≤ q₀
  hSL : HarrisLit.IsSLTwoOver q₀ ↥N
  hTypU : TypU ↥T

private theorem map_subtype_centralizer_singleton {M : Type*} [Group M] (Γ : Subgroup M)
    (z : Γ) :
    (Subgroup.centralizer {z}).map Γ.subtype = Γ ⊓ Subgroup.centralizer {(z : M)} := by
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hw))⟩
  · rintro ⟨hyΓ, hy⟩
    exact ⟨⟨y, hyΓ⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy)), rfl⟩

private theorem isTwoComponentIn_map_of_injective {G H : Type*} [Group G] [Group H]
    (ι : G →* H) (hι : Function.Injective ι) {J A : Subgroup G}
    (h : HarrisLit.IsTwoComponentIn J A) :
    HarrisLit.IsTwoComponentIn (J.map ι) (A.map ι) := by
  refine ⟨Subgroup.map_mono h.1, ?_, HarrisLit.isTwoQuasisimple_of_mulEquiv
    (J.equivMapOfInjective ι hι) h.2.2⟩
  let eA : ↥A ≃* ↥(A.map ι) := A.equivMapOfInjective ι hι
  have hmap : (J.subgroupOf A).map eA.toMonoidHom = (J.map ι).subgroupOf (A.map ι) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, h.1 hx⟩, hx, Subtype.ext hxy⟩
  rw [← hmap]
  exact h.2.1.map eA.surjective

theorem exists_ncData_of_noncentralDatum {G : Type} [Group G] [Finite G] {y : G}
    {K : Subgroup G} (hy : orderOf y = 2) (hK : Omega.IsComponentIn K (centralizer ({y} : Set G)))
    (h : NoncentralDatum ↥K) :
    ∃ (z : G) (T N : Subgroup G) (q₀ : ℕ), NcData G y z K T N q₀ := by
  obtain ⟨q₀, T, N, z, hqodd, hq5, hz2, hzcK, hzN, hNT, hTz, hTc, hSL, hTU⟩ := h
  have hz2' : orderOf ((z : ↥K) : G) = 2 := by rw [Subgroup.orderOf_coe, hz2]
  have hzc' : ((z : ↥K) : G) ∉ (Subgroup.center ↥K).map K.subtype := by
    intro hmem
    obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hmem
    exact hzcK (K.subtype_injective hceq ▸ hc)
  have hT : HarrisLit.IsTwoComponentIn (T.map K.subtype)
      (K ⊓ Subgroup.centralizer ({((z : ↥K) : G)} : Set G)) := by
    have hTA : HarrisLit.IsTwoComponentIn T (Subgroup.centralizer ({z} : Set ↥K)) :=
      (HarrisLit.isTwoComponentIn_iff hTz).mpr hTc
    have h1 := isTwoComponentIn_map_of_injective K.subtype K.subtype_injective hTA
    rwa [map_subtype_centralizer_singleton K z] at h1
  have hSL' : HarrisLit.IsSLTwoOver q₀ ↥(N.map K.subtype) :=
    isSLTwoOver_of_mulEquiv (N.equivMapOfInjective K.subtype K.subtype_injective) hSL
  have hTypU' : TypU ↥(T.map K.subtype) :=
    coreInvariant_typU ↥T ↥(T.map K.subtype)
      ⟨QuotientGroup.congr _ _ (T.equivMapOfInjective K.subtype K.subtype_injective)
        (CFSG.pPrimeCore_map_iso 2
          (T.equivMapOfInjective K.subtype K.subtype_injective))⟩ hTU
  refine ⟨(z : G), T.map K.subtype, N.map K.subtype, q₀, ?_⟩
  exact ⟨hy, hz2', hK, z.2, hzc', hT, Subgroup.map_mono hNT,
    Subgroup.mem_map_of_mem K.subtype hzN, hqodd, hq5, hSL', hTypU'⟩

end CFSG.OddStandard.SmallF3.HypA2
