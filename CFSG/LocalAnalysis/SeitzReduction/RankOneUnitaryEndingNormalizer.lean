module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingProduct
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStart

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem le_of_isPGroup_of_le_centralizer (h : U3Start G L f t T) {K : Subgroup G}
    (hK : IsPGroup 2 K) (hKC : K ≤ centralizer ({t} : Set G)) (hTK : T ≤ K) : K ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.sylow
  have hK' : IsPGroup 2 (K.subgroupOf (centralizer ({t} : Set G))) :=
    hK.comap_subtype (K := centralizer ({t} : Set G))
  have hle : (P : Subgroup _) ≤ K.subgroupOf (centralizer ({t} : Set G)) := by
    intro x hx
    rw [hP, mem_subgroupOf] at hx
    exact mem_subgroupOf.mpr (hTK hx)
  have heq := P.is_maximal' hK' hle
  intro k hk
  have hk' : (⟨k, hKC hk⟩ : centralizer ({t} : Set G)) ∈ K.subgroupOf _ := mem_subgroupOf.mpr hk
  rw [heq, hP] at hk'
  exact mem_subgroupOf.mp hk'

end U3Start

theorem mem_normalizer_map_conj_of_mem_normalizer {G : Type*} [Group G] {K : Subgroup G}
    {g y : G} (hy : g⁻¹ * y * g ∈ normalizer (K : Set G)) :
    y ∈ normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq', ← map_conj_mul_eq,
    show y * g = g * (g⁻¹ * y * g) by group, map_conj_mul_eq,
    mem_normalizer_iff_map_conj_eq'.mp hy]

end CFSG.SeitzReduction.RankOne
