module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ}

namespace D1MSideAt

variable {M S : Subgroup G}

theorem fixed_le_barM_normalizer_inf (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {L : Subgroup G} :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) :=
  fixed_le_barM_normalizer_inf_of_twoCore_le h.twoCore_M_le hp hp2 hzM hz hCz

theorem mem_normalizer_block_of_cube (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) {z : G}
    (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z)) (hz3 : z ^ 3 = 1)
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {L : Subgroup G}
    (hL : IsWeakSBlock M (S) L) : z ∈ Subgroup.normalizer (L : Set G) :=
  h.mem_normalizer_block_of_cube_of_inner hp hp2 h86 hzM hz hz3 hCz hL
    (h.blockInnerNormalizer h84 h86 hD2 hL)

end D1MSideAt

end CFSG.AGLEmbedding
