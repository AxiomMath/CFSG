module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbAdjBruhat

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Adj

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

theorem map_parJ_mul_eq_iff {S : Type*} [Group S] {π : K →* S} {M : ℕ}
    (h : BorelQuotient D n H π M) {j k : Fin D.rank} (hjk : j ≠ k) :
    (((parJ D H {j}).map π : Set S) * ((parJ D H {k}).map π : Set S) =
        ((parJ D H {j, k}).map π : Set S)) ↔ D.cartan j k = 0 := by
  constructor
  · intro heq
    have hmem : π (n k * n j) ∈ ((parJ D H {j, k}).map π : Set S) :=
      Subgroup.mem_map.2 ⟨n k * n j,
        CFSG.AGLEmbeddingD2.Tits.GN516.AdjBruhat.n_mul_n_mem h.ct j k, rfl⟩
    rw [← heq] at hmem
    exact CFSG.AGLEmbeddingD2.Tits.GN516.AdjBruhat.cartan_eq_zero_of_mul_mem h.ct h.extras hjk
      (CFSG.AGLEmbeddingD2.Tits.GN516.AdjBruhat.mem_mul_of_map_mem_mul h hmem)
  · intro hcart
    have hK := CFSG.AGLEmbeddingD2.Tits.GN516.AdjBruhat.parJ_mul_eq_of_cartan_eq_zero h.ct
      h.extras hjk hcart
    simp only [Subgroup.coe_map]
    rw [← Set.image_mul, hK]

end CFSG.AGLEmbeddingD2.Tits.GN516.Adj
