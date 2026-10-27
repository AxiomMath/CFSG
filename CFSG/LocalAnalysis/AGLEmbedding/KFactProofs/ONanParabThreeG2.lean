module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabStated
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.RootSystem

section G2

variable {K : Type} [Field K] [Finite K]

theorem g2_torus_pow_eq_one (i : Fin (Tag.rank .G2)) {g : adjointGroup .G2 K}
    (hg : g ∈ torus (τ := .G2) K i) : g ^ (Nat.card K - 1) = 1 := by
  obtain ⟨t, rfl⟩ := hg
  rw [← map_pow, unit_pow_card_sub_one, map_one]

theorem borelQuotient_g2 [CharP K 2] {Y : Type} [Group Y] (e : Y ≃* AdjointQuotient .G2 K) :
    BorelQuotient (g2Datum K) (CFSG.LieType.Chevalley.weylElement .G2 K) (torus (τ := .G2) K)
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)) (Nat.card K - 1) where
  ct := g2_isCTGroupDatum K
  extras := g2_steinbergExtras K
  pGroup := fun _ hγ => isPGroup_of_isParametrization
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := K)
      (RootSystem.ofCartan (g2Datum K).isFiniteType (g2Datum K).divisible)
      (adjDatum_roots (rootOperatorFamily .G2) K)) hγ
  surj := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  odd := odd_card_sub_one K
  torus_pow := fun i _ hg => g2_torus_pow_eq_one i hg
  ker_central := fun z hz =>
    (QuotientGroup.eq_one_iff z).1
      (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
  ker_pow := fun z hz => by
    have hc : z ∈ Subgroup.center ↥(adjointGroup .G2 K) :=
      (QuotientGroup.eq_one_iff z).1
        (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    rw [hc, one_pow]

omit [Finite K] in
theorem hasSL2Node_g2 (i : Fin (Tag.rank .G2)) : HasSL2Node (g2Datum K) i K := by
  obtain ⟨φ, hφ, hx, hy⟩ := g2_exists_sl2_hom (K := K) i
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c, ← xPar_simple]
    exact xPar_mem (isRoot_single _ i) c
  · rw [hy c, ← xPar_neg_simple]
    exact xPar_mem (isRoot_neg_single _ i) c

theorem threeDvd_g2 [CharP K 2] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient .G2 K)
    (T : Sylow 2 Y) (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J :=
  (borelQuotient_g2 e).three_dvd_card (fun i => (hasSL2Node_g2 i).hasOrderThree) T J hNJ hJ

end G2

end CFSG.AGLEmbedding.ParabHub
