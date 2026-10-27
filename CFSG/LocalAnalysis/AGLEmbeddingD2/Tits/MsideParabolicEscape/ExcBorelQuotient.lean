module

public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabStated

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.RootSystem
  CFSG.AGLEmbedding.ParabHub

variable {K : Type} [Field K] [Finite K]

theorem f4_torus_pow_eq_one (i : Fin (Tag.rank .F4)) {g : adjointGroup .F4 K}
    (hg : g ∈ torus (τ := .F4) K i) : g ^ (Nat.card K - 1) = 1 := by
  obtain ⟨t, rfl⟩ := hg
  rw [← map_pow, unit_pow_card_sub_one, map_one]

theorem e8_torus_pow_eq_one (i : Fin (Tag.rank .E8)) {g : adjointGroup .E8 K}
    (hg : g ∈ torus (τ := .E8) K i) : g ^ (Nat.card K - 1) = 1 := by
  obtain ⟨t, rfl⟩ := hg
  rw [← map_pow, unit_pow_card_sub_one, map_one]



theorem borelQuotient_f4 [CharP K 2] {Y : Type} [Group Y] (e : Y ≃* AdjointQuotient .F4 K) :
    BorelQuotient (f4Datum K) (CFSG.LieType.Chevalley.weylElement .F4 K) (torus (τ := .F4) K)
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)) (Nat.card K - 1) where
  ct := f4_isCTGroupDatum K
  extras := f4_steinbergExtras K
  pGroup := fun _ hγ => isPGroup_of_isParametrization (f4_isParametrization K) hγ
  surj := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  odd := odd_card_sub_one K
  torus_pow := fun i _ hg => f4_torus_pow_eq_one i hg
  ker_central := fun z hz =>
    (QuotientGroup.eq_one_iff z).1
      (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
  ker_pow := fun z hz => by
    have hc : z ∈ Subgroup.center ↥(adjointGroup .F4 K) :=
      (QuotientGroup.eq_one_iff z).1
        (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    rw [hc, one_pow]

theorem borelQuotient_e8 [CharP K 2] {Y : Type} [Group Y] (e : Y ≃* AdjointQuotient .E8 K) :
    BorelQuotient (e8Datum K) (CFSG.LieType.Chevalley.weylElement .E8 K) (torus (τ := .E8) K)
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)) (Nat.card K - 1) where
  ct := e8_isCTGroupDatum K
  extras := e8_steinbergExtras K
  pGroup := fun _ hγ => isPGroup_of_isParametrization (e8_isParametrization K) hγ
  surj := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  odd := odd_card_sub_one K
  torus_pow := fun i _ hg => e8_torus_pow_eq_one i hg
  ker_central := fun z hz =>
    (QuotientGroup.eq_one_iff z).1
      (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
  ker_pow := fun z hz => by
    have hc : z ∈ Subgroup.center ↥(adjointGroup .E8 K) :=
      (QuotientGroup.eq_one_iff z).1
        (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    rw [hc, one_pow]

omit [Finite K]
  in
theorem hasSL2Node_f4 (i : Fin (Tag.rank .F4)) : HasSL2Node (f4Datum K) i K := by
  obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom_xPar (K := K)
    (exists_sl2_hom (rootOperatorFamily .F4) (neighbour_F4 i).choose_spec.1)
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact xPar_mem (isRoot_single _ i) c
  · rw [hy c]
    exact xPar_mem (isRoot_neg_single _ i) c

omit [Finite K]
  in
theorem hasSL2Node_e8 (i : Fin (Tag.rank .E8)) : HasSL2Node (e8Datum K) i K := by
  obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom_xPar (K := K)
    (exists_sl2_hom (rootOperatorFamily .E8) (neighbour_E8 i).choose_spec.1)
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact xPar_mem (isRoot_single _ i) c
  · rw [hy c]
    exact xPar_mem (isRoot_neg_single _ i) c

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
