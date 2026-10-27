module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.RootSystem CFSG.AGLEmbedding.ParabHub
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts.ChevAut

variable {K : Type} [Field K]

section E6

variable [Finite K]


theorem borelQuotient_e6 [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* AdjointQuotient .E6 K) :
    BorelQuotient (e6Datum K) (e6Data_valid.nm K) (e6Data_valid.torus K)
      (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (e6Isogeny K))) (Nat.card K - 1) where
  ct := e6Datum_isCTGroupDatum K
  extras := e6Datum_steinbergExtras K
  pGroup := fun _ hγ => isPGroup_of_isParametrization
    (Φ := RootSystem.ofCartan (e6Datum K).isFiniteType (e6Datum K).divisible)
    (e6Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E6)) hγ
  surj := e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (e6Isogeny_surjective K))
  odd := odd_card_sub_one K
  torus_pow := fun i _ hg => torus_pow_card_sub_one e6Data_valid K i hg
  ker_central := fun z hz => by
    have hz1 : z ∈ (e6Isogeny K).ker := by
      have h1 : (QuotientGroup.mk' _) (e6Isogeny K z) = 1 :=
        e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h2
      exact h2
    exact e6Isogeny_ker_le_center K hz1
  ker_pow := fun z hz => by
    have hz1 : z ∈ (e6Isogeny K).ker := by
      have h1 : (QuotientGroup.mk' _) (e6Isogeny K z) = 1 :=
        e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h2
      exact h2
    exact center_pow_eq_one (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K)
      (e6Datum_bruhatExtras K) (fun i h hh => torus_pow_card_sub_one e6Data_valid K i hh) z
      (e6Isogeny_ker_le_center K hz1)

end E6

section E7

variable [Finite K]


theorem borelQuotient_e7 [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* AdjointQuotient .E7 K) :
    BorelQuotient (e7Datum K) (e7Data_valid.nm K) (e7Data_valid.torus K)
      (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (e7Isogeny K))) (Nat.card K - 1) where
  ct := e7Datum_isCTGroupDatum K
  extras := e7Datum_steinbergExtras K
  pGroup := fun _ hγ => isPGroup_of_isParametrization
    (Φ := RootSystem.ofCartan (e7Datum K).isFiniteType (e7Datum K).divisible)
    (e7Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E7)) hγ
  surj := e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (e7Isogeny_surjective K))
  odd := odd_card_sub_one K
  torus_pow := fun i _ hg => torus_pow_card_sub_one e7Data_valid K i hg
  ker_central := fun z hz => by
    have hz1 : z ∈ (e7Isogeny K).ker := by
      have h1 : (QuotientGroup.mk' _) (e7Isogeny K z) = 1 :=
        e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h2
      exact h2
    exact e7Isogeny_ker_le_center K hz1
  ker_pow := fun z hz => by
    have hz1 : z ∈ (e7Isogeny K).ker := by
      have h1 : (QuotientGroup.mk' _) (e7Isogeny K z) = 1 :=
        e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h2
      exact h2
    exact center_pow_eq_one (e7Datum_isCTGroupDatum K) (e7Datum_steinbergExtras K)
      (e7Datum_bruhatExtras K) (fun i h hh => torus_pow_card_sub_one e7Data_valid K i hh) z
      (e7Isogeny_ker_le_center K hz1)

end E7

section Nodes


theorem hasSL2Node_e6 (i : Fin (Tag.rank .E6)) : HasSL2Node (e6Datum K) i K := by
  obtain ⟨φ, hφ, hx, hy⟩ := e6Data_valid.exists_sl2Hom K i
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact e6Data_valid.xm_mem_rootGroup K _ _
  · rw [hy c]
    exact e6Data_valid.xm_mem_rootGroup K _ _

theorem hasSL2Node_e7 (i : Fin (Tag.rank .E7)) : HasSL2Node (e7Datum K) i K := by
  obtain ⟨φ, hφ, hx, hy⟩ := e7Data_valid.exists_sl2Hom K i
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact e7Data_valid.xm_mem_rootGroup K _ _
  · rw [hy c]
    exact e7Data_valid.xm_mem_rootGroup K _ _

end Nodes

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
