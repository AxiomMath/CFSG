module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux
import CFSG.LocalAnalysis.AGLEmbedding.CoverCore

public section

namespace CFSG.AGLEmbedding

theorem coverAbelianSylowLemma : CoverAbelianSylowLemma := by
  intro K _ _ X _ π hπ hker hperf p hp hp2 hZ1 hZp hZc hD T
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨D, hn, hF, hN, hidx⟩ := hD
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (D.card_span hp)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q (T.mapSurjective hπ)
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  set D' := D.map (MulAut.conj g).toMonoidHom hinj with hD'
  have hspan : D'.span ≤ (T : Subgroup K).map π := by
    have h2 := congrArg (fun S : Sylow p X => (S : Subgroup X)) hg
    simp only [Sylow.coe_mapSurjective] at h2
    rw [hD', ModuleSpec.map_span, ← h2, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hQ
  have hle : D'.span.comap π ≤ (T : Subgroup K) := by
    calc D'.span.comap π ≤ ((T : Subgroup K).map π).comap π := Subgroup.comap_mono hspan
      _ = (T : Subgroup K) ⊔ π.ker := Subgroup.comap_map_eq _ _
      _ = (T : Subgroup K) := by rw [hker, sup_eq_left]; exact IsPGroup.le_sylow_of_normal hZp T
  have hidx' : ¬ p ∣ (D'.span.comap π).index := by
    rwa [Subgroup.index_comap_of_surjective _ hπ, hD', ModuleSpec.map_span,
      Subgroup.index_map_of_bijective (MulAut.conj g).bijective]
  have heq : D'.span.comap π = (T : Subgroup K) :=
    (((T.isPGroup'.to_le hle).toSylow hidx').3 T.isPGroup' hle).symm
  have hN' : D'.Nondeg := hN
  have hF' : D'.NoFun := hF
  have hn' : D'.n ≤ 4 := hn
  obtain ⟨hexp, hcardE⟩ := forall_pow_eq_one_and_card_le_of_cover hp hZ1 hZp hZc T hn'
    (by rw [← heq]; exact D'.card_comap π hp hπ hker)
    (by rw [← heq]; exact fun x hx y hy => D'.commutator_mem_center π hker hx hy)
    (by rw [← heq]; exact fun x hx y hy => D'.commutator_pow_eq_one π hker hx hy)
    (by rw [← heq]; exact D'.commute_or_mem_center_of_nondeg π hp hp2 hπ hker hZp hZc hN')
    (by rw [← heq]; exact D'.exists_pow_eq_pow_of_noFun π hp hp2 hπ hker hZp hZc hF')
  refine ⟨hexp, csSup_le' fun k hk => ?_⟩
  obtain ⟨E, hET, hE, hk⟩ := hk
  have h1 := hcardE E hET fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [hk] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1

end CFSG.AGLEmbedding
