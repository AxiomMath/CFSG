module


public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality

open CFSG.Open

variable {G : Type} [Group G]

theorem map_layer (e : MulAut G) (H : Subgroup G) :
    (rankThreeLayer H).map e.toMonoidHom = rankThreeLayer (H.map e.toMonoidHom) := by
  have quasisimple_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
      (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
    obtain ⟨hp, hs⟩ := h
    have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
    refine ⟨?_, ?_⟩
    · have := congrArg (Subgroup.map (e : A →* B)) hp
      unfold commutator at this
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective] at this
      simpa [commutator] using this
    · exact (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup
  have subnormal_map (e : MulAut G) {L K : Subgroup G} (h : IsSubnormal L K) :
      IsSubnormal (L.map e.toMonoidHom) (K.map e.toMonoidHom) := by
    induction h with
    | refl H => exact IsSubnormal.refl _
    | @step H M K hHM hn _ ih =>
      refine IsSubnormal.step (Subgroup.map_mono hHM) ?_ ih
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hHM),
        ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hn)
  have component_map (e : MulAut G) {L K : Subgroup G} (h : IsComponentOf L K) :
      IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
    ⟨Subgroup.map_mono h.1, subnormal_map e h.2.1,
      quasisimple_of_equiv (L.equivMapOfInjective e.toMonoidHom e.injective) h.2.2⟩
  have map_layer_le (e : MulAut G) (H : Subgroup G) :
      (rankThreeLayer H).map e.toMonoidHom ≤ rankThreeLayer (H.map e.toMonoidHom) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (component_map e hL)
  refine le_antisymm (map_layer_le e H) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_layer_le e.symm (H.map e.toMonoidHom))
  have h1 : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [h1, Subgroup.map_map] at h
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
  rwa [this, Subgroup.map_id] at h

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality
