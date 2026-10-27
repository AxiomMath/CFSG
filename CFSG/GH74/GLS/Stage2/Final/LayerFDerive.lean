module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalLib
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerTransport
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Final.LayerFD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem odd_index_oPrimeResidual (Q : Type*) [Group Q] [Finite Q] :
    Odd (oPrimeResidual 2 Q).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hP : (P : Subgroup Q) ≤ oPrimeResidual 2 Q := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : (oPrimeResidual 2 Q).index ∣ (P : Subgroup Q).index := Subgroup.index_dvd_of_le hP
  have hnd : ¬ 2 ∣ (P : Subgroup Q).index := P.not_dvd_index
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 => hnd (h2.trans hdvd)))

theorem perfect_le_oPrimeResidual {Q : Type*} [Group Q] [Finite Q] {K : Subgroup Q}
    (hK : Group.IsPerfect K) : K ≤ oPrimeResidual 2 Q := by
  have : (oPrimeResidual 2 Q).Normal := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 Q
  have hodd : Odd (Nat.card (Q ⧸ oPrimeResidual 2 Q)) := odd_index_oPrimeResidual Q
  have hsolv : Group.IsSolvable (Q ⧸ oPrimeResidual 2 Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have himg : K.map (QuotientGroup.mk' (oPrimeResidual 2 Q)) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Q))) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hK
    have : Group.IsPerfect ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Q))) :=
      Group.IsPerfect.map (QuotientGroup.mk' (oPrimeResidual 2 Q))
    exact Group.IsPerfect.not_isSolvable ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Q))) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg

theorem layer_le_oPrimeResidual (Q : Type*) [Group Q] [Finite Q] : layer Q ≤ oPrimeResidual 2 Q :=
  sSup_le fun _ hK => perfect_le_oPrimeResidual hK.1.1

theorem layer_map_subtype_oPrimeResidual (Q : Type*) [Group Q] [Finite Q] :
    (layer ↥(oPrimeResidual 2 Q)).map (oPrimeResidual 2 Q).subtype = layer Q := by
  have hN : (oPrimeResidual 2 Q).Normal := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 Q
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine CFSG.LocalCores.component_le_layer
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (L.equivMapOfInjective (oPrimeResidual 2 Q).subtype (oPrimeResidual 2 Q).subtype_injective) hL.1,
        hL.2.trans' hN.isSubnormal⟩
  · refine sSup_le fun K hK => ?_
    have hKY : K ≤ oPrimeResidual 2 Q := perfect_le_oPrimeResidual hK.1.1
    calc K = (K.subgroupOf (oPrimeResidual 2 Q)).map (oPrimeResidual 2 Q).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hKY).symm
      _ ≤ _ := Subgroup.map_mono (CFSG.LocalCores.component_le_layer
          (CFSG.LocalCores.component_overgroup hK hKY))

theorem map_layer_le_pPrimeCore (X : Type*) [Group X] [Finite X] :
    (layer X).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ layer (X ⧸ pPrimeCore 2 X) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hnot : ¬ J ≤ (QuotientGroup.mk' (pPrimeCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have hsolv : Group.IsSolvable ↥(pPrimeCore 2 X) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X)))
    have hsolvJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    have := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolvJ
  exact CFSG.LocalCores.component_le_layer
    ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩

section Bar

variable {G : Type} [Group G]

theorem barOf_sup {z : G} {A B : Subgroup G} (hA : A ≤ Cen z) (hB : B ≤ Cen z) :
    barOf z (A ⊔ B) = barOf z A ⊔ barOf z B := by
  unfold barOf
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem barOf_layerTimesSylow {z : G} {S : Subgroup G} (hSC : S ≤ Cen z) :
    barOf z (layerTimesSylow z S) =
      barOf z ((layer ↥(Cen z)).map (Cen z).subtype) ⊔ barOf z S :=
  barOf_sup (Subgroup.map_subtype_le _) hSC

theorem barOf_layer_le [Finite G] (z : G) :
    barOf z ((layer ↥(Cen z)).map (Cen z).subtype) ≤ layer (CentralizerBar z) := by
  have h : ((layer ↥(Cen z)).map (Cen z).subtype).subgroupOf (Cen z) = layer ↥(Cen z) :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  unfold barOf
  rw [h]
  exact map_layer_le_pPrimeCore ↥(Cen z)

end Bar

end CFSG.GH74.GLS.Stage2.Final.LayerFD

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem barOf_layerTimesSylow_eq {G Gs : Type} [Group G] [Finite G] [Group Gs] [Finite Gs]
    {z : G} {S : Subgroup G} {z' : Gs} {S' : Subgroup Gs}
    (hS : IsPGroup 2 ↥S) (hSC : S ≤ Cen z) (hSC' : S' ≤ Cen z')
    (hlift : barOf z ((CFSG.layer ↥(Cen z)).map (Cen z).subtype) = CFSG.layer (CentralizerBar z))
    (hB' : barOf z' (layerTimesSylow z' S') = oPrimeResidual 2 (CentralizerBar z'))
    (φ : ↥(oPrimeResidual 2 (CentralizerBar z)) ≃* ↥(oPrimeResidual 2 (CentralizerBar z')))
    (hφ : ∀ y : ↥(oPrimeResidual 2 (CentralizerBar z)),
      (y : CentralizerBar z) ∈ barOf z S ↔ (φ y : CentralizerBar z') ∈ barOf z' S') :
    barOf z (layerTimesSylow z S) = oPrimeResidual 2 (CentralizerBar z) := by
  have hX : barOf z (layerTimesSylow z S) = layer (CentralizerBar z) ⊔ barOf z S := by
    rw [LayerFD.barOf_layerTimesSylow hSC, hlift]
  apply le_antisymm
  · rw [hX]
    exact sup_le (LayerFD.layer_le_oPrimeResidual _) (barOf_le_oPrimeResidual hS)
  · intro y hy
    let y₀ : ↥(oPrimeResidual 2 (CentralizerBar z)) := ⟨y, hy⟩
    have hφy : (φ y₀ : CentralizerBar z') ∈ barOf z' (layerTimesSylow z' S') := by
      rw [hB']
      exact (φ y₀).2
    rw [LayerFD.barOf_layerTimesSylow hSC'] at hφy
    have hφy' : (φ y₀ : CentralizerBar z') ∈ layer (CentralizerBar z') ⊔ barOf z' S' :=
      sup_le_sup_right (LayerFD.barOf_layer_le z') _ hφy
    have : (layer (CentralizerBar z')).Normal := by
      have := CFSG.LocalCores.layer_characteristic (G := CentralizerBar z')
      infer_instance
    obtain ⟨a, ha', b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.1 hφy'
    have haY : a ∈ oPrimeResidual 2 (CentralizerBar z') := LayerFD.layer_le_oPrimeResidual _ ha'
    have hbY : b ∈ oPrimeResidual 2 (CentralizerBar z') := by
      have hb' : b = a⁻¹ * (φ y₀ : CentralizerBar z') := by
        rw [← hab]
        group
      rw [hb']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haY) (φ y₀).2
    let a₀ : ↥(oPrimeResidual 2 (CentralizerBar z')) := ⟨a, haY⟩
    let b₀ : ↥(oPrimeResidual 2 (CentralizerBar z')) := ⟨b, hbY⟩
    have hy₀eq : y₀ = φ.symm a₀ * φ.symm b₀ := by
      apply φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact Subtype.ext hab.symm
    have ha₀ : a₀ ∈ layer ↥(oPrimeResidual 2 (CentralizerBar z')) := by
      have h1 : a ∈ (layer ↥(oPrimeResidual 2 (CentralizerBar z'))).map
          (oPrimeResidual 2 (CentralizerBar z')).subtype := by
        rw [LayerFD.layer_map_subtype_oPrimeResidual]
        exact ha'
      obtain ⟨t, ht, hta⟩ := h1
      have : t = a₀ := Subtype.ext hta
      rw [← this]
      exact ht
    have hA : (φ.symm a₀ : CentralizerBar z) ∈ layer (CentralizerBar z) := by
      have h1 : φ.symm a₀ ∈ (layer ↥(oPrimeResidual 2 (CentralizerBar z'))).map φ.symm.toMonoidHom :=
        Subgroup.mem_map_of_mem φ.symm.toMonoidHom ha₀
      rw [ModelLT.layer_map_equiv φ.symm] at h1
      have h2 : ((φ.symm a₀ : ↥(oPrimeResidual 2 (CentralizerBar z))) : CentralizerBar z) ∈
          (layer ↥(oPrimeResidual 2 (CentralizerBar z))).map
            (oPrimeResidual 2 (CentralizerBar z)).subtype :=
        Subgroup.mem_map_of_mem _ h1
      rwa [LayerFD.layer_map_subtype_oPrimeResidual] at h2
    have hB : (φ.symm b₀ : CentralizerBar z) ∈ barOf z S := by
      rw [hφ (φ.symm b₀), MulEquiv.apply_symm_apply]
      exact hb
    have hyeq : y = (φ.symm a₀ : CentralizerBar z) * (φ.symm b₀ : CentralizerBar z) :=
      congrArg Subtype.val hy₀eq
    rw [hX, hyeq]
    exact Subgroup.mul_mem_sup hA hB

theorem layer_sup_barOf_eq_of_barOf_eq {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hSC : S ≤ Cen z)
    (hB : barOf z (layerTimesSylow z S) = oPrimeResidual 2 (CentralizerBar z)) :
    layer (CentralizerBar z) ⊔ barOf z S = oPrimeResidual 2 (CentralizerBar z) := by
  apply le_antisymm
  · exact sup_le (LayerFD.layer_le_oPrimeResidual _) (barOf_le_oPrimeResidual hS)
  · rw [← hB, LayerFD.barOf_layerTimesSylow hSC]
    exact sup_le_sup_right (LayerFD.barOf_layer_le z) _

end CFSG.GH74.GLS.Stage2.Final
