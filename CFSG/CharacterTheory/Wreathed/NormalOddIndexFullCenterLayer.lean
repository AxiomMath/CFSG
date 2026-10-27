module

public import CFSG.CharacterTheory.Wreathed.NormalOddIndexFullCenterLayerBasic
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public noncomputable section

namespace CFSG.Wreathed.NormalOddIndexFullCenterLayer
universe u v
variable {H : Type u} [Group H]

theorem normal_simple_isComponent (Q : Subgroup H) [Q.Normal] [IsSimpleGroup Q]
    (hnonab : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsComponent Q := by
  let : Group.IsPerfect Q :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top Q hnonab⟩
  have hc : Subgroup.center Q = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot Q hnonab
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨⟨inferInstance, e.isSimpleGroup, ?_⟩, (inferInstance : Q.Normal).isSubnormal⟩
  exact CFSG.ComponentClassification.Helpers.nonabelian_of_equiv e hnonab

theorem generalizedFitting_eq_simple [Finite H]
    (Q : Subgroup H) [Q.Normal] [IsSimpleGroup Q]
    (hnonab : ∃ a b : Q, a * b ≠ b * a)
    (hcentralizer : Subgroup.centralizer (Q : Set H) = ⊥) : CFSG.generalizedFitting H = Q :=
  CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot Q
    (normal_simple_isComponent Q hnonab) hcentralizer

theorem centralizer_comap_of_injective {G : Type v} [Group G]
    (i : G →* H) (hi : Function.Injective i) (P : Subgroup G) :
    (Subgroup.centralizer (P.map i : Set H)).comap i = Subgroup.centralizer (P : Set G) := by
  ext g
  constructor
  · intro hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro p hp
    apply hi
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp hg (i p) (Subgroup.mem_map_of_mem i hp)
  · intro hg
    apply Subgroup.mem_centralizer_iff.mpr
    rintro h ⟨p, hp, rfl⟩
    simpa only [map_mul] using congrArg i (Subgroup.mem_centralizer_iff.mp hg p hp)

theorem centralizer_eq_bot_of_injective {G : Type v} [Group G]
    (i : G →* H) (hi : Function.Injective i) (P : Subgroup G)
    (hc : Subgroup.centralizer (P.map i : Set H) = ⊥) :
    Subgroup.centralizer (P : Set G) = ⊥ := by
  rw [← centralizer_comap_of_injective i hi P, hc]
  change i.ker = ⊥
  exact (MonoidHom.ker_eq_bot_iff i).mpr hi

@[expose] def fullCenterInclusion (M D : Subgroup H)
    (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    D ⧸ Subgroup.center D →* H ⧸ Subgroup.center H :=
  (quotientInclusion D).comp
    (QuotientGroup.quotientMulEquivOfEq
      (center_subgroupOf_eq M D hMD hcentralizer).symm).toMonoidHom

theorem fullCenterInclusion_mk (M D : Subgroup H)
    (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) (d : D) :
    fullCenterInclusion M D hMD hcentralizer (QuotientGroup.mk' (Subgroup.center D) d) =
      QuotientGroup.mk' (Subgroup.center H) (d : H) := rfl

theorem fullCenterInclusion_injective (M D : Subgroup H)
    (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    Function.Injective (fullCenterInclusion M D hMD hcentralizer) :=
  (quotientInclusion_injective D).comp (MulEquiv.injective _)

theorem fullCenterInclusion_range (M D : Subgroup H)
    (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (fullCenterInclusion M D hMD hcentralizer).range =
      D.map (QuotientGroup.mk' (Subgroup.center H)) := by
  unfold fullCenterInclusion
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    Subgroup.map_top, quotientInclusion_range]

theorem localProjectiveImage_map (M D : Subgroup H)
    (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    ((M.subgroupOf D).map (QuotientGroup.mk' (Subgroup.center D))).map
      (fullCenterInclusion M D hMD hcentralizer) =
      M.map (QuotientGroup.mk' (Subgroup.center H)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨d, hd, rfl⟩, rfl⟩
    rw [fullCenterInclusion_mk]
    exact Subgroup.mem_map.mpr ⟨(d : H), hd, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    let d : D := ⟨m, hMD hm⟩
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (Subgroup.center D) d,
      Subgroup.mem_map.mpr ⟨d, hm, rfl⟩, ?_⟩
    exact fullCenterInclusion_mk M D hMD hcentralizer d

theorem ambient_generalizedFitting [Finite H] (M : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    CFSG.generalizedFitting (H ⧸ Subgroup.center H) =
      M.map (QuotientGroup.mk' (Subgroup.center H)) := by
  let : Group.IsPerfect M := hM.1
  let : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.1
  let Q := M.map (QuotientGroup.mk' (Subgroup.center H))
  let e := projectiveImageEquiv M hcentralizer
  let : IsSimpleGroup Q := e.symm.isSimpleGroup
  have hnonab : ∃ a b : Q, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv e.symm hM.2.2
  exact generalizedFitting_eq_simple Q hnonab (projectiveImage_centralizer M hcentralizer)

theorem local_generalizedFitting [Finite H] (M D : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    CFSG.generalizedFitting (D ⧸ Subgroup.center D) =
      (M.subgroupOf D).map (QuotientGroup.mk' (Subgroup.center D)) := by
  let P := (M.subgroupOf D).map (QuotientGroup.mk' (Subgroup.center D))
  let i := fullCenterInclusion M D hMD hcentralizer
  have hi : Function.Injective i := fullCenterInclusion_injective M D hMD hcentralizer
  have hmap : P.map i = M.map (QuotientGroup.mk' (Subgroup.center H)) :=
    localProjectiveImage_map M D hMD hcentralizer
  let : Group.IsPerfect M := hM.1
  let : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.1
  let e := (P.equivMapOfInjective i hi).trans
    ((MulEquiv.subgroupCongr hmap).trans (projectiveImageEquiv M hcentralizer).symm)
  let : IsSimpleGroup P := e.isSimpleGroup
  have hnonab : ∃ a b : P, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv e hM.2.2
  have hc : Subgroup.centralizer (P.map i : Set (H ⧸ Subgroup.center H)) = ⊥ := by
    rw [hmap]
    exact projectiveImage_centralizer M hcentralizer
  exact generalizedFitting_eq_simple P hnonab (centralizer_eq_bot_of_injective i hi P hc)

theorem generalizedFitting_map [Finite H] (M D : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (CFSG.generalizedFitting (D ⧸ Subgroup.center D)).map
      (fullCenterInclusion M D hMD hcentralizer) =
      CFSG.generalizedFitting (H ⧸ Subgroup.center H) := by
  rw [local_generalizedFitting M D hM hMD hcentralizer,
    ambient_generalizedFitting M hM hcentralizer,
    localProjectiveImage_map M D hMD hcentralizer]

@[expose] def layerInclusionEquiv [Finite H] (M D : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    CFSG.generalizedFitting (D ⧸ Subgroup.center D) ≃*
      CFSG.generalizedFitting (H ⧸ Subgroup.center H) :=
  ((CFSG.generalizedFitting (D ⧸ Subgroup.center D)).equivMapOfInjective
    (fullCenterInclusion M D hMD hcentralizer)
    (fullCenterInclusion_injective M D hMD hcentralizer)).trans
      (MulEquiv.subgroupCongr (generalizedFitting_map M D hM hMD hcentralizer))

theorem layerInclusionEquiv_coe [Finite H] (M D : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H)
    (a : CFSG.generalizedFitting (D ⧸ Subgroup.center D)) :
    (layerInclusionEquiv M D hM hMD hcentralizer a : H ⧸ Subgroup.center H) =
      fullCenterInclusion M D hMD hcentralizer (a : D ⧸ Subgroup.center D) := rfl

theorem layerInclusionEquiv_mk [Finite H] (M D : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H)
    (d : D) (hd : QuotientGroup.mk' (Subgroup.center D) d ∈
      CFSG.generalizedFitting (D ⧸ Subgroup.center D)) :
    (layerInclusionEquiv M D hM hMD hcentralizer
      (⟨QuotientGroup.mk' (Subgroup.center D) d, hd⟩ :
        CFSG.generalizedFitting (D ⧸ Subgroup.center D)) : H ⧸ Subgroup.center H) =
      QuotientGroup.mk' (Subgroup.center H) (d : H) := by
  rw [layerInclusionEquiv_coe]
  exact fullCenterInclusion_mk M D hMD hcentralizer d

theorem projectiveImage_simple (M : Subgroup H) (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    IsSimpleGroup (M.map (QuotientGroup.mk' (Subgroup.center H))) ∧
      ∃ a b : M.map (QuotientGroup.mk' (Subgroup.center H)), a * b ≠ b * a := by
  let : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.1
  let e := projectiveImageEquiv M hcentralizer
  exact ⟨e.symm.isSimpleGroup,
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv e.symm hM.2.2⟩

theorem ambient_layer_centralizer [Finite H] (M : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    Subgroup.centralizer (CFSG.generalizedFitting (H ⧸ Subgroup.center H) :
      Set (H ⧸ Subgroup.center H)) = ⊥ := by
  let : Group.IsPerfect M := hM.1
  rw [ambient_generalizedFitting M hM hcentralizer]
  exact projectiveImage_centralizer M hcentralizer

theorem local_layer_centralizer [Finite H] (M D : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    Subgroup.centralizer (CFSG.generalizedFitting (D ⧸ Subgroup.center D) :
      Set (D ⧸ Subgroup.center D)) = ⊥ := by
  let i := fullCenterInclusion M D hMD hcentralizer
  have hi := fullCenterInclusion_injective M D hMD hcentralizer
  apply centralizer_eq_bot_of_injective i hi
  rw [generalizedFitting_map M D hM hMD hcentralizer]
  exact ambient_layer_centralizer M hM hcentralizer

theorem normal_odd_index_subgroup_preserves_full_center_quasisimple_layer [Finite H]
    (M D : Subgroup H) [M.Normal] [D.Normal] (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (htwo : IsPGroup 2 (Subgroup.center H))
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H)
    (hodd : Odd D.index) :
    Subgroup.center H ⊔ M ≤ D ∧
      (Subgroup.center D).map D.subtype = Subgroup.center H ∧
      ∃ i : D ⧸ Subgroup.center D →* H ⧸ Subgroup.center H,
        Function.Injective i ∧ i.range.Normal ∧ Odd i.range.index ∧
        (∀ d : D, i (QuotientGroup.mk' (Subgroup.center D) d) =
          QuotientGroup.mk' (Subgroup.center H) (d : H)) ∧
        (∃ e : M ⧸ Subgroup.center M ≃*
          M.map (QuotientGroup.mk' (Subgroup.center H)),
          ∀ m : M, (e (QuotientGroup.mk' (Subgroup.center M) m) :
            H ⧸ Subgroup.center H) = QuotientGroup.mk' (Subgroup.center H) (m : H)) ∧
        IsSimpleGroup (M.map (QuotientGroup.mk' (Subgroup.center H))) ∧
        (∃ a b : M.map (QuotientGroup.mk' (Subgroup.center H)), a * b ≠ b * a) ∧
        CFSG.generalizedFitting (H ⧸ Subgroup.center H) =
          M.map (QuotientGroup.mk' (Subgroup.center H)) ∧
        CFSG.generalizedFitting (D ⧸ Subgroup.center D) =
          (M.subgroupOf D).map (QuotientGroup.mk' (Subgroup.center D)) ∧
        (CFSG.generalizedFitting (D ⧸ Subgroup.center D)).map i =
          CFSG.generalizedFitting (H ⧸ Subgroup.center H) ∧
        (∃ e : CFSG.generalizedFitting (D ⧸ Subgroup.center D) ≃*
          CFSG.generalizedFitting (H ⧸ Subgroup.center H),
          ∀ a : CFSG.generalizedFitting (D ⧸ Subgroup.center D),
            (e a : H ⧸ Subgroup.center H) = i (a : D ⧸ Subgroup.center D)) ∧
        Subgroup.centralizer (CFSG.generalizedFitting (H ⧸ Subgroup.center H) :
          Set (H ⧸ Subgroup.center H)) = ⊥ ∧
        Subgroup.centralizer (CFSG.generalizedFitting (D ⧸ Subgroup.center D) :
          Set (D ⧸ Subgroup.center D)) = ⊥ := by
  have hMD := quasisimple_le_normal_of_odd_index M D hM heven hodd
  have hAD := center_le_normal_of_odd_index D htwo hodd
  let i := fullCenterInclusion M D hMD hcentralizer
  have hi := fullCenterInclusion_injective M D hMD hcentralizer
  have hrange := fullCenterInclusion_range M D hMD hcentralizer
  have hnormal : i.range.Normal := by
    rw [hrange]
    infer_instance
  have hindex : Odd i.range.index := by
    rw [hrange]
    exact hodd.of_dvd_nat (Subgroup.index_map_dvd D (QuotientGroup.mk'_surjective _))
  have hsimple := projectiveImage_simple M hM hcentralizer
  exact ⟨sup_le hAD hMD, center_map_eq M D hMD hAD hcentralizer, i,
    hi, hnormal, hindex, fullCenterInclusion_mk M D hMD hcentralizer,
    ⟨projectiveImageEquiv M hcentralizer, projectiveImageEquiv_mk M hcentralizer⟩,
    hsimple.1, hsimple.2, ambient_generalizedFitting M hM hcentralizer,
    local_generalizedFitting M D hM hMD hcentralizer,
    generalizedFitting_map M D hM hMD hcentralizer,
    ⟨layerInclusionEquiv M D hM hMD hcentralizer,
      layerInclusionEquiv_coe M D hM hMD hcentralizer⟩,
    ambient_layer_centralizer M hM hcentralizer,
    local_layer_centralizer M D hM hMD hcentralizer⟩

end CFSG.Wreathed.NormalOddIndexFullCenterLayer
