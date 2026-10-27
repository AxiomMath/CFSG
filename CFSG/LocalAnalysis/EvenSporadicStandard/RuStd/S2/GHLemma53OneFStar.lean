module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUOut
public import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

theorem generalizedFitting_eq_sup_of_isComponent {X : Type*} [Group X] [Finite X]
    {A B : Subgroup X} (hA : CFSG.IsComponent A) (hB : CFSG.IsComponent B)
    (hC : centralizer ((A ⊔ B : Subgroup X) : Set X) = ⊥) :
    CFSG.generalizedFitting X = A ⊔ B := by
  have hlayer : CFSG.layer X = A ⊔ B := by
    apply le_antisymm
    · rw [CFSG.layer.eq_sSup]
      apply sSup_le
      intro K hK
      rcases CFSG.LocalCores.distinct_components_commute hK hA with hKA | hKA
      · rw [hKA]; exact le_sup_left
      · rcases CFSG.LocalCores.distinct_components_commute hK hB with hKB | hKB
        · rw [hKB]; exact le_sup_right
        · have hAK : A ≤ Subgroup.centralizer (K : Set X) :=
            Subgroup.le_centralizer_iff.1
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKA)
          have hBK : B ≤ Subgroup.centralizer (K : Set X) :=
            Subgroup.le_centralizer_iff.1
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKB)
          have hKc : K ≤ Subgroup.centralizer ((A ⊔ B : Subgroup X) : Set X) := by
            rw [Subgroup.le_centralizer_iff]
            exact sup_le hAK hBK
          have hKbot : K = ⊥ := le_bot_iff.mp (hC ▸ hKc)
          rw [hKbot]; exact bot_le
    · exact sup_le (le_sSup hA) (le_sSup hB)
  have hfit : CFSG.fittingSubgroup X = ⊥ := by
    have h := CFSG.LocalCores.fitting_layer_commute (G := X)
    rw [hlayer] at h
    exact le_bot_iff.mp (hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  rw [CFSG.generalizedFitting, hfit, hlayer, bot_sup_eq]

theorem isComponent_of_prodSplit {X : Type} [Group X] {N A B : Subgroup X} [N.Normal]
    (h : Close.ProdSplit N A B) : CFSG.IsComponent A := by
  have hns : Close.NonabSimple A := h.isA.nonabSimple
  haveI : IsSimpleGroup ↥A := hns.1
  obtain ⟨a, ha, b, hb, hab⟩ := hns.2
  have hq : CFSG.IsQuasisimple ↥A :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥A)
      ⟨⟨a, ha⟩, ⟨b, hb⟩, by simpa using hab⟩).1
  have hnorm : (A.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff h.le_A).2 fun a n ha hn => h.conj_A n hn a ha
  exact ⟨hq, Subgroup.IsSubnormal.step A N h.le_A
    (Subgroup.Normal.isSubnormal (inferInstance : N.Normal)) hnorm⟩

theorem nonempty_fStar_equiv_prod_of_normal {X : Type} [Group X] [Finite X] (N : Subgroup X)
    [N.Normal] (e : ↥N ≃* (A6 × A6)) (hC : centralizer (N : Set X) = ⊥) :
    Nonempty (↥(fStar X) ≃* (A6 × A6)) := by
  obtain ⟨A, B, hAB⟩ := Close.exists_prodSplit e
  have hA : CFSG.IsComponent A := isComponent_of_prodSplit hAB
  have hB : CFSG.IsComponent B := isComponent_of_prodSplit hAB.swap
  have hF : CFSG.generalizedFitting X = N := by
    rw [generalizedFitting_eq_sup_of_isComponent hA hB (by rw [hAB.sup_eq]; exact hC),
      hAB.sup_eq]
  exact ⟨(MulEquiv.subgroupCongr
    ((CFSG.generalizedFitting_eq_componentClassification X).symm.trans hF)).trans e⟩

theorem nonempty_fStar_equiv_U43_of_mulEquiv_U43Ext
    {X : Type} [Group X]
    [Finite X] (e : X ≃* ↥Fin76b.U43Ext) : Nonempty (↥(fStar X) ≃* U43) := by
  let P' : Subgroup ↥Fin76b.U43Ext :=
    CFSG.EvenSporadicStandard.M24Std.CU43.P.subgroupOf Fin76b.U43Ext
  have hP'norm : P'.Normal := by
    apply Subgroup.normal_of_index_eq_two
    exact Fin76b.U16.index_P_U43Ext
  have eP' : ↥P' ≃* U43 :=
    (Subgroup.subgroupOfEquivOfLe Fin76b.U16.P_le_U43Ext).trans
      CFSG.EvenSporadicStandard.M24Std.CU43.psiEquiv.symm
  have hP'q : CFSG.IsQuasisimple ↥P' := by
    have hns := Close.u43_nonabSimple eP'
    haveI : IsSimpleGroup ↥P' := hns.1
    obtain ⟨a, ha, b, hb, hab⟩ := hns.2
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥P')
      ⟨⟨a, ha⟩, ⟨b, hb⟩, by simpa using hab⟩).1
  have hP'comp : CFSG.IsComponent P' :=
    ⟨hP'q, Subgroup.Normal.isSubnormal hP'norm⟩
  have hP'cent : Subgroup.centralizer (P' : Set ↥Fin76b.U43Ext) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxR : (x : Equiv.Perm (Fin 820)) ∈ CFSG.EvenSporadicStandard.M24Std.CU43.R :=
      Fin76b.U16.U43ExtStar_le_R (Fin76b.U16.U43Ext_le_U43ExtStar x.2)
    have hcomm : ∀ p ∈ CFSG.EvenSporadicStandard.M24Std.CU43.P,
        (x : Equiv.Perm (Fin 820)) * p = p * (x : Equiv.Perm (Fin 820)) := by
      intro p hp
      have hmem : (⟨p, Fin76b.U16.P_le_U43Ext hp⟩ : ↥Fin76b.U43Ext) ∈ P' := by
        rw [Subgroup.mem_subgroupOf]; exact hp
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.1 hx ⟨p, Fin76b.U16.P_le_U43Ext hp⟩ hmem).symm
    have hx1 : x = 1 :=
      Subtype.ext (CFSG.EvenSporadicStandard.M24Std.CU43.inj_of_comm hxR hcomm)
    rw [hx1, mem_bot]
  have hF' : CFSG.generalizedFitting ↥Fin76b.U43Ext = P' :=
    generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot P' hP'comp hP'cent
  have hmap : (CFSG.generalizedFitting X).map e.toMonoidHom =
      CFSG.generalizedFitting ↥Fin76b.U43Ext :=
    CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  have eGen : ↥(CFSG.generalizedFitting X) ≃*
      ↥(CFSG.generalizedFitting ↥Fin76b.U43Ext) :=
    ((CFSG.generalizedFitting X).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have eFull : ↥(CFSG.generalizedFitting X) ≃* U43 :=
    (eGen.trans (MulEquiv.subgroupCongr hF')).trans eP'
  exact ⟨(MulEquiv.subgroupCongr
    (CFSG.generalizedFitting_eq_componentClassification X).symm).trans eFull⟩

end CFSG.EvenSporadicStandard.RuStd.S2
