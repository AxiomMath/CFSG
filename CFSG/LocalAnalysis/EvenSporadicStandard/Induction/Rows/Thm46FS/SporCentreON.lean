module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreBasic
public import CFSG.Sporadic.ONOddCore.LocalComp

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG CFSG.LocalCores CFSG.ONSchreier CFSG.Sporadic.ONOddCore Subgroup

section ON


theorem nonempty_center_equiv_zmod_four_of_component_M {B : Subgroup onM} (hB : IsComponent B) :
    Nonempty (center B ≃* Multiplicative (ZMod 4)) := by
  have hker : Group.IsSolvable piR.ker := by
    rw [ker_piR]
    have hp : IsPGroup 2 (onQ.subgroupOf onM) :=
      IsPGroup.of_card (n := 2) (by rw [card_onQ_subgroupOf_M]; norm_num)
    have : Group.IsNilpotent (onQ.subgroupOf onM) := hp.isNilpotent
    infer_instance
  have hNab : ∀ x ∈ piR.ker, ∀ y ∈ piR.ker, x * y = y * x := by
    intro x hx y hy
    rw [ker_piR, onQ_subgroupOf_M] at hx hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self qM a b).eq
  have hidx : (XR.comap piR).index = 2 := by
    rw [Subgroup.index_comap_of_surjective XR piR_surjective]
    exact XR_index
  have hLM : onL.subgroupOf onM ≤ XR.comap piR := by
    have h1 : commutator onM ≤ XR.comap piR := by
      rw [commutator_def]
      exact Sporadic.SuzOddCore.commutator_le_of_index_two hidx
    rwa [commutator_M_eq] at h1
  have : Group.IsPerfect (onL.subgroupOf onM) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe onL_le_M).symm.toMonoidHom)
      (subgroupOfEquivOfLe onL_le_M).symm.surjective
  have hLL : ⁅onL.subgroupOf onM, onL.subgroupOf onM⁆ = onL.subgroupOf onM :=
    Subgroup.commutator_eq_self
  have hle : piR.ker ≤ ⁅XR.comap piR, XR.comap piR⁆ := by
    rw [ker_piR]
    calc onQ.subgroupOf onM ≤ onL.subgroupOf onM := fun x hx => ((mem_Q_iff x).1 hx).1
      _ = ⁅onL.subgroupOf onM, onL.subgroupOf onM⁆ := hLL.symm
      _ ≤ ⁅XR.comap piR, XR.comap piR⁆ := Subgroup.commutator_mono hLM hLM
  obtain ⟨c⟩ := nonempty_center_equiv_ker piR piR_surjective hker hNab XR_index XR_simple
    XR_noncomm hle hB
  have e1 : piR.ker ≃* zpowers qM :=
    MulEquiv.subgroupCongr (by rw [ker_piR, onQ_subgroupOf_M])
  have h4 : Nat.card (zpowers qM) = 4 := by
    rw [← onQ_subgroupOf_M]
    exact card_onQ_subgroupOf_M
  obtain ⟨e2⟩ := nonempty_mulEquiv_zmod_four h4
  exact ⟨(c.trans e1).trans e2⟩

end ON

theorem nonempty_center_equiv_zmod_four
    {S : Type*} [Group S] (e : S ≃* Blueprint.NativeSporadic.ON)
    {t : S} (ht : orderOf t = 2) {Q : Subgroup S} (hQC : Q ≤ centralizer ({t} : Set S))
    (hQ : IsComponent (Q.subgroupOf (centralizer ({t} : Set S)))) :
    Nonempty (center Q ≃* Multiplicative (ZMod 4)) := by
  set f : S ≃* Pv := e.trans onEquivPv
  have hft : orderOf (f t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨g⟩ := centralizer_P_equiv_M hft
  set h : centralizer ({t} : Set S) ≃* onM := (centralizerCongr f t).trans g
  obtain ⟨c⟩ := nonempty_center_equiv_zmod_four_of_component_M
    (isComponent_map_mulEquiv h hQ)
  obtain ⟨c'⟩ := nonempty_center_equiv_map h hQC
  exact ⟨c'.trans c⟩

end CFSG.EvenSporadicStandard.Induction.SporCentre
