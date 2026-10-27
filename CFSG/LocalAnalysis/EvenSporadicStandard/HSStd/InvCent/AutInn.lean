module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
public import Mathlib.GroupTheory.SpecificGroups.Alternating

import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup
open scoped commutatorElement

theorem mulAut_mul_conj_mul_inv {A : Type*} [Group A] (σ : MulAut A) (a : A) :
    σ * MulAut.conj a * σ⁻¹ = MulAut.conj (σ a) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem mulAut_conj_injective {A : Type*} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : A →* MulAut A) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro c hc
  rw [MonoidHom.mem_ker] at hc
  apply CFSG.EvenSporadicStandard.SolomonRed.eq_one_of_central_of_simple hnab
  intro x
  have h : c * x * c⁻¹ = x := by
    have := congrArg (fun f : MulAut A => f x) hc
    simpa [MulAut.conj_apply] using this
  have h2 : c * x = x * c := by
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h]
  exact h2.symm

theorem eq_one_of_commute_conj {A : Type*} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) {σ : MulAut A}
    (h : ∀ a : A, σ * MulAut.conj a = MulAut.conj a * σ) : σ = 1 := by
  have hinj := mulAut_conj_injective hnab
  ext a
  show σ a = a
  apply hinj
  rw [← mulAut_mul_conj_mul_inv σ a, h a, mul_inv_cancel_right]

theorem rhyp_mulAut {A : Type*} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) :
    RHyp (MulAut A) (MulAut.conj : A →* MulAut A).range := by
  have hinj : Function.Injective (MulAut.conj : A →* MulAut A) :=
    mulAut_conj_injective hnab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(MulAut.conj : A →* MulAut A) a, ⟨a, rfl⟩,
      (MulAut.conj : A →* MulAut A) b, ⟨b, rfl⟩, fun h => hab ?_⟩
    exact hinj (by rw [map_mul, map_mul]; exact h)
  · intro N hN hNne
    haveI : IsSimpleGroup ↥(MulAut.conj : A →* MulAut A).range :=
      (MonoidHom.ofInjective hinj).symm.isSimpleGroup
    haveI : N.Normal := hN
    rcases Subgroup.Normal.eq_bot_or_eq_top
        ((N ⊓ (MulAut.conj : A →* MulAut A).range).subgroupOf
          (MulAut.conj : A →* MulAut A).range) with hbot | htop
    · exfalso
      apply hNne
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      refine eq_one_of_commute_conj hnab fun a => ?_
      have hInn : σ * MulAut.conj a * σ⁻¹ * (MulAut.conj a)⁻¹ ∈
          (MulAut.conj : A →* MulAut A).range := by
        rw [mulAut_mul_conj_mul_inv, ← map_inv, ← map_mul]
        exact ⟨σ a * a⁻¹, rfl⟩
      have hNmem : σ * MulAut.conj a * σ⁻¹ * (MulAut.conj a)⁻¹ ∈ N := by
        have hc := hN.conj_mem σ⁻¹ (inv_mem hσ) (MulAut.conj a)
        simpa [mul_assoc] using mul_mem hσ hc
      have hmem : σ * MulAut.conj a * σ⁻¹ * (MulAut.conj a)⁻¹ ∈
          N ⊓ (MulAut.conj : A →* MulAut A).range := ⟨hNmem, hInn⟩
      have hy : (⟨σ * MulAut.conj a * σ⁻¹ * (MulAut.conj a)⁻¹, hInn⟩ :
          ↥(MulAut.conj : A →* MulAut A).range) ∈
          (N ⊓ (MulAut.conj : A →* MulAut A).range).subgroupOf
            (MulAut.conj : A →* MulAut A).range := Subgroup.mem_subgroupOf.2 hmem
      rw [hbot, Subgroup.mem_bot] at hy
      have hprod : σ * MulAut.conj a * σ⁻¹ * (MulAut.conj a)⁻¹ = 1 := by
        simpa using congrArg Subtype.val hy
      have h1 : σ * MulAut.conj a * σ⁻¹ = MulAut.conj a := mul_inv_eq_one.mp hprod
      calc σ * MulAut.conj a = σ * MulAut.conj a * σ⁻¹ * σ := by group
        _ = MulAut.conj a * σ := by rw [h1]
    · rw [Subgroup.subgroupOf_eq_top] at htop
      exact htop.trans inf_le_left
  · intro σ hσ
    refine eq_one_of_commute_conj hnab fun a => ?_
    exact (hσ (MulAut.conj a)).symm

theorem commutator_mulAut_alt6 :
    commutator (MulAut (alternatingGroup (Fin 6))) =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  haveI hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hcenter : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hnab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
    CFSG.EvenSporadicStandard.SolomonRed.exists_noncommute_of_center_eq_bot hcenter
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro α _ β _
    obtain ⟨c, hc⟩ := (CFSG.EvenSporadicStandard.SolomonRed.OutSq.abel
      CFSG.EvenSporadicStandard.SolomonRed.outSq_alternatingGroup_six) α β
    rw [commutatorElement_def, MonoidHom.mem_range]
    refine ⟨c, ?_⟩
    have h1 : α * β = MulAut.conj c * (β * α) :=
      MulEquiv.ext fun x => by
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        exact hc x
    rw [h1]
    group
  · have hperf : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      isPerfect_of_simple_of_nonab' hnab
    have hperf' : _root_.commutator (alternatingGroup (Fin 6)) = ⊤ :=
      hperf.commutator_eq_top
    have hmap :
        ⁅(MulAut.conj : alternatingGroup (Fin 6) →*
              MulAut (alternatingGroup (Fin 6))).range,
          (MulAut.conj : alternatingGroup (Fin 6) →*
              MulAut (alternatingGroup (Fin 6))).range⁆ =
        (MulAut.conj : alternatingGroup (Fin 6) →*
          MulAut (alternatingGroup (Fin 6))).range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hperf']
    rw [← hmap]
    exact Subgroup.commutator_mono le_top le_top

end CFSG.EvenSporadicStandard.HSStd.InvCent
