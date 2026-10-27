module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimSylow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def AllInner (Y : Type) [Group Y] : Prop :=
  ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g

section Generic

variable {Y : Type} [Group Y]

theorem eq_one_of_conj_eq_one (hZ : center Y = ⊥) {a : Y} (h : MulAut.conj a = 1) : a = 1 := by
  have ha : a ∈ center Y := mem_center_iff.2 fun y => by
    have := DFunLike.congr_fun h y
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rwa [hZ, mem_bot] at ha

theorem mul_self_eq_one_of_conj_mul_self (hZ : center Y = ⊥) {a : Y}
    (h : MulAut.conj a * MulAut.conj a = 1) : a * a = 1 := by
  rw [← map_mul] at h
  exact eq_one_of_conj_eq_one hZ h

theorem mul_comm_of_conj_comm (hZ : center Y = ⊥) {a b : Y}
    (h : MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a) : a * b = b * a := by
  have h1 : MulAut.conj (a * b * (b * a)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h, mul_inv_cancel]
  have := eq_one_of_conj_eq_one hZ h1
  rwa [mul_inv_eq_one] at this

theorem autCenterCond_of_inner (hinn : AllInner Y) (hZ : center Y = ⊥)
    (hcen : CenterInvolutions Y) : AutCenterCond Y := by
  intro ν σ hν hσ hνσ hfix
  obtain ⟨a, rfl⟩ := hinn ν
  obtain ⟨b, rfl⟩ := hinn σ
  have haa : a * a = 1 := mul_self_eq_one_of_conj_mul_self hZ hν
  have hbb : b * b = 1 := mul_self_eq_one_of_conj_mul_self hZ hσ
  have hab : a * b = b * a := mul_comm_of_conj_comm hZ hνσ
  have hfix' : ∀ y : Y, y * a = a * y → b * y = y * b := by
    intro y hy
    have h1 : MulAut.conj a y = y := by
      rw [MulAut.conj_apply, ← hy]
      group
    have h2 := hfix y h1
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  by_cases ha : a = 1
  · left
    apply DFunLike.ext
    intro y
    rw [MulAut.one_apply]
    have h2 := hfix' y (by rw [ha, mul_one, one_mul])
    rw [MulAut.conj_apply, h2]
    group
  · have ha2 : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha
    rcases hcen a b ha2 hbb hab.symm hfix' with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]

theorem orderOf_eq_two_of_mul_self_eq_one {a : Y} (haa : a * a = 1) (ha : a ≠ 1) :
    orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha

theorem umovesCond_of_inner (hinn : AllInner Y) (hZ : center Y = ⊥)
    (hcomm : InvolutionsCommute Y) : UMovesCond Y := by
  intro u hu α hα
  obtain ⟨a, rfl⟩ := hinn α
  have haa : a * a = 1 := mul_self_eq_one_of_conj_mul_self hZ hα
  by_cases ha : a = 1
  · exact ⟨1, by rw [ha, map_one, MulAut.one_apply]⟩
  · obtain ⟨h, hh⟩ := hcomm u a hu (orderOf_eq_two_of_mul_self_eq_one haa ha)
    refine ⟨h, ?_⟩
    rw [MulAut.conj_apply, ← hh]
    group

end Generic

end CFSG.EvenSporadicStandard.Solomon78
