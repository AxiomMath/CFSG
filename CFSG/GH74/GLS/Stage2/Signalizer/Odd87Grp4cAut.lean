module

public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.GH74.GLS.Stage1.Main

theorem mulAut_quaternion_equiv_perm :
    Nonempty (MulAut (QuaternionGroup 2) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨eQ⟩ := m3Q_equiv_quaternion
  have h24 : Nat.card (MulAut SL2F3) = 24 := card_mulAut_of_equiv_m3 (MulEquiv.refl _)
  have hle : Nat.card (MulAut ↥m3Q) ≤ Nat.card (MulAut SL2F3) := by
    have h2 : Nat.card (MulAut ↥m3Q) = Nat.card (QuaternionGroup 2 ≃* QuaternionGroup 2) :=
      (Nat.card_congr (MulAut.congr eQ).toEquiv).symm
    rw [h2, h24]
    exact CFSG.ClassicalInvolution.q8_natCard_mulEquiv_le
  have hbij : Function.Bijective resQ := resQ_injective.bijective_of_nat_card_le hle
  exact ⟨(((MulAut.congr eQ).trans (MulEquiv.ofBijective resQ hbij).symm).trans
    mulAutM3Equiv.symm).trans CFSG.GorensteinWalter.pgl2_three_equiv_perm⟩

theorem mulAut_equiv_perm_of_quaternion {V : Type*} [Group V] (e : V ≃* QuaternionGroup 2) :
    Nonempty (MulAut V ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨θ⟩ := mulAut_quaternion_equiv_perm
  exact ⟨(MulAut.congr e).trans θ⟩

theorem natCard_mulAut_of_quaternion {V : Type*} [Group V] (e : V ≃* QuaternionGroup 2) :
    Nat.card (MulAut V) = 24 := by
  obtain ⟨θ⟩ := mulAut_equiv_perm_of_quaternion e
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card, Nat.factorial]

theorem conj_ker_eq_center {M : Type*} [Group M] :
    (MulAut.conj : M →* MulAut M).ker = Subgroup.center M := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff, MulEquiv.ext_iff]
  constructor
  · intro h g
    have := h g
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = (x * g * x⁻¹) * x := by rw [this]
      _ = x * g := by group
  · intro h g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc x * g * x⁻¹ = (g * x) * x⁻¹ := by rw [h g]
      _ = g := by group

theorem natCard_range_conj_mul_natCard_center (M : Type*) [Group M] [Finite M] :
    Nat.card (MulAut.conj : M →* MulAut M).range * Nat.card (Subgroup.center M) = Nat.card M := by
  have h := Subgroup.index_mul_card (MulAut.conj : M →* MulAut M).ker
  rw [Subgroup.index_ker, conj_ker_eq_center] at h
  exact h

theorem inn_normal (M : Type*) [Group M] : ((MulAut.conj : M →* MulAut M).range).Normal := by
  refine ⟨fun n hn φ => ?_⟩
  obtain ⟨m, rfl⟩ := hn
  refine ⟨φ m, ?_⟩
  refine MulEquiv.ext fun g => ?_
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
