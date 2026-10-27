module

public import CFSG.ClassicalInvolution.Solomon73.YamakiModel

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

@[expose] def A0 : Subgroup (StatedSp 3 (ZMod 2)) :=
  Subgroup.closure (yamakiSp '' {i | 3 ≤ i.val ∧ i.val ≤ 8})

@[expose] def V0 : Subgroup (StatedSp 3 (ZMod 2)) :=
  Subgroup.closure (yamakiSp '' {i | i.val ≤ 1 ∨ (3 ≤ i.val ∧ i.val ≤ 5)})

@[expose] def orbN0 (x : StatedSp 3 (ZMod 2)) : Set (StatedSp 3 (ZMod 2)) :=
  {y | ∃ n ∈ N0, n * x * n⁻¹ = y}

@[expose] def rho28 : StatedSp 3 (ZMod 2) := yamakiSp 3 * yamakiSp 7

theorem yamakiSp_mem_A0 {i : Fin 12} (h₁ : 3 ≤ i.val) (h₂ : i.val ≤ 8) : yamakiSp i ∈ A0 :=
  Subgroup.subset_closure ⟨i, ⟨h₁, h₂⟩, rfl⟩

theorem yamakiSp_mem_V0 {i : Fin 12} (hi : i.val ≤ 1 ∨ (3 ≤ i.val ∧ i.val ≤ 5)) :
    yamakiSp i ∈ V0 :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem A0_le_S0 : A0 ≤ S0 :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hi, he⟩ => he ▸ yamakiSp_mem_S0 hi.2

theorem A0_le_N0 : A0 ≤ N0 := A0_le_S0.trans S0_le_N0

theorem A0_le_Hhat : A0 ≤ Hhat := A0_le_S0.trans S0_le_Hhat

theorem alpha_mem_A0 : alpha ∈ A0 := yamakiSp_mem_A0 (by decide) (by decide)

theorem pi12_mem_A0 : pi12 ∈ A0 := yamakiSp_mem_A0 (by decide) (by decide)

theorem pi3_mem_A0 : pi3 ∈ A0 := A0.mul_mem alpha_mem_A0 pi12_mem_A0

theorem rho28_mem_A0 : rho28 ∈ A0 :=
  A0.mul_mem (yamakiSp_mem_A0 (by decide) (by decide)) (yamakiSp_mem_A0 (by decide) (by decide))

theorem pi12_mem_V0 : pi12 ∈ V0 := yamakiSp_mem_V0 (by decide)

end CFSG.ClassicalInvolution.Sp62Rec
