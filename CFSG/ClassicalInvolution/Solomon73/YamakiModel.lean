module

public import CFSG.ClassicalInvolution.Solomon73.YamakiPres

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open

@[expose] def S0 : Subgroup (StatedSp 3 (ZMod 2)) :=
  Subgroup.closure (yamakiSp '' {i | i.val ≤ 8})

@[expose] def X0 : Subgroup (StatedSp 3 (ZMod 2)) :=
  Subgroup.closure (yamakiSp '' {i | i.val ≤ 8 ∨ i = 10})

@[expose] def N0 : Subgroup (StatedSp 3 (ZMod 2)) :=
  Subgroup.closure (yamakiSp '' {i | i.val ≤ 8 ∨ i = 9 ∨ i = 10})

@[expose] def Hhat : Subgroup (StatedSp 3 (ZMod 2)) :=
  Subgroup.closure (yamakiSp '' {i | i.val ≤ 8 ∨ i = 10 ∨ i = 11})

@[expose] def alpha : StatedSp 3 (ZMod 2) := yamakiSp 5

@[expose] def pi12 : StatedSp 3 (ZMod 2) := yamakiSp 4

@[expose] def pi3 : StatedSp 3 (ZMod 2) := alpha * pi12

theorem yamakiSp_mem_S0 {i : Fin 12} (hi : i.val ≤ 8) : yamakiSp i ∈ S0 :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem yamakiSp_mem_X0 {i : Fin 12} (hi : i.val ≤ 8 ∨ i = 10) : yamakiSp i ∈ X0 :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem yamakiSp_mem_N0 {i : Fin 12} (hi : i.val ≤ 8 ∨ i = 9 ∨ i = 10) : yamakiSp i ∈ N0 :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem yamakiSp_mem_Hhat {i : Fin 12} (hi : i.val ≤ 8 ∨ i = 10 ∨ i = 11) :
    yamakiSp i ∈ Hhat :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem S0_le_X0 : S0 ≤ X0 :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hi, he⟩ => he ▸ yamakiSp_mem_X0 (Or.inl hi)

theorem X0_le_N0 : X0 ≤ N0 :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hi, he⟩ => he ▸ yamakiSp_mem_N0 (hi.imp_right Or.inr)

theorem X0_le_Hhat : X0 ≤ Hhat :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hi, he⟩ => he ▸ yamakiSp_mem_Hhat (hi.imp_right Or.inl)

theorem S0_le_N0 : S0 ≤ N0 := S0_le_X0.trans X0_le_N0

theorem S0_le_Hhat : S0 ≤ Hhat := S0_le_X0.trans X0_le_Hhat

theorem alpha_mem_S0 : alpha ∈ S0 := yamakiSp_mem_S0 (by decide)

theorem pi12_mem_S0 : pi12 ∈ S0 := yamakiSp_mem_S0 (by decide)

theorem pi3_mem_S0 : pi3 ∈ S0 := S0.mul_mem alpha_mem_S0 pi12_mem_S0

end CFSG.ClassicalInvolution.Solomon73.Yamaki
