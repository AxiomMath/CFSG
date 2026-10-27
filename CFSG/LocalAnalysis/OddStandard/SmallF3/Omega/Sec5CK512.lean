module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CKPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Fact512K_of (hS : Asc82SchurU43) : Asc82Fact512K := by
  intro G _ _ L hL t ht2 hct z hz
  obtain ⟨K₁, K₂, hP, hsup⟩ :=
    sec5c_exists_pair hS hL (sec5c_oddCoreIn_bot hL ht2 hct) hz
  obtain ⟨h₁, h₂⟩ := hP.pocket hsup
  refine ⟨K₁, K₂, h₁, h₂, hP.ne, ?_, hP.iso₁, hP.iso₂, hsup⟩
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hP.comm a ha b hb)

end CFSG.OddStandard.SmallF3.Omega
